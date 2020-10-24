/*
 * Souffle - A Datalog Compiler
 * Copyright (c) 2013, 2015, Oracle and/or its affiliates. All rights reserved
 * Licensed under the Universal Permissive License v 1.0 as shown at:
 * - https://opensource.org/licenses/UPL
 * - <souffle root>/licenses/SOUFFLE-UPL.txt
 */

/************************************************************************
 *
 * @file ClauseTranslator.h
 *
 * Translator for clauses from AST to RAM
 *
 ***********************************************************************/

#include "ast2ram/ClauseTranslator.h"
#include "Global.h"
#include "ast/Aggregator.h"
#include "ast/Clause.h"
#include "ast/IntrinsicFunctor.h"
#include "ast/NumericConstant.h"
#include "ast/RecordInit.h"
#include "ast/UnnamedVariable.h"
#include "ast/analysis/Functor.h"
#include "ast/transform/ReorderLiterals.h"
#include "ast/utility/Utils.h"
#include "ast/utility/Visitor.h"
#include "ast2ram/AstToRamTranslator.h"
#include "ast2ram/Location.h"
#include "ast2ram/ValueIndex.h"
#include "ram/Aggregate.h"
#include "ram/Break.h"
#include "ram/Conjunction.h"
#include "ram/Constraint.h"
#include "ram/EmptinessCheck.h"
#include "ram/Filter.h"
#include "ram/Negation.h"
#include "ram/NestedIntrinsicOperator.h"
#include "ram/Project.h"
#include "ram/Query.h"
#include "ram/Relation.h"
#include "ram/Scan.h"
#include "ram/TupleElement.h"
#include "ram/UnpackRecord.h"
#include "ram/utility/Utils.h"
#include "souffle/utility/StringUtil.h"
#include <map>
#include <vector>

namespace souffle::ast2ram {

/** generate RAM code for a clause */
Own<ram::Statement> ClauseTranslator::translateClause(
        const ast::Clause& clause, const ast::Clause& originalClause, const int version) {
    if (auto reorderedClause = getReorderedClause(clause, version)) {
        // translate reordered clause
        return translateClause(*reorderedClause, originalClause, version);
    }

    // get extract some details
    const ast::Atom* head = clause.getHead();

    // handle facts
    if (isFact(clause)) {
        // translate arguments
        VecOwn<ram::Expression> values;
        for (auto& arg : head->getArguments()) {
            values.push_back(translator.translateValue(arg, ValueIndex()));
        }

        // create a fact statement
        return mk<ram::Query>(mk<ram::Project>(translator.translateRelation(head), std::move(values)));
    }

    // the rest should be rules
    assert(isRule(clause));

    createValueIndex(clause);

    // -- create RAM statement --

    Own<ram::Operation> op = createOperation(clause);

    /* add equivalence constraints imposed by variable binding */
    for (const auto& cur : valueIndex->getVariableReferences()) {
        // the first appearance
        const Location& first = *cur.second.begin();
        // all other appearances
        for (const Location& loc : cur.second) {
            if (first != loc && !valueIndex->isGenerator(loc.identifier)) {
                // FIXME: equiv' for float types (`FEQ`)
                op = mk<ram::Filter>(
                        mk<ram::Constraint>(BinaryConstraintOp::EQ, translator.makeRamTupleElement(first),
                                translator.makeRamTupleElement(loc)),
                        std::move(op));
            }
        }
    }

    /* add conditions caused by atoms, negations, and binary relations */
    for (const auto& lit : clause.getBodyLiterals()) {
        if (auto condition = translator.translateConstraint(lit, *valueIndex)) {
            op = mk<ram::Filter>(std::move(condition), std::move(op));
        }
    }

    // add aggregator conditions
    size_t curLevel = op_nesting.size() - 1;
    for (auto it = op_nesting.rbegin(); it != op_nesting.rend(); ++it, --curLevel) {
        const ast::Node* cur = *it;

        if (const auto* atom = dynamic_cast<const ast::Atom*>(cur)) {
            // add constraints
            size_t pos = 0;
            for (auto arg : atom->getArguments()) {
                if (auto* agg = dynamic_cast<ast::Aggregator*>(arg)) {
                    auto loc = valueIndex->getGeneratorLoc(*agg);
                    // FIXME: equiv' for float types (`FEQ`)
                    op = mk<ram::Filter>(
                            mk<ram::Constraint>(BinaryConstraintOp::EQ, mk<ram::TupleElement>(curLevel, pos),
                                    translator.makeRamTupleElement(loc)),
                            std::move(op));
                }
                ++pos;
            }
        }
    }

    // add generator levels
    --level;
    for (auto* cur : reverse(generators)) {
        if (auto agg = dynamic_cast<const ast::Aggregator*>(cur)) {
            // condition for aggregate and helper function to add terms
            Own<ram::Condition> aggCond;
            auto addAggCondition = [&](Own<ram::Condition> arg) {
                aggCond = aggCond ? mk<ram::Conjunction>(std::move(aggCond), std::move(arg)) : std::move(arg);
            };

            // translate constraints of sub-clause
            for (auto&& lit : agg->getBodyLiterals()) {
                if (auto newCondition = translator.translateConstraint(lit, *valueIndex)) {
                    addAggCondition(std::move(newCondition));
                }
            }

            // get the first predicate of the sub-clause
            // NB: at most one atom is permitted in a sub-clause
            const ast::Atom* atom = nullptr;
            for (auto&& lit : agg->getBodyLiterals()) {
                if (atom == nullptr) {
                    atom = dynamic_cast<const ast::Atom*>(lit);
                } else {
                    assert(!isA<ast::Atom>(lit) && "Unsupported complex aggregation body encountered!");
                }
            }

            // translate arguments's of atom (if exists) to conditions
            if (atom != nullptr) {
                size_t pos = 0;
                auto addAggEqCondition = [&](Own<ram::Expression> value) {
                    if (isUndefValue(value.get())) return;

                    // FIXME: equiv' for float types (`FEQ`)
                    addAggCondition(mk<ram::Constraint>(
                            BinaryConstraintOp::EQ, mk<ram::TupleElement>(level, pos), std::move(value)));
                };
                for (auto* arg : atom->getArguments()) {
                    // variable bindings are issued differently since we don't want self
                    // referential variable bindings
                    if (auto* var = dynamic_cast<const ast::Variable*>(arg)) {
                        for (auto&& loc : valueIndex->getVariableReferences().find(var->getName())->second) {
                            if (level != loc.identifier || (int)pos != loc.element) {
                                addAggEqCondition(translator.makeRamTupleElement(loc));
                                break;
                            }
                        }
                    } else if (auto value = translator.translateValue(arg, *valueIndex)) {
                        addAggEqCondition(std::move(value));
                    }
                    ++pos;
                }
            }

            // translate aggregate expression
            auto expr = translator.translateValue(agg->getTargetExpression(), *valueIndex);

            // add Ram-Aggregation layer
            op = mk<ram::Aggregate>(std::move(op), agg->getOperator(), translator.translateRelation(atom),
                    expr ? std::move(expr) : mk<ram::UndefValue>(),
                    aggCond ? std::move(aggCond) : mk<ram::True>(), level);
        } else if (const auto* func = dynamic_cast<const ast::IntrinsicFunctor*>(cur)) {
            VecOwn<ram::Expression> args;
            for (auto&& x : func->getArguments()) {
                args.push_back(translator.translateValue(x, *valueIndex));
            }

            auto func_op = [&]() -> ram::NestedIntrinsicOp {
                switch (func->getFunctionOp().value()) {
                    case FunctorOp::RANGE: return ram::NestedIntrinsicOp::RANGE;
                    case FunctorOp::URANGE: return ram::NestedIntrinsicOp::URANGE;
                    case FunctorOp::FRANGE: return ram::NestedIntrinsicOp::FRANGE;

                    default: fatal("missing case handler or bad code-gen");
                }
            };

            op = mk<ram::NestedIntrinsicOperator>(func_op(), std::move(args), std::move(op), level);
        }

        --level;
    }

    // build operation bottom-up
    while (!op_nesting.empty()) {
        // get next operator
        const ast::Node* cur = op_nesting.back();
        op_nesting.pop_back();

        // get current nesting level
        auto level = op_nesting.size();

        if (const auto* atom = dynamic_cast<const ast::Atom*>(cur)) {
            // add constraints
            // TODO: do we wish to enable constraints by header functor? record inits do so...
            op = filterByConstraints(level, atom->getArguments(), std::move(op), false);

            // check whether all arguments are unnamed variables
            bool isAllArgsUnnamed = true;
            for (auto* argument : atom->getArguments()) {
                if (!isA<ast::UnnamedVariable>(argument)) {
                    isAllArgsUnnamed = false;
                }
            }

            // add check for emptiness for an atom
            op = mk<ram::Filter>(
                    mk<ram::Negation>(mk<ram::EmptinessCheck>(translator.translateRelation(atom))),
                    std::move(op));

            // add a scan level
            if (atom->getArity() != 0 && !isAllArgsUnnamed) {
                if (head->getArity() == 0) {
                    op = mk<ram::Break>(
                            mk<ram::Negation>(mk<ram::EmptinessCheck>(translator.translateRelation(head))),
                            std::move(op));
                }
                if (Global::config().has("profile")) {
                    std::stringstream ss;
                    ss << head->getQualifiedName();
                    ss.str("");
                    ss << "@frequency-atom" << ';';
                    ss << originalClause.getHead()->getQualifiedName() << ';';
                    ss << version << ';';
                    ss << stringify(toString(clause)) << ';';
                    ss << stringify(toString(*atom)) << ';';
                    ss << stringify(toString(originalClause)) << ';';
                    ss << level << ';';
                    op = mk<ram::Scan>(translator.translateRelation(atom), level, std::move(op), ss.str());
                } else {
                    op = mk<ram::Scan>(translator.translateRelation(atom), level, std::move(op));
                }
            }

            // TODO: support constants in nested records!
        } else if (const auto* rec = dynamic_cast<const ast::RecordInit*>(cur)) {
            // add constant constraints
            op = filterByConstraints(level, rec->getArguments(), std::move(op));

            // add an unpack level
            const Location& loc = valueIndex->getDefinitionPoint(*rec);
            op = mk<ram::UnpackRecord>(
                    std::move(op), level, translator.makeRamTupleElement(loc), rec->getArguments().size());
        } else {
            fatal("Unsupported AST node for creation of scan-level!");
        }
    }

    /* generate the final RAM Insert statement */
    Own<ram::Condition> cond = createCondition(originalClause);
    if (cond != nullptr) {
        return mk<ram::Query>(mk<ram::Filter>(std::move(cond), std::move(op)));
    } else {
        return mk<ram::Query>(std::move(op));
    }
}

Own<ram::Operation> ClauseTranslator::createOperation(const ast::Clause& clause) {
    const auto head = clause.getHead();

    VecOwn<ram::Expression> values;
    for (ast::Argument* arg : head->getArguments()) {
        values.push_back(translator.translateValue(arg, *valueIndex));
    }

    Own<ram::Operation> project = mk<ram::Project>(translator.translateRelation(head), std::move(values));

    if (head->getArity() == 0) {
        project = mk<ram::Filter>(
                mk<ram::EmptinessCheck>(translator.translateRelation(head)), std::move(project));
    }

    // build up insertion call
    return project;  // start with innermost
}

Own<ram::Condition> ClauseTranslator::createCondition(const ast::Clause& originalClause) {
    const auto head = originalClause.getHead();

    // add stopping criteria for nullary relations
    // (if it contains already the null tuple, don't re-compute)
    if (head->getArity() == 0) {
        return mk<ram::EmptinessCheck>(translator.translateRelation(head));
    }
    return nullptr;
}

Own<ram::Operation> ClauseTranslator::filterByConstraints(size_t const level,
        const std::vector<ast::Argument*>& args, Own<ram::Operation> op, bool constrainByFunctors) {
    size_t pos = 0;

    auto mkFilter = [&](bool isFloatArg, Own<ram::Expression> rhs) {
        return mk<ram::Filter>(
                mk<ram::Constraint>(isFloatArg ? BinaryConstraintOp::FEQ : BinaryConstraintOp::EQ,
                        mk<ram::TupleElement>(level, pos), std::move(rhs)),
                std::move(op));
    };

    for (auto* a : args) {
        if (auto* c = dynamic_cast<const ast::Constant*>(a)) {
            auto* const c_num = dynamic_cast<const ast::NumericConstant*>(c);
            assert((!c_num || c_num->getType()) && "numeric constant wasn't bound to a type");
            op = mkFilter(c_num && *c_num->getType() == ast::NumericConstant::Type::Float,
                    translator.translateConstant(*c));
        } else if (auto* func = dynamic_cast<const ast::Functor*>(a)) {
            if (constrainByFunctors) {
                TypeAttribute returnType = translator.getFunctorAnalysis()->getReturnType(func);
                op = mkFilter(
                        returnType == TypeAttribute::Float, translator.translateValue(func, *valueIndex));
            }
        }

        ++pos;
    }

    return op;
}

Own<ast::Clause> ClauseTranslator::getReorderedClause(const ast::Clause& clause, const int version) const {
    const auto plan = clause.getExecutionPlan();

    // check whether there is an imposed order constraint
    if (plan == nullptr) {
        // no plan, so reorder it according to the internal heuristic
        if (auto* reorderedClause = ast::transform::ReorderLiteralsTransformer::reorderClauseWithSips(
                    *translator.getSipsMetric(), &clause)) {
            return Own<ast::Clause>(reorderedClause);
        }
        return nullptr;
    }
    auto orders = plan->getOrders();
    if (orders.find(version) == orders.end()) {
        return nullptr;
    }

    // get the imposed order
    const auto& order = orders[version];

    // create a copy and fix order
    Own<ast::Clause> reorderedClause(clause.clone());

    // Change order to start at zero
    std::vector<unsigned int> newOrder(order->getOrder().size());
    std::transform(order->getOrder().begin(), order->getOrder().end(), newOrder.begin(),
            [](unsigned int i) -> unsigned int { return i - 1; });

    // re-order atoms
    reorderedClause.reset(reorderAtoms(reorderedClause.get(), newOrder));

    // clear other order and fix plan
    reorderedClause->clearExecutionPlan();

    return reorderedClause;
}

void ClauseTranslator::indexValues(const ast::Node* curNode, const std::vector<ast::Argument*>& curNodeArgs,
        std::map<const ast::Node*, int>& nodeLevel, const ram::Relation* relation) {
    for (size_t pos = 0; pos < curNodeArgs.size(); ++pos) {
        // get argument
        auto& arg = curNodeArgs[pos];

        // check for variable references
        if (auto var = dynamic_cast<const ast::Variable*>(arg)) {
            if (pos < relation->getArity()) {
                valueIndex->addVarReference(*var, nodeLevel[curNode], pos, relation->getName());
            } else {
                valueIndex->addVarReference(*var, nodeLevel[curNode], pos);
            }
        }

        // check for nested records
        if (auto rec = dynamic_cast<const ast::RecordInit*>(arg)) {
            // introduce new nesting level for unpack
            op_nesting.push_back(rec);
            nodeLevel[rec] = level++;

            // register location of record
            valueIndex->setRecordDefinition(*rec, nodeLevel[curNode], pos);

            // resolve nested components
            indexValues(rec, rec->getArguments(), nodeLevel, relation);
        }
    }
}

/** index values in rule */
void ClauseTranslator::createValueIndex(const ast::Clause& clause) {
    for (const auto* atom : ast::getBodyLiterals<ast::Atom>(clause)) {
        // map from each list of arguments to its nesting level
        std::map<const ast::Node*, int> nodeLevel;

        // give the atom the current level
        nodeLevel[atom] = level++;
        op_nesting.push_back(atom);

        // index each value in the atom
        indexValues(atom, atom->getArguments(), nodeLevel,
                translator.lookupRelation(translator.translateRelation(atom)));
    }

    // add aggregation functions
    visitDepthFirstPostOrder(clause, [&](const ast::Argument& arg) {
        // returns the write-location for this generator (or none if an equiv arg was already seen)
        auto addGenerator = [&]() -> std::optional<int> {
            // The by-value compare means that we're effectively doing CSE for any
            // generator args during code-gen. This is a weird place to do this.
            if (dynamic_cast<const ast::Aggregator*>(&arg) != nullptr &&
                    any_of(generators, [&](auto* x) { return *x == arg; }))
                return {};
            generators.push_back(&arg);

            int aggLoc = level++;
            valueIndex->setGeneratorLoc(arg, Location({aggLoc, 0}));
            return aggLoc;
        };

        if (auto agg = dynamic_cast<const ast::Aggregator*>(&arg)) {
            if (auto aggLoc = addGenerator()) {
                // bind aggregator variables to locations
                const ast::Atom* atom = nullptr;
                for (auto lit : agg->getBodyLiterals()) {
                    if (atom == nullptr) {
                        atom = dynamic_cast<const ast::Atom*>(lit);
                    } else {
                        break;
                    }
                }
                if (atom != nullptr) {
                    size_t pos = 0;
                    for (auto* arg : atom->getArguments()) {
                        if (const auto* var = dynamic_cast<const ast::Variable*>(arg)) {
                            valueIndex->addVarReference(
                                    *var, *aggLoc, (int)pos, translator.translateRelation(atom));
                        }
                        ++pos;
                    }
                }
            }
        }

        auto* func = as<ast::IntrinsicFunctor>(arg);
        if (func && ast::analysis::FunctorAnalysis::isMultiResult(*func)) {
            addGenerator();
        }
    });

    // add multi-result functor introductions
    visitDepthFirst(clause, [&](const ast::BinaryConstraint& bc) {
        if (bc.getOperator() != BinaryConstraintOp::EQ && bc.getOperator() != BinaryConstraintOp::FEQ) return;
        const auto* lhs = dynamic_cast<const ast::Variable*>(bc.getLHS());
        const auto* rhs = dynamic_cast<const ast::IntrinsicFunctor*>(bc.getRHS());
        if (lhs == nullptr || rhs == nullptr) return;
        if (!ast::analysis::FunctorAnalysis::isMultiResult(*rhs)) return;
        valueIndex->addVarReference(*lhs, valueIndex->getGeneratorLoc(*rhs));
    });
}

}  // namespace souffle::ast2ram
