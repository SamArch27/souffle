ARG SOUFFLE_DOCKER_BASE_IMAGE

FROM ${SOUFFLE_DOCKER_BASE_IMAGE}

ARG CC
ARG CXX

ARG SOUFFLE_CATEGORY
ARG SOUFFLE_CONFS
ARG SOUFFLE_CONFIGURE_OPTIONS
ARG SOUFFLE_MAKE_JOBS

ENV CC="${CC}"
ENV CXX="${CXX}"

ENV SOUFFLE_CATEGORY="${SOUFFLE_CATEGORY}"
ENV SOUFFLE_CONFS="${SOUFFLE_CONFS}"
ENV SOUFFLE_CONFIGURE_OPTIONS="${SOUFFLE_CONFIGURE_OPTIONS}"
ENV SOUFFLE_MAKE_JOBS="${SOUFFLE_MAKE_JOBS}"

COPY . /home/souffle/souffle

WORKDIR /home/souffle/souffle

USER root

RUN echo "btl_base_warn_component_unused = 0" >> /etc/openmpi/openmpi-mca-params.conf

RUN chown -R souffle .

USER souffle

RUN ./bootstrap
RUN ./configure ${SOUFFLE_CONFIGURE_OPTIONS}
RUN make -j${SOUFFLE_MAKE_JOBS}

ENTRYPOINT ["./sh/run_docker.sh", "souffle"]
