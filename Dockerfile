FROM ubuntu:25.10

RUN apt update && \
    apt install -y git build-essential && \
    rm -rf /var/lib/apt/lists/*

WORKDIR /work

RUN <<EOR
    git clone https://github.com/polyml/polyml.git
    cd polyml
    ./configure --prefix=/usr
    make
    make install
EOR

RUN <<EOR
    git clone https://github.com/HOL-Theorem-Prover/HOL.git
    cd HOL
    poly < tools/smart-configure.sml
    bin/build -j4
EOR

ENV PATH="$PATH:/work/HOL/bin/"

COPY . gp2-hol
RUN <<EOR
    cd gp2-hol
    Holmake -j4
EOR
