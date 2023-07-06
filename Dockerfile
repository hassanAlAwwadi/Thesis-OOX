FROM rust:1.67

WORKDIR /
RUN apt-get update -y \
    && apt-get install build-essential -y \
    && apt-get -y install cmake \
    && apt-get install libclang-dev -y \
    && git clone https://github.com/DanielvanVliet/OOX.git OOX
WORKDIR /OOX
RUN cargo build --release 