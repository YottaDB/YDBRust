FROM yottadb/yottadb-base

# Install packaged dependencies
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
  build-essential git curl cmake gcc g++ pkg-config libmagic-dev \
  libssl-dev zlib1g-dev ca-certificates clang \
  libsdl2-dev libsdl2-gfx-dev libsdl2-ttf-dev

# Install the stable toolchain with rustup
RUN curl https://static.rust-lang.org/rustup/dist/x86_64-unknown-linux-gnu/rustup-init >/tmp/rustup-init && \
    chmod +x /tmp/rustup-init && \
    /tmp/rustup-init -y --no-modify-path --default-toolchain stable --profile minimal
ENV PATH=/root/.cargo/bin:$PATH
VOLUME /opt/ydbrust
WORKDIR /opt/ydbrust
