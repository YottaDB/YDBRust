FROM yottadb/yottadb-base

# Install packaged dependencies
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
  build-essential git curl cmake gcc g++ pkg-config libmagic-dev \
  libssl-dev zlib1g-dev ca-certificates cargo clang \
  libsdl2-dev libsdl2-gfx-dev libsdl2-ttf-dev

VOLUME /opt/ydbrust
WORKDIR /opt/ydbrust
