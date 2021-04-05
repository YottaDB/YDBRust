#################################################################
#                                                               #
# Copyright (c) 2019-2021 YottaDB LLC and/or its subsidiaries.  #
# All rights reserved.                                          #
#                                                               #
#       This source code contains the intellectual property     #
#       of its copyright holder(s), and is made available       #
#       under a license.  If you do not know the terms of       #
#       the license, please stop and do not read further.       #
#                                                               #
#################################################################

FROM yottadb/yottadb-base

# Install packaged dependencies
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
  build-essential git curl cmake gcc g++ pkg-config libmagic-dev \
  libssl-dev zlib1g-dev ca-certificates clang \
  libsdl2-dev libsdl2-gfx-dev libsdl2-ttf-dev
# Install Rust from rustup. sdl2 requires at least 1.48, which isn't currently packaged.
# Using a separate rustup-init.sh file allows passing CLI arguments.
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs > rustup-init.sh
RUN sh rustup-init.sh -y --default-toolchain stable

VOLUME /opt/ydbrust
WORKDIR /opt/ydbrust
