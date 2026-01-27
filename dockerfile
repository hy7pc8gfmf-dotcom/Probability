# 使用官方Coq镜像作为基础
FROM coqorg/coq:8.16

# 设置元数据
LABEL maintainer="FormalCert Team <team@formalcert.org>"
LABEL version="4.0.0"
LABEL description="FormalCert Probability System Development Environment"

# 设置环境变量
ENV COQ_VERSION=8.16
ENV OPAMYES=true
ENV DEBIAN_FRONTEND=noninteractive

# 安装系统依赖
RUN apt-get update && apt-get install -y \
    build-essential \
    curl \
    git \
    wget \
    vim \
    nano \
    python3 \
    python3-pip \
    texlive-latex-base \
    texlive-latex-extra \
    && rm -rf /var/lib/apt/lists/*

# 创建并设置工作目录
WORKDIR /workspace

# 设置Opam环境
RUN opam update && opam upgrade -y

# 安装Coquelicot和其他依赖
RUN opam install -y coq-coquelicot && \
    opam install -y coq-mathcomp-ssreflect coq-mathcomp-algebra coq-mathcomp-field

# 安装coqdoc用于文档生成
RUN opam install -y coq-coqdoc

# 验证安装
RUN coqc --version && \
    opam list | grep -E "coq|mathcomp"

# 设置默认命令
CMD ["coqide", "--version"]