# 使用Coq官方镜像
FROM coqorg/coq:8.20

# 设置工作目录
WORKDIR /workspace

# 安装一些必要的工具（如果需要）
RUN apt-get update && \
    apt-get install -y \
        curl \
        git \
        make \
        && rm -rf /var/lib/apt/lists/*

# 设置环境变量
ENV OPAMYES=true
ENV OPAMROOT=/usr/local/opam