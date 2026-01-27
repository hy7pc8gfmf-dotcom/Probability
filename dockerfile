# Dockerfile
FROM coqorg/coq:8.16

# 安装必要的工具
RUN apt-get update && apt-get install -y \
    git \
    make \
    time \
    && rm -rf /var/lib/apt/lists/*

# 设置工作目录
WORKDIR /workspace

# 复制必要的文件（如果需要）
COPY Makefile ./

# 设置环境变量
ENV OPAMYES=true
ENV OPAMROOT=/usr/local/opam

# 设置默认命令
CMD ["bash"]