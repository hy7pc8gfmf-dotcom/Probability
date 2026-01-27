# 使用Coq官方镜像
FROM coqorg/coq:8.16

# 设置工作目录
WORKDIR /workspace

# 安装额外的工具（可选）
RUN apt-get update && apt-get install -y \
    curl \
    git \
    make \
    vim \
    && rm -rf /var/lib/apt/lists/*

# 显示Coq版本
RUN echo "Coq version:" && coqc --version

# 设置默认命令
CMD ["/bin/bash"]