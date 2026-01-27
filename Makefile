# FormalCert Probability System - Makefile
# 简化版本，专注于Docker容器操作

.PHONY: help all build test docs clean docker-build docker-run docker-shell

# 默认目标
help:
	@echo "FormalCert Probability System - 构建工具"
	@echo ""
	@echo "可用命令:"
	@echo "  make docker-build    # 构建Docker开发镜像"
	@echo "  make docker-run      # 运行Docker容器编译项目"
	@echo "  make docker-shell    # 进入Docker容器的交互式shell"
	@echo "  make test            # 运行测试"
	@echo "  make docs            # 生成文档"
	@echo "  make clean           # 清理构建文件"
	@echo "  make all             # 构建和测试所有内容"

# 构建Docker镜像 - 使用固定版本的Coq
docker-build:
	@echo "构建FormalCert Coq开发镜像..."
	@echo "注意：使用预配置的Coq环境，跳过Opam安装..."
	docker build \
		--build-arg COQ_VERSION=8.16 \
		-t formalcert-coq-dev:latest .

# 在Docker中运行编译 - 使用已经安装好的环境
docker-run:
	@echo "在Docker中编译Coq文件..."
	@mkdir -p _build
	docker run --rm \
		-v $(PWD):/workspace \
		-w /workspace \
		formalcert-coq-dev:latest \
		bash -c " \
			echo '=== 检查Coq环境 ===' && \
			coqc --version && \
			echo '=== 编译Coq文件 ===' && \
			if [ -f 'src/FormalCert_Probability_System.v' ]; then \
				cd src && \
				coqc -q FormalCert_Probability_System.v && \
				echo '✓ 编译成功'; \
			elif [ -f '上.txt' ]; then \
				echo '找到上.txt，处理为Coq文件...' && \
				mkdir -p src && \
				cp 上.txt src/FormalCert_Probability_System.v && \
				cd src && \
				coqc -q FormalCert_Probability_System.v && \
				echo '✓ 编译成功'; \
			else \
				echo '未找到Coq文件，请检查工作目录'; \
				ls -la && \
				find . -name '*.v' -o -name '*.txt' | head -10; \
			fi \
		"

# 进入Docker容器的交互式shell
docker-shell:
	@echo "启动Docker交互式shell..."
	docker run -it --rm \
		-v $(PWD):/workspace \
		-w /workspace \
		--entrypoint /bin/bash \
		formalcert-coq-dev:latest

# 生成文档
docs:
	@echo "生成文档..."
	@mkdir -p docs/html docs/latex
	docker run --rm \
		-v $(PWD):/workspace \
		-w /workspace \
		formalcert-coq-dev:latest \
		bash -c " \
			if [ -f 'src/FormalCert_Probability_System.v' ]; then \
				cd src && \
				coqdoc --html -d ../docs/html FormalCert_Probability_System.v && \
				coqdoc --latex -d ../docs/latex FormalCert_Probability_System.v && \
				echo '文档生成完成'; \
			else \
				echo '未找到Coq文件，无法生成文档'; \
			fi \
		"

# 运行测试 - 仅编译验证
test: docker-run
	@echo "测试完成"

# 清理
clean:
	@echo "清理构建文件..."
	@rm -rf _build *.vo *.glob *.aux *.vok *.vos docs/html/* docs/latex/* src/*.vo src/*.glob
	@echo "清理完成"

# 完整构建
all: docker-build docker-run docs
	@echo "完整构建完成"

# 快速验证
quick-check:
	@echo "快速语法检查..."
	@if [ -f "src/FormalCert_Probability_System.v" ]; then \
		docker run --rm \
			-v $(PWD):/workspace \
			-w /workspace \
			formalcert-coq-dev:latest \
			bash -c " \
				cd src && \
				head -100 FormalCert_Probability_System.v > quick_test.v && \
				coqc -q quick_test.v && \
				echo '✓ 快速检查通过'; \
			"; \
	elif [ -f "上.txt" ]; then \
		docker run --rm \
			-v $(PWD):/workspace \
			-w /workspace \
			formalcert-coq-dev:latest \
			bash -c " \
				mkdir -p src && \
				head -100 上.txt > src/quick_test.v && \
				cd src && \
				coqc -q quick_test.v && \
				echo '✓ 快速检查通过'; \
			"; \
	else \
		echo "错误: 未找到Coq源文件或上.txt"; \
	fi

# 本地开发快速启动
dev:
	@echo "启动开发环境..."
	@make docker-build
	@make docker-shell