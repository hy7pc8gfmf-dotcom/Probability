# 简化的Makefile用于本地构建

.PHONY: all check doc clean setup

# 主文件
MAIN_FILE = FormalCert_Probability_System.v

# 默认目标
all: check

# 设置开发环境
setup:
	@echo "设置开发环境..."
	@chmod +x scripts/setup-dev.sh
	@./scripts/setup-dev.sh

# 检查文件
check:
	@echo "检查Coq文件..."
	@if [ -f "$(MAIN_FILE)" ]; then \
		echo "编译 $(MAIN_FILE)..."; \
		coqc -q $(MAIN_FILE) && echo "✓ 编译成功"; \
	else \
		echo "找不到 $(MAIN_FILE)"; \
		echo "尝试查找.v文件..."; \
		FIRST_V=$$(find . -name "*.v" -type f | head -1); \
		if [ -n "$$FIRST_V" ]; then \
			echo "编译 $$FIRST_V..."; \
			coqc -q $$FIRST_V && echo "✓ 编译成功"; \
		else \
			echo "错误: 找不到任何.v文件"; \
			exit 1; \
		fi; \
	fi

# 生成文档
doc:
	@echo "生成文档..."
	@mkdir -p docs/html
	@if [ -f "$(MAIN_FILE)" ]; then \
		coqdoc --html -d docs/html $(MAIN_FILE); \
		echo "文档生成到 docs/html/"; \
	else \
		echo "找不到 $(MAIN_FILE)，无法生成文档"; \
	fi

# 清理
clean:
	@echo "清理构建文件..."
	@rm -rf _build *.vo *.glob *.aux docs/html/* docs/latex/*
	@echo "清理完成"

# 帮助
help:
	@echo "可用命令:"
	@echo "  make setup    - 设置开发环境"
	@echo "  make check    - 编译检查Coq文件"
	@echo "  make doc      - 生成文档"
	@echo "  make clean    - 清理构建文件"
	@echo "  make help     - 显示此帮助"
