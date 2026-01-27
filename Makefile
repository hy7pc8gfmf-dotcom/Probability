# Makefile for FormalCert Probability System
# 用法: 
#   make all      # 编译所有文件
#   make check    # 语法检查
#   make doc      # 生成文档
#   make clean    # 清理编译文件

COQC = coqc
COQDOC = coqdoc
COQFLAGS = -Q . FormalCert

# 主文件列表（按依赖顺序）
MAIN_FILES = \
    UnifiedMathFoundationImpl.v \
    UnifiedMeasureTheory.v

# 生成的目标文件
VO_FILES = $(MAIN_FILES:.v=.vo)
GLOBS = $(MAIN_FILES:.v=.glob)

# 默认目标
all: $(VO_FILES)

# 编译规则
%.vo: %.v
	$(COQC) $(COQFLAGS) $<

# 检查所有文件
check: all
	@echo "所有文件编译成功!"

# 生成文档
doc:
	mkdir -p html
	$(COQDOC) --html -d html $(MAIN_FILES)
	@echo "文档已生成到html/目录"

# 清理
clean:
	rm -f *.vo *.glob *.aux
	rm -rf html
	rm -rf _build

# 性能测试
benchmark:
	@echo "编译时间基准测试..."
	time $(MAKE) clean all

# 检查公理
axiom-check:
	@grep -n "Axiom" *.v | tee axioms.txt
	@echo "公理总数: $$(grep -c "Axiom" *.v)"

# 统计信息
stats:
	@echo "代码统计:"
	@echo "文件数: $$(find . -name "*.v" | wc -l)"
	@echo "总行数: $$(find . -name "*.v" -exec wc -l {} + | tail -1 | awk '{print $$1}')"
	@echo "定理数: $$(grep -c "Theorem\|Lemma\|Corollary" *.v)"

.PHONY: all check doc clean benchmark axiom-check stats
