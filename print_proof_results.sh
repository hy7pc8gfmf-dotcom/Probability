#!/bin/bash

# 形证概率系统 - 证明成果打印脚本
# 与coq-ci.yml工作流完美契合
# 用于打印证明结果和定理列表

# 检查是否在CI环境中运行
if [ -z "$CI" ]; then
    echo "错误: 请在GitHub Actions CI环境中运行此脚本"
    echo "使用方法: 在CI工作流中调用此脚本"
    exit 1
fi

# 检查必要的报告文件是否存在
if [ ! -f "summary_report.md" ]; then
    echo "错误: 未找到summary_report.md报告文件"
    echo "请确保在CI工作流中已生成汇总报告"
    exit 1
fi

# 打印系统标题
echo -e "\n\033[1;36m==================================================\033[0m"
echo -e "\033[1;36m    形证概率系统 (FormalCert Probability System)    \033[0m"
echo -e "\033[1;36m          证明成果概览 (v4.0)              \033[0m"
echo -e "\033[1;36m==================================================\033[0m"

# 提取证明定理列表
echo -e "\n\033[1;32m已证明的核心定理列表:\033[0m"
echo "-----------------------------------"
# 提取所有Theorem和Corollary
grep -E "Theorem|Corollary" summary_report.md | awk -F' ' '{print $2}' | sort | uniq

# 提取分布函数的关键性质
echo -e "\n\033[1;32m分布函数的关键性质:\033[0m"
echo "-----------------------------------"
grep -E "值域性质|单调性|右连续性|负无穷极限|正无穷极限" summary_report.md | sed 's/.*- \([^:]*\):.*/\1/g' | sort | uniq

# 提取期望的关键性质
echo -e "\n\033[1;32m期望的关键性质:\033[0m"
echo "-----------------------------------"
grep -E "线性性|单调性|非负性|有界收敛|单调收敛" summary_report.md | sed 's/.*- \([^:]*\):.*/\1/g' | sort | uniq

# 提取联合可测性定理
echo -e "\n\033[1;32m联合可测性定理:\033[0m"
echo "-----------------------------------"
grep -E "joint_measurability|连续映射的可测性" summary_report.md | sed 's/.*- \([^:]*\):.*/\1/g' | sort | uniq

# 提取向量运算的可测性
echo -e "\n\033[1;32m向量运算的可测性:\033[0m"
echo "-----------------------------------"
grep -E "向量加法|标量乘法|点积" summary_report.md | sed 's/.*- \([^:]*\):.*/\1/g' | sort | uniq

# 提取收敛定理
echo -e "\n\033[1;32m收敛定理:\033[0m"
echo "-----------------------------------"
grep -E "单调收敛定理|有界收敛定理" summary_report.md | sed 's/.*- \([^:]*\):.*/\1/g' | sort | uniq

# 提取关键成就总结
echo -e "\n\033[1;32m证明成果总结:\033[0m"
echo "-----------------------------------"
grep -E "关键成就" summary_report.md | sed 's/.*关键成就: //g' | sed 's/^ *//'

# 打印系统验证状态
echo -e "\n\033[1;32m系统验证状态:\033[0m"
echo "-----------------------------------"
if grep -q "✅ FormalCert_Probability_System.v 完整编译成功" summary_report.md; then
    echo -e "\033[1;32m✅ 所有证明均通过验证\033[0m"
else
    echo -e "\033[1;31m⚠️ 部分证明未通过验证，请检查详细报告\033[0m"
fi

# 打印证明定理总数
theorem_count=$(grep -E "Theorem|Corollary" summary_report.md | wc -l)
echo -e "\n\033[1;33m总证明定理数: $theorem_count\033[0m"

# 打印完成信息
echo -e "\n\033[1;36m形证概率系统证明成果打印完成\033[0m"
echo "证明成果已成功输出到控制台"
echo "详细报告和编译产物已上传到Artifacts"

# 检查是否需要发送通知
if [ "$CI" = "true" ]; then
    echo -e "\n\033[1;36mCI/CD工作流执行状态: \033[0m$(cat /github/workflow/event_name)"
    echo -e "\033[1;36m提交: \033[0m$(cat /github/workflow/commit_sha)"
    echo -e "\033[1;36m分支: \033[0m$(cat /github/workflow/branch)"
fi