# 标量乘输出回归

已修复：`batch_mul` 返回前对 Y 执行一次完整约减，恢复 `felem_contract` 的输入范围。
以下记录修复前的反例。

输入标准 P-384 生成元 G，两个点 −G、G，标量 32、16，无独立生成元标量。
两点均为合法仿射点，标量均非负且小于群阶。期望输出 −16G。

在 i=5，两个窗口贡献 −G、G，累加器变为无穷远。
在 i=0，第一点贡献零，第二点选择 −16G。
`felem_neg` 产生未约减的 Y；`point_add` 的无穷远分支直接复制它。
最终 `felem_contract` 的输入范围被违反，`felem_to_bin48` 截去未传播的高位。
序列化结果错误，且不在曲线上。

调用者在两点输入时使用 mixed=1。该路径的 Y：

```text
实际: 27eadd621ed6f92dbe7e92a1656bb70e2be2b03bf1d5c42463545a81bbf585442edef3460b640ddc88dd48ab1454c98c
期望: 27eadd621ed6f92dbe7e92a1656bb70e2be2b03bf1d5c42463545a81bbf585442edef3460b640ddc97dd48ab1454c98c
```

回归检查：

```sh
python3 formal/p384/check_scalar_counterexample.py
bash formal/p384/check.sh GeneratedScalarOutput ScalarOutput ScalarCounterexample Audit
```

C 回归提取当前预计算、实际批量仿射化辅助函数、标量循环、收缩和序列化函数体，重新编译并启用 UBSan。
修复前首先失败于序列化数值；修复后 8 个场景均通过，包含两种 mixed 模式、生成元相消、无穷远和零结果。

Lean 的 `scalarCounterexampleEncodedY_incorrect`、`scalarCounterexampleEncodedY_value`、
`scalarCounterexampleEncodedY_off_curve` 核验同一 Y 的机器取负、机器收缩及字节编码结果。
`scalarCounterexample_group_value` 证明期望群值。
新增 `scalarCounterexampleFixedEncoding_value` 和 `scalarCounterexampleFixedEncoding_on_curve` 核验修复后的正确输出。
`machineScalarOutputY_correct` 对任意七个 64 位肢证明约减与模 p 保值，随后连接收缩、序列化和 BN 导出。
完整 C 标量循环的具体执行轨迹尚未在 Lean 中证明。

公开接口验收使用独立构建：`enable-ec_nistp_64_gcc_128 no-shared no-tests`。
同一 `check_scalar_api.c` 在修复前的完整库中报告两个公开点乘失败，修复后均通过；EVP 的有效签名与修改摘要检查前后均通过。
验收代码比较实际 EC_METHOD 指针，确认使用此实现。当前目录的默认配置未改动。

在该完整库的构建目录外运行（`p384_build` 指向其根目录）：

```sh
cc -std=c11 -O2 -Wall -Wextra -Werror -I"$p384_build/include" \
  formal/p384/check_scalar_api.c "$p384_build/libcrypto.a" \
  -pthread -ldl -o formal/p384/.build/scalar-api-test
formal/p384/.build/scalar-api-test
```
