# ecp_nistp384.c 的 Lean 4 证明

针对 `crypto/ec/ecp_nistp384.c` 的整数、64/128 位运算和字节内存模型；整份 C 的端到端证明未完成。
已修复标量乘负 Y 未约减导致的序列化错误，见 [SCALAR_COUNTEREXAMPLE.md](SCALAR_COUNTEREXAMPLE.md)。
当前目录入口为 `ecp_nistp384.lean`，证明模块位于 `formal/p384/P384/`。

## 运行

在仓库根目录执行：

```sh
bash formal/p384/check.sh
python3 formal/p384/check_c.py
python3 formal/p384/test_generation.py
python3 formal/p384/check_interface_c.py
python3 formal/p384/test_interfaces.py
python3 formal/p384/check_contract_c.py
python3 formal/p384/test_contract_generation.py
python3 formal/p384/check_bn_length_c.py
python3 formal/p384/test_bn_bits_generation.py
python3 formal/p384/check_scalar_c.py
python3 formal/p384/test_scalar_generation.py
python3 formal/p384/check_scalar_counterexample.py
```

使用 `/usr1/lem/tmp/lean4-p384/` 中的 Lean 4.19.0 和 mathlib4。
mathlib 提交：`c44e0c8ee63ca166450922a373c7409c5d26b00b`。
其他安装位置可设置 `LEAN_P384_ROOT`、`MATHLIB_DIR`。检查过程不下载依赖；mathlib 缓存须已就绪。

## 已证明

| 文件 | 结论 |
| --- | --- |
| `Basic.lean` | 7/13 肢、基数 2^56 的整数解释；约减表示的数值范围 |
| `Generated.lean` | 从 C 提取乘法、平方、补偿常数、约减和求逆链；证明约减的 80 个中间赋值均处于 [0, 2^128)，输出前六肢 < 2^56、末肢 ≤ 2^48 |
| `Field.lean` | 乘法/平方的精确整数等式；取负/减法的模 p 正确性；乘法/平方结果满足约减入口界限 |
| `Machine.lean` | 64 位无符号取负模型到整数模型的精化；证明约减输入不会触发该减法下溢 |
| `WordSemantics.lean` | 任意位宽的位移、低位掩码、宽化和窄化转换的整数对应关系 |
| `Bytes.lean` | 小端字节编码、截断、分块和双向还原 |
| `Serialization.lean` | 8 字节加载后取低 56 位；48 字节与 7 肢表示的双向还原及严格输出边界 |
| `BNBytes.lean` | BIGNUM 导出掩码、饱和游标、字数组读取下标边界；导入的移位与按位或累积循环 |
| `BNImport.lean` | 裁去高位零字节不改变数值；按 8 字节打包及块数计算正确；保留零输入复用对象的实际符号行为 |
| `BNExport.lean` | 导出字节等于有效字节的补零编码；屏蔽容量区中的旧数据；连接 48 字节导出与肢表示 |
| `ByteMemory.lean`、`SerializationMemory.lean` | 抽象字节内存上的读写、重叠 `memmove`、8 字节“或写”；证明六次跨 7 字节写入加末尾 6 字节复制等于序列化，且输出区外不变 |
| `InterfaceValues.lean` | 连接 BIGNUM 字数组、有效长度、导出、肢表示、内存序列化与重新导入的数值性质 |
| `SignedWords.lean`、`Carry.lean`、`ContractFirst.lean`、`ContractCarry.lean` | 有符号右移、低位掩码、借位及进位；第一阶段 19 次机器赋值精化到整数折叠；证明输出末肢严格 < 2^48 |
| `BitSlices.lean`、`ContractCompare.lean`、`ContractConditions.lean`、`ContractGates.lean` | 五个条件掩码的位段含义；证明组合条件等价于输入值 ≥ p |
| `GeneratedContract.lean`、`ContractSubtract.lean`、`ContractArithmetic.lean`、`Contract.lean` | 提取 `felem_contract` 全部 56 次赋值；证明机器模型输出值为输入值 mod p、范围为 [0,p)、满足序列化界限且收缩幂等 |
| `FieldInterfaces.lean` | 乘法、平方、求逆的机器结果，经收缩、内存序列化及 BIGNUM 打包后保持模 p 运算性质 |
| `BitWidth.lean`、`GeneratedBNWordBits.lean`、`BNWordBits.lean` | 提取并证明 64 位 `BN_num_bits_word` 六级搜索等于整数位宽；32 位计数器赋值均在有符号范围内 |
| `ConstantTime32.lean`、`BNNumBits.lean` | 32 位零检测、相等掩码；普通和 CONSTTIME 位数分支、循环前缀值及有符号范围 |
| `BNNormalize.lean` | 规范化循环保持数值、读取下标有效、末字非零或 top=0；零值清除符号；区分 release/debug 标志位掩码 |
| `BNLength.lean` | 包含规范化重试的导出长度判定等价于数值可编码；48 字节成功返回 48，超长返回 −1 且输出不变 |
| `BNToFelem.lean`、`CheckedFieldInterfaces.lean` | 连接符号检查、位数检查、字节导出和肢转换的成功/拒绝路径；成功输入经乘法、平方或求逆再导出满足模 p 规格 |
| `GeneratedMachine.lean` | 128 位约减模型的全部 80 次赋值及 64 位输出转换逐步精化到整数轨迹；证明输出边界与模 p 正确性 |
| `GeneratedProducts.lean`、`ProductRefinement.lean` | 64 位输入宽化、平方前的 64 位倍增、128 位乘法/平方及组合约减的精化 |
| `Counterexamples.lean` | 证明 `felem_neg` 注释中的输入契约不足、输出边界错误 |
| `Reduction.lean` | 约减前后的差是 p 的整数倍；组合乘法/平方约减正确且满足输出边界 |
| `Inversion.lean` | C 求逆链的指数精确为 p−2；连接肢运算与 ZMod p；保持约减表示；非零输入的逆元性质依赖显式参数 `hp : p.Prime` |
| `Pratt.lean`、`Prime.lean` | 用 Lucas 定理和数值 Pratt 证书证明 `p_prime : p.Prime`；模幂由 Lean 内核计算 |
| `MachineInversion.lean` | 组合机器运算的求逆链保持约减表示，并正确计算非零输入的逆元；无需素性假设 |
| `Representation.lean`、`GeneratedZero.lean`、`ZeroRefinement.lean` | 约减表示的唯一性；完整零检测掩码和 0/1 结果的正确性；有符号减法边界 |
| `Points.lean` | 手工建模 Jacobian 点加/点倍公式；证明与仿射公式等价、点倍保持曲线方程及无穷远/相等分支性质 |
| `ScalarBits.lean`、`GeneratedBooth.lean`、`Booth.lean`、`ScalarWindows.lean` | 48 字节位读取及读取范围；C 的 32 位整型提升、8 位赋值和 64 位窗口拼接；完整 Booth 辅助函数、符号与数字范围、77 个窗口重建原标量 |
| `Comb.lean` | 95 位间隔、99 轮梳形窗口及四列系数重建 384 位标量 |
| `Selection.lean` | 完整 21 肢扫描；16/17 项查表正确，越界索引输出零，读取下标范围 |
| `BatchSchedule.lean`、`ScalarMul.lean` | `skip` 不变量、首次复制和后续加法、381/99 轮、普通点与生成元交织；任意交换群中的结果等于线性组合 |
| `ScalarPrecompute.lean`、`JacobianPrecompute.lean` | 0..16 项预计算，奇数项点加和偶数项点倍；Jacobian 公式的预计算表表示正确倍数 |
| `ScalarNegation.lean` | Booth 符号生成的条件复制掩码、机器 Y 取负和曲线域值；证明取负后 Y 及 Y+Z 满足平方入口范围 |
| `CurveGroup.lean`、`JacobianBatch.lean` | Jacobian 点加、点倍、取负对应 mathlib 曲线群，包含相等点、逆点、无穷远分支；坐标循环精化到群循环 |
| `GeneratedScalarConstants.lean`、`ScalarCurve.lean` | 从 C 提取曲线参数和全部内置表项；核验 p、a、生成元坐标、各肢范围、非零表项的曲线方程与非奇异性 |
| `GeneratedGeneratorWitness.lean`、`ScalarTable.lean` | 内核核验 285 次倍点见证及内置表的全部组合；证明每个表项为梳形系数乘以标准生成元 |
| `JacobianScalar.lean` | 合成机器窗口读取与重编码、预计算、选项符号、内置生成元表及坐标循环；`jacobianScalarMul_correct` 证明坐标数学模型输出表示所需线性组合 |
| `GeneratedScalarOutput.lean`、`ScalarOutput.lean` | 提取 `batch_mul` 输出阶段的零初始化、64→128 位宽化和约减；对任意 7 个 64 位肢证明输出约减、模 p 保值、后续收缩和 BN 导出正确 |
| `ScalarCounterexample.lean` | 保留修复前的数值反例；证明新增约减后输出 Y 精确正确、满足序列化范围且点在曲线上 |
| `Words.lean` | 64 位条件复制、查表掩码和零检测掩码；查表索引限于 5 位，零检测输入限于非负的 63 位数 |
| `Audit.lean` | 审计全部 P384 定理，只允许 `propext`、`Classical.choice`、`Quot.sound` |

约减入口要求每肢满足 0 ≤ in[i] < 2^128−2^125。
乘法/平方边界证明要求每个输入肢位于 [0, 2^61)。所有前提均出现在定理类型中。
证明不使用 `sorry`、自定义公理或 `native_decide`。

## 源码关联与边界

`generate.py --check` 核对源码 SHA-256，并重新生成模型逐字比较。
源码变更后应先审查，再运行 `python3 formal/p384/generate.py` 和全部检查。
提取器不是经过证明的 C 前端。乘法、平方、约减、求逆及零检测使用受限语法检查；
额外语句、截断转换和复制/循环变化会被拒绝，或使对应证明失败。
`test_generation.py` 覆盖 14 个会破坏源码关联的变异，包括删除乘法前的宽化转换。
64/128 位运算与整数模型之间已有 Lean 精化；它不建立完整 C 操作语义、调用栈或内存对应关系。

`generate_contract.py --check` 重新提取 `felem_contract` 全部语句并比较模型；
验证局部变量类型、两个 `memcpy`、条件循环及两处相同的进位序列。
`test_contract_generation.py` 包含 11 项检查；合法表达式变化会改变模型，须重新通过 Lean 证明。
该提取器同样不是经过证明的 C 前端。

`generate_bn_bits.py --check` 核对六级搜索的全部语句及 64 位分支。
`test_bn_bits_generation.py` 包含 10 项检查，覆盖移位、增量、更新、类型、CT 辅助函数和 release 标志位宏变化。

`generate_scalar.py --check` 重新提取 Booth 辅助函数、曲线参数、内置表、输出约减，并重建倍点见证。
`ScalarTable.lean` 独立核验见证的每一步；见证生成器不属于证明的可信基础。
`test_scalar_generation.py` 包含 19 项检查，覆盖重编码语句、移位、类型、数组维数、字节宽度、表常数、输出零初始化、复制范围、约减及循环指纹变化。
`scalar-sources.json` 绑定位读取、查表、标量循环、点运算及调用者的审阅版本；
这些循环仍是手工翻译，指纹不证明翻译正确。

其他接口循环采用手工翻译；`check_interfaces.py` 核对 `interface-sources.json` 中 19 个函数及两个 BN 头文件的去空白、去注释指纹。
这只能绑定审阅过的源码，不能证明翻译正确，也不表示全部被监控函数均已完整证明。
`test_interfaces.py` 检查 7 种源码变异被拒绝及当前指纹匹配。

素性证书数据保存在 `primality-certificate.json`，来自其中注明的固定提交。
仅使用其数值，证明在本工程重新构造；不导入上游证明代码。
复验无需联网。重新生成命令：`python3 formal/p384/generate_primality.py`。

`check_c.py` 从当前源码提取函数体，在本机重新编译，启用 UBSan，
与独立的 Python 整数/仿射运算比较，包括极值、零、p、p−1、相等点、逆点和无穷远点。
这是补充测试，不是 C 与 Lean 的形式化精化证明。

`check_interface_c.py` 重新编译当前 C 的转换、位数计算和规范化函数体，启用 UBSan，
通过 9,453 项差分检查，覆盖补零、容量区旧数据、CONSTTIME 标志、负数、超长输入和分配失败。
分配、扩容、清理和常数时间相等辅助函数采用本地测试替身；不能据此证明 OpenSSL 内存管理实现。

`check_contract_c.py` 为当前 C 函数体插入阶段快照，进行 5,057 项检查，
覆盖全部 32 种条件组合、第一阶段折叠、条件减法、规范输出及幂等性，启用 UBSan。

`check_bn_length_c.py` 重新编译当前位数、规范化、导出函数体及四个实际 CT 辅助函数，
通过 26,561 项检查，覆盖前导零、固定长度对象、CONSTTIME 标志、规范化重试、负长度、拒绝路径和输出区外不变。
使用 release 宏配置，关闭 `BN_DEBUG`/`BN_RAND_DEBUG`，启用 UBSan。
release 中 `BN_FLG_FIXED_TOP=0`，规范化保留全部标志位；debug 的 0x10000 清除行为另有参数化定理。

`check_scalar_c.py` 提取当前标量乘、位读取、查表、Booth 函数和内置表，与独立仿射运算比较。
2,426 项检查覆盖最高位、负零、空输入、全部表项、普通点预计算、两种 mixed 模式、混合多标量输入及最终规范序列化，启用 UBSan。
`check_scalar_counterexample.py` 的 8 个回归场景覆盖相消后负窗口、生成元与普通点相消、无穷远及零结果；均检查最终字节值。
`check_scalar_api.c` 在启用此实现的独立完整库中验证公开 `EC_POINTs_mul`、`EC_POINT_mul` 和 EVP 验签；修复前两个点乘失败，修复后全部通过。

接口值定理针对小端、64 位字和 `size_t`、`BN_BYTES=8`。
新增位数及规范化模型采用 32 位 `int`、非 e2k、`BN_DEBUG` 关闭的配置。
导出要求有效长度不超过容量、容量字节数 < 2^63；保值的 48 字节导出还要求数值 < 2^384。
序列化保值要求前六肢 < 2^56、末肢 < 2^48；约减结果的末肢 ≤ 2^48 不足以满足此条件。
`serializeMemory_correct` 无须此范围即可证明输出字节及区外不变；`serializeMemory_value` 显式要求该范围。
`machineContract_correct` 已从约减输入推出这一严格范围；
`machineContract_to_bn_value` 不再要求调用者另行假设收缩输出范围。
字节内存模型采用小端加载和输入肢值快照；未证明 C 指针的类型、对齐、有效对象、别名和生命周期规则。

BN 长度与转换定理要求 `top ≤ dmax`、`64*dmax+7 < 2^31`，允许有效区末尾为零。
已证明分配器限制 `dmax ≤ INT_MAX/(4*64)` 蕴含该算术界限；尚未证明所有对象构造路径保持它。
`bnPadLengthAccept48_correct` 不再把 `BN_num_bits` 或规范化的正确性作为接口假设。
`bnToFelemCall_success` 证明转换成功当且仅当符号为非负且数值 < 2^384；拒绝时保留原输出肢数组。

尚未证明：全部点运算 C 调用点及最终 X/Z 满足相应输入不变量、
点运算全部机器调用边界、预计算表的机器精化及批量仿射化、
BN 对象构造、分配失败路径及错误队列、
`BN_CTX`、`BN_nnmod`、EC 接口及内存管理、汇编分支、
完整 C 有符号运算与内存操作语义、编译器精化、内存安全或常数时间性。

标量乘的群与坐标数学模型已证明；`jacobianScalarMul_correct` 的输入前提是每个标量恰为 48 字节，
且输入坐标表示相应曲线点。它不把 64/128 位 C 点运算、`mixed` 优化、批量仿射化、
BN 标量规范化和分配/错误路径等同于已证明的接口。
普通点表在坐标模型中由点加/点倍构造；实际 `select_point` 的机器扫描正确性另由 `Selection.lean` 给出。
生成元索引模型中的 `%16` 在有效输入上已证明不改变索引。

实际 `BN_lebin2bn` 向已为负数的对象导入 48 个零字节时，会留下 `top=0, neg=1`。
已用当前 C 测试确认，并由 `bnImportSign_zero48` 记录；不能假定该路径总会清除符号。
这不影响数值为零的结论；是否可从本文件公共接口到达该状态尚未证明。BN 实现未修改。

## 端到端证明的实际阻碍

整份 C 的端到端证明尚未完成。现有模型定理和公理审计不能代替该证明。

修复前，两个有效点 −G、G，标量 32、16，在完整计算与序列化路径上得到错误结果。
`batch_mul` 现在返回前将 Y 的七个 64 位肢宽化到零初始化的宽数组，并调用一次 `felem_reduce`。
`machineScalarOutputY_correct` 无须输入约减假设；`machineScalarOutputY_to_bn` 证明接续收缩和 BN 导出的模 p 数值。
`ScalarCounterexample.lean` 保留旧路径反例并核验修复后的具体输出；完整 C 标量执行轨迹尚未形式化。

`felem_neg` 的注释允许每肢 < 2^60−2^29，但以下输入违反取负的模 p 正确性：

```text
in = [0, 1148417904979476465, 0, 0, 0, 0, 0]
out[1] = 18446744073709551615
(value(out) + value(in)) mod p = 2^120，而不是 0
```

零输入还会得到 out[0] = 1152939096792887296 > 2^60，违反注释的输出界限。
上述反例已用 Lean 的 `BitVec 64` 证明；实际 C 复现命令：

```sh
python3 formal/p384/check_neg_contract.py
```

这些反例没有证明公共接口能到达错误输入。
`machineNeg_correct_reduced` 已证明约减输入的取负正确；完整证明仍须从每个 C 调用点推出该不变量。

本地 `clean/export/CCLib` 的 Clight 库没有 128 位整数类型或值，且要求 Lean 4.32.1；
当前环境为 Lean 4.19.0。不能把该库直接用于此文件的 `uint128_t` 运算。
当前 OpenSSL 配置还定义了 `OPENSSL_NO_EC_NISTP_64_GCC_128`，排除了本文件；
因此验证构建必须另行明确启用该实现。对整份源码的 Clang 语法检查已在临时包装单元中启用它并通过，
但这不建立 C 到 Lean 的语义精化。
