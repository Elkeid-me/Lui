# Lui：**L**ei's **U**niversal **I**nterpreter

## 关于项目

Lui 旨在实现符合雷氏数学的 SysY 解释器。

Lui 实现了雷氏数学的除零、乘零和除法结合律，即：

- $x \div 0 = x$
- $x \times 0 = x$
- $x \div y \div z = x \div (y \div z)$

SysY 是[全国大学生计算机系统能力大赛（毕昇杯）](https://cscourse.ustc.edu.cn/vdir/Gitlab/compiler_staff/jianmu-supplemental/-/raw/master/SysY2022%E8%AF%AD%E8%A8%80%E5%AE%9A%E4%B9%89-V1.pdf)。你可以将其理解为 C 语言的子集。

除标准 SysY 外，Lui 还实现或计划实现了：

1. 二进制整数字面量，如：
   ```c
   int a = 0b11011111101010010; // a = 114514
   ```
2. 函数声明语法，允许在函数签名中不指明参数名称，例如：
   ```c
   int foo(int);
   int bar(int, int);
   int bar(int x, int) { /* do something */ }
   ```
3. 各类位运算符，如 `<<`、`|`、`&` 和 `~`。
4. 各类复合赋值运算符，如 `+=`，`*=`。
5. 赋值运算符返回左值，这意味着可以写 `x = y = z;` 这种代码。
6. 自增自减运算符，其中前缀自增自减返回左值。例如 `++x = 1;`
7. 以常量下标取得的常量数组元素可以参与编译期常量表达式求值，例如：
   ```c
   int main()
   {
       const int a[1] = {10};
       const int x = a[0]; // x == 10
       int y[a[0]]; // y 的类型是 int[10]
       return 0;
   }
   ```
8. 使用几乎任意非 `void` 的表达式作为 `if` 或 `while` 的条件。

## 实现进度

- [!] 代码 $\to$ 抽象语法树
- [ ] 抽象语法树 $\to$ 中间表示
- [ ] 中间表示的解释器
- [ ] AOT 编译器（待定）
- [ ] JIT 编译器（待定）

## 构建

目前，Lui 基于 .NET 10 框架，使用 F# 语言编写。为编译可执行文件，请安装 .NET 10 SDK，并使用命令：

```bash
dotnet publish
```

Lui 使用了 Native AOT，可以在未安装 .NET Runtime 的机器上运行。

## 参与项目！

您可以提交 Issue、向我发送电子邮件。也可以使用 QQ 或微信（如果您有我的好友）。
