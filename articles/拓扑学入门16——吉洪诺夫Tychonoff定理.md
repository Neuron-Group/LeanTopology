---
id: "556647150"
title: "拓扑学入门16——吉洪诺夫（Tychonoff）定理"
author: "sumeragi693"
type: zhihu-article
source: "https://zhuanlan.zhihu.com/p/556647150"
created: "2022-08-26 06:37"
updated: "2024-03-25 22:41"
downloaded: "2026-04-20"
---
[https://zhuanlan.zhihu.com/p/555842689](https://zhuanlan.zhihu.com/p/555842689)

## 前言

本章将证明吉洪诺夫定理。该定理主张任何数量的紧空间的积空间都是紧空间，这是拓扑学中最重要的定理之一。

## 正文

首先，作为吉洪诺夫定理证明的准备，先证明一个十分漂亮的亚历山大（Alexander）子基定理。该定理说明，证明紧性时只考虑由属于某个子基的开集构成的开覆盖就足够了。

为了证明亚历山大子基定理，需要一些基础性的讨论，即使用佐恩（Zorn）引理的形式来完成。佐恩引理与其说是拓扑学，不如说是集合论的内容，不过为了让证明更加完整，在此也一并证明它。首先，来复习一下为此所需要的有关有序集的术语。

集合 $X$ 中的二元关系 $\leq$ 满足以下3个条件时称为**偏序关系**或简称**序关系**， $(X,\leq)$ 称为**偏序集**（或有序集、半序集）。

-   1)对于任意 $x\in X$ ，有 $x\le x$ （自反性）。
-   2)如果 $x\le y,y\le z$ ，那么 $x\le z$ （传递性）。
-   3)如果 $x\le y,y\le x$ ，那么 $x=y$ （反对称性）。

当 $x\le y$ 且 $x\ne y$ 时，写作 $x<y$ 。进一步地，当 $\le$ 还满足以下第4个条件时， $(X,\leq)$ 称为**全序集**。

-   4)对于任意 $x,y\in X$ ，或者 $x\le y$ 成立，或者 $y\le x$ 成立（即任意两个元素之间都存在序关系）。

例如，数集 $\mathbb N,\mathbb Z,\mathbb Q,\mathbb R$ 在通常意义的大小关系下都是全序集，而 $\mathbb C$ 是偏序集。

为了方便接下来的证明，依然把 $x\le y$ 称作“ $x$ 小于或等于 $y$ ”，把 $x<y$ 称作“ $x$ 小于 $y$ ”。当然这只是一种称呼，并不一定是数的大小关系。

设 $(X,\le)$ 为偏序集， $A\subseteq X$ 。元素 $a\in A$ 称为 $A$ 的**最小元**，指的是对于任意 $b\in A$ ，都有 $a\le b$ 。集合 $A$ 的最小元未必存在（如开区间 $(a,b)$ ），但只要存在就一定唯一。同样也可以定义 $A$ 的**最大元**。

偏序集 $(X,\le)$ 称为**良序集**，指的是任意非空子集都存在最小元。特别地，对于任意 $x,y\in X$ ，因为 $\left\{ x,y \right\}\subseteq X$ 也存在最小元，所以良序集一定是全序集。例如，数集 $\mathbb N$ 在通常意义的大小关系下是良序集。

元素 $x\in X$ 称为子集 $A$ （在 $X$ 中）的**上界**，指的是对于任意 $a\in A$ ，都有 $a\le x$ 。更强的情况是，如果对于任意 $a\in A$ ，都有 $a<x$ ，即 $a\le x$ 且 $a\ne x$ ，那么 $x$ 称为 $A$ 的**真上界**（或严格上界）。显然 $A$ 的真上界 $x\notin A$ 。

设 $(X,\le)$ 为偏序集，元素 $x\in X$ 称为 $X$ 的**极大元**，指的是当元素 $y\in X$ 满足 $x\le y$ 时， $y=x$ 。等价说法是不存在 $y\in X$ ，使得 $x<y$ 。注意要区分 $X$ 的最大元和极大元。最大元指的是对于任意 $y\in X$ ，都有 $y\le x$ ，这要求 $X$ 中的任意元素都和 $x$ 存在序关系（简单来说，就是任意元素都能和 $x$ 比较大小）。而极大元指的是满足 $x\le y$ 的元素 $y\in X$ 有且只有 $x$ ，也就是说 $y$ 未必和 $x$ 存在序关系，但只要存在序关系就一定满足 $y\le x$ （简单来说，就是把所有和 $x$ 存在序关系的元素找出来构成子集 $X'$ ，而 $x$ 是 $X'$ 的最大元）。当然在全序集中二者是等价的概念。

设 $(X,\le)$ 为偏序集， $A\subseteq X$ 。把序关系 $\le$ 限制在 $A$ 中得到 $\le_A$ ，则 $(A,\le_A)$ 也构成偏序集。如果 $(A,\le_A)$ 还是全序集或良序集，那么 $A$ 称为 $X$ 的**全序子集**或**良序子集**。容易验证全序集的子集都是全序子集，良序集的子集都是良序子集。

### 定理16.1（佐恩引理）

设 $(X,\le)$ 为偏序集。如果 $X$ 的任意全序子集 $A$ 在 $X$ 中都存在上界，那么 $X$ 存在极大元。

证明：假设 $X$ 不存在极大元，那么对于任意全序子集 $A$ ，它在 $X$ 中一定存在真上界。这是因为由已知条件， $A$ 存在上界 $x$ 。而因为 $X$ 不存在极大元，所以一定存在 $y\in X$ ，使得 $x<y$ 。此时， $y$ 就是 $A$ 的真上界。于是对每个全序子集 $A$ ，可以选择它的某个真上界记作 $u(A)$ 。用映射的语言来说，把所有全序子集组成的集族记作 $\mathcal A\subseteq P(X)$ ，则映射 $u:\mathcal A\rightarrow X$ 把每个全序子集 $A$ 映射成它的真上界 $u(A)\in X$ 。

对于 $C\subseteq X$ 和 $x\in C$ ，集合 $C_x=\left\{ y\in C|y<x \right\}$ 称为 $C$ 在 $x$ 处的**切片**。由定义可知当 $x,x'\in C$ 且 $x< x'$ 时， $C_x\subset C_{x'}$ ；而当 $x\in C\subseteq C'$ 时， $C_x\subseteq C'_x$ 。如果 $C$ 同时满足以下两个条件，就把 $C$ 称为 $X$ 中的**链**（或锁、锁链）。

1.  $C$ 是 $X$ 的良序子集（从而也是全序子集）；
2.  对于任意 $x\in C$ ，都有 $x=u(C_x)$ ，即切片 $C_{x}$ 在映射 $u$ 下的像恰好为下标 $x$ 。

此时，以下主张成立：

*对于* $X$ *中的任意两条链* $C,C'$ *，或者* $C=C'$ *，或者其中一方是另一方的某个切片。*

该主张的证明稍后再进行（命题16.2），在此先利用它继续证明佐恩引理。设 $X$ 中所有链组成的集族为 $\left\{C_\lambda|\lambda\in\Lambda  \right\}$ ，再令 $C=\bigcup_{\lambda\in\Lambda} C_\lambda$ 为所有链之并。此时， $C$ 也是 $X$ 中的链，理由如下。

先证 $C$ 是 $X$ 的良序子集。设 $\emptyset\ne A\subseteq C$ 为任意非空子集，则存在某个 $\lambda\in\Lambda$ ，使得 $A\cap C_\lambda\ne\emptyset$ 。而 $C_\lambda$ 为 $X$ 的良序子集，所以集合 $A\cap C_\lambda\subseteq C_\lambda$ 存在最小元 $x_0$ 。任取 $x\in A$ ，则存在某个 $\mu\in\Lambda$ ，使得 $x\in C_\mu$ 。如果 $\lambda=\mu$ ，那么 $x\in A\cap C_\lambda$ ，所以 $x_0\le x$ 。如果 $\lambda\ne\mu$ ，根据上述主张，或者 $C_\lambda$ 是 $C_\mu$ 的某个切片，即存在 $y\in C_\mu$ 使得 $C_\lambda=(C_\mu)_y$ ；或者 $C_\mu$ 是 $C_\lambda$ 的某个切片，即存在 $z\in C_\lambda$ 使得 $C_\mu=(C_\lambda)_z$ 。后者，根据切片的定义， $C_\mu\subset C_\lambda$ ，所以 $x\in A\cap  C_\lambda$ ，从而 $x_0\le x$ 。前者又可细分成两种情况，第一种是 $y\le x$ ，第二种是 $x<y$ （因为 $C_\mu$ 是链，所以是全序集，所以 $x,y\in C_\mu$ 之间一定存在序关系）。第一种， $x_0\in  A\cap C_\lambda\subseteq C_\lambda=(C_\mu)_y$ ，所以 $x_0<y\le x$ 。第二种， $x\in(C_\mu)_y=C_\lambda$ ，所以 $x\in A\cap  C_\lambda$ ，从而 $x_0\le x$ 。不管哪种情况下都有 $x_0\le x$ ，且 $x_0\in A\cap C_\lambda\subseteq A$ ，所以 $x_0$ 是 $A$ 的最小元。由 $A$ 的任意性可知 $C$ 是 $X$ 的良序子集。

再证对于任意 $x\in C$ ，都有 $x=u(C_x)$ 。设 $x\in C$ 为任意一点，则存在某个 $\lambda\in\Lambda$ ，使得 $x\in C_\lambda$ 。因为 $C_\lambda\subseteq C$ ，所以 $(C_\lambda)_x\subseteq C_x$ 。反过来，任取 $w\in C_x$ ，则 $w\in C$ 且 $w<x$ 。此时存在某个 $\mu\in\Lambda$ ，使得 $w\in C_\mu$ 。如果 $\lambda=\mu$ ，那么 $w\in C_\lambda$ ，所以 $w\in(C_\lambda)_x$ 。如果 $\lambda\ne\mu$ ，根据上述主张，或者 $C_\lambda$ 是 $C_\mu$ 的某个切片，即存在 $y\in C_\mu$ ，使得 $C_\lambda=(C_\mu)_y$ ；或者 $C_\mu$ 是 $C_\lambda$ 的某个切片，即存在 $z\in C_\lambda$ ，使得 $C_\mu=(C_\lambda)_z$ 。后者，根据切片的定义， $w\in C_\mu\subset C_\lambda$ ，所以 $w\in (C_\lambda)_x$ 。前者，由 $x\in C_\lambda=(C_\mu)_y$ 得 $x<y$ ，所以 $w<x<y$ 。而 $w,y\in C_\mu$ ，所以 $w\in (C_\mu)_y=C_\lambda$ ，从而 $w\in (C_\lambda)_x$ 。不管哪种情况下都有 $w\in (C_\lambda)_x$ ，根据 $w$ 的任意性得 $C_x\subseteq  (C_\lambda)_x$ ，因此 $(C_\lambda)_x=C_x$ 。而 $C_\lambda$ 是链，所以 $x=u[(C_\lambda)_x]=u(C_x)$ 。

现在 $C$ 满足链的定义，所以 $C$ 是链。 $C$ 也是全序子集，所以 $C$ 在 $X$ 中存在某个真上界 $u(C)$ 。

令 $\bar C=C\cup\left\{ u(C) \right\}\supset C$ ，任取非空子集 $B\subseteq \bar C$ 。当 $u(C)\notin B$ 时， $B\subseteq C$ ，而 $C$ 是良序子集，因此 $B$ 存在最小元。当 $u(C)\in B$ 时， $B-\left\{ u(C) \right\}=B\cap C\subseteq C$ ，因此 $B-\left\{ u(C) \right\}$ 存在最小元，记作 $x\in B-\left\{ u(C) \right\}=B\cap C\subseteq C$ 。而 $u(C)$ 的定义告诉我们 $x< u(C)$ ，所以 $B=(B-\left\{ u(C) \right\})\cup\left\{ u(C) \right\}$ 依然存在最小元 $x$ 。两种情况下 $B$ 都存在最小元，所以 $\bar C$ 是良序子集。又任取 $y\in \bar C$ ，则 $\bar C_y=\left\{ z\in\bar C|z<y \right\}$ 。当 $y=u(C)$ 时，显然 $\bar C_y=C$ ，那么 $y=u(\bar C_y)$ 。当 $y\in C$ 时， $\bar C_y=\left\{ z\in\bar C|z<y \right\}=\left\{ z\in C|z<y \right\}=C_y$ ，由 $C$ 是链可知 $y=u(C_y)=u(\bar C_y)$ 。两种情况下都有 $y=u(\bar C_y)$ ，结合 $\bar C$ 是良序子集得 $\bar C$ 也是链。

然而，根据 $C$ 的定义可知 $\bar C\subseteq C$ ，与 $\bar C\supset C$ 矛盾。所以假设不成立， $X$ 一定存在极大元。

证毕。

现在来证明上述主张。

### 命题16.2（两条链的关系）

对于 $X$ 中的任意两条链 $C,C'$ ，或者 $C=C'$ ，或者其中一方是另一方的某个切片。

证明：设 $C,C'$ 中的两条链，只要证明当 $C\ne C'$ ，即 $C\nsubseteq C'$ 或 $C'\nsubseteq C$ 时，其中一方是另一方的某个切片。为此，不妨设 $C\nsubseteq C'$ （ $C'\nsubseteq C$ 时同理），则 $C\supseteq C-C'\ne\emptyset$ 。由 $C$ 是链得 $C-C'$ 存在最小元 $x_1\in C-C'\subseteq C$ 。此时 $C_{x_1}=\left\{ y\in C|y<x_1 \right\}$ ，而 $\forall x\in C-C',x_1\leq x$ 恒成立，即所有属于 $C$ 且不属于 $C'$ 的元素都不在 $C_{x_1}$ 中，所以 $C_{x_1}$ 要么是空集，不空时元素一定都来自 $C'$ 。两种情况下都有 $C_{x_1}\subseteq C'$ 成立。

假设该包含关系取不到等号，则 $C'\supseteq C'-C_{x_1}\ne\emptyset$ 。由 $C'$ 是链得 $C'-C_{x_1}$ 存在最小元 $x_2\in C'-C_{x_1}\subseteq C'$ 。同理可证 $C_{x_2}'=\left\{ y\in C'|y<x_2 \right\}\subseteq C_{x_1}$ 。

再次假设该包含关系取不到等号，则 $C\supseteq C_{x_1}\supseteq C_{x_1}-C_{x_2}'\ne\emptyset$ 。由 $C$ 是链得 $C_{x_1}-C_{x_2}'$ 存在最小元 $x_3\in C_{x_1}-C_{x_2}'\subseteq C_{x_1}\subseteq C$ 。因为 $x_3\in C_{x_1}$ ，所以 $x_3<x_1$ ，那么 $C_{x_3}=\left\{ y\in C|y<x_3 \right\}\subset C_{x_1}$ ，即 $C_{x_3}$ 中的元素全都来自 $C_{x_1}$ 。于是又同理得 $C_{x_3}\subseteq C_{x_2}'$ 。

任取 $x\in C_{x_2}'\subseteq C'$ ，由 $x_3<x_1\Rightarrow x_3\in C_{x_1}\subset C'$ 可知 $x,x_3$ 都是链 $C'$ 的元素，所以可以分成 $x<x_3$ 和 $x_3\le x$ 两种情况。后者不可能成立，否则由 $x\in C_{x_2}'\Rightarrow x<x_2$ 可以得到 $x_3<x_2\Rightarrow x_3\in C_{x_2}'$ ，和 $x_3\in C_{x_1}-C_{x_2}'$ 矛盾，所以只可能是 $x<x_3$ 的情况。由 $x\in C_{x_2}'\subset C_{x_1}\subseteq C$ 得 $x,x_3$ 也都是链 $C$ 的元素，所以 $x<x_3\Rightarrow x\in C_{x_3}$ 。于是由 $x$ 的任意性可知 $C_{x_2}'\subseteq C_{x_3}$ ，那么 $C_{x_3}= C_{x_2}'$ 。

因为 $C,C'$ 都是链，所以 $x_2=u(C'_{x_2})=u(C_{x_3})=x_3\in C_{x_1}$ ，但这与 $x_2\in C'-C_{x_1}$ 矛盾。所以假设 $C_{x_2}'\subseteq C_{x_1}$ 取不到等号不成立，即唯一的可能性是 $C_{x_2}'= C_{x_1}$ 。同理， $x_1=u(C_{x_1})=u(C'_{x_2})=x_2\in C'$ ，这又与 $x_1\in C-C'$ 矛盾。所以假设 $C_{x_1}\subseteq C'$ 取不到等号也不成立，即唯一的可能性是 $C_{x_1}=C'$ 。这就是要证明的结论。

证毕。

### 注意16.3（佐恩引理的另一版本）

在佐恩引理（定理16.1）的描述中可以插入两次“非空”一词，实际上插入后的版本更常用。

*设* $(X,\le)$ *为****非空****偏序集。如果* $X$ *的任意****非空****全序子集* $A$ *在* $X$ *中都存在上界，那么* $X$ *存在极大元。*

让我们从定理16.1来推导它。要想利用定理16.1，就要说明 $X$ 的任意全序子集 $A$ 在 $X$ 中都存在上界。现在已知任意非空全序子集都存在上界，因此只需要说明① $\emptyset$ 是全序子集② $\emptyset$ 在 $X$ 中存在上界。

①是很容易验证的，因为 $A$ 是全序集的定义是 $\forall x,y(x,y\in A\rightarrow x\le y\vee y\le x)$ ，现在命题 $x,y\in\emptyset$ 不成立，所以蕴涵式为真，即 $\emptyset$ 满足全序集的定义。②也很容易验证，因为 $X\ne\emptyset$ ，所以任取 $x\in X$ ，根据上界的定义， $\forall y(y\in \emptyset\rightarrow y\le x)$ 的条件 $y\in\emptyset$ 不成立，所以蕴涵式为真，即 $x$ 满足 $\emptyset$ 的上界的定义。现在得到了 $\emptyset$ 也存在上界，于是 $X$ 的任意全序子集 $A$ 在 $X$ 中都存在上界，根据定理16.1， $X$ 存在极大元。

### 定理16.4（亚历山大子基定理）

设 $X$ 为拓扑空间，以下命题等价：

1.  $X$ 是紧空间。
2.  存在某个子基 $\mathcal S$ ，使得由 $\mathcal S$ 中的开集所构成的任意开覆盖 $\mathcal U\subseteq\mathcal S$ 都具有有限子覆盖。

证明： $1\Rightarrow2$ 显然，只证 $2\Rightarrow1$ 。

假设 $X$ 不紧，那么存在某个开覆盖 $\mathcal U_0$ 没有有限子覆盖。把所有这样的开覆盖找出来组成集族 $\Phi=\left\{ \mathcal U|\mathcal U为X的开覆盖且没有有限子覆盖 \right\}$ ，并在 $\Phi$ 中定义关系 $\leq$ 为 $\mathcal U\le \mathcal V\Leftrightarrow \mathcal U\subseteq\mathcal V$ 。容易验证 $\leq$ 是序关系，所以 $(\Phi,\le)$ 成为偏序集。

因为 $\mathcal U_0\in\Phi$ ，所以 $\Phi$ 非空。设 $\emptyset\ne \Psi\subseteq\Phi$ 为任意非空全序子集，把其中的元素（开覆盖）对应到某个指标集 $\Lambda$ ，则它可以写成 $\Psi=\left\{ \mathcal U_\lambda|\lambda\in \Lambda \right\}$ ，并且 $\Lambda\ne\emptyset$ 。令 $\mathcal U=\bigcup_{\lambda\in \Lambda} \mathcal U_{\lambda}$ ，因为每个 $\mathcal U_\lambda$ 都是 $X$ 的开覆盖，所以 $\mathcal U$ 也是开覆盖。任取它的有限子集 $\left\{ U_1,U_2,\cdots,U_n\right\}\subseteq \mathcal U$ ，则分别存在 $\lambda_1,\lambda_2,\cdots,\lambda_n$ ，使得 $U_i\in\mathcal U_{\lambda_i}(i=1,2,\cdots,n)$ 。而每个 $\mathcal U_{\lambda_i}\in\Psi$ ，即 $\left\{ \mathcal U_{\lambda_i}|i=1,2,\cdots,n \right\}\subseteq\Psi$ ，由 $\Psi$ 的全序性可知这 $n$ 个元素中存在最大元。不妨设最大元为 $\mathcal U_{\lambda_1}$ （通过替换下标总能做到这一点），则每个 $U_i\in\mathcal U_{\lambda_i}\subseteq \mathcal U_{\lambda_1}$ 成立，即 $\left\{ U_1,U_2,\cdots,U_n\right\}\subseteq \mathcal U_{\lambda_1}$ 。而 $\mathcal U_{\lambda_1}\in\Psi\subseteq\Phi$ ，由 $\Phi$ 的定义可知开覆盖 $\mathcal U_{\lambda_1}$ 没有有限子覆盖，那么 $\left\{ U_1,U_2,\cdots,U_n\right\}$ 不是开覆盖。于是由 $\left\{ U_1,U_2,\cdots,U_n\right\}$ 的任意性可知 $\mathcal U=\bigcup_{\lambda\in \Lambda} \mathcal U_{\lambda}$ 没有有限子覆盖，因此 $\mathcal U\in\Phi$ 。又 $\mathcal U=\bigcup_{\lambda\in \Lambda} \mathcal U_{\lambda}$ 意味着 $\forall\lambda\in\Lambda,U_\lambda\subseteq\mathcal U\Rightarrow U_\lambda\le\mathcal U$ ，所以 $\mathcal U$ 是全序子集 $\Psi=\left\{ \mathcal U_\lambda|\lambda\in \Lambda \right\}$ 的上界。由 $\Psi$ 的任意性可知非空偏序集 $(\Phi,\le)$ 的任意非空全序子集 $\Psi\subseteq\Phi$ 都存在上界，根据注意16.3， $\Phi$ 存在极大元。

设 $\mathcal V=\left\{ V_\lambda|\lambda\in \Gamma\right\}$ （这里的指标集为 $\Gamma$ ）为 $\Phi$ 的某个极大元，根据极大元的定义可知 $\mathcal V\in\Phi$ ，因此 $\mathcal V$ 为 $X$ 的开覆盖。由于 $\mathcal V\cap\mathcal S\subseteq\mathcal S$ ，如果 $\mathcal V\cap\mathcal S$ 也是 $X$ 的开覆盖，那么根据已知条件， $\mathcal V\cap\mathcal S$ 具有有限子覆盖 $\mathcal V_S$ 。然而 $\mathcal V_S\subseteq\mathcal V\cap\mathcal S\subseteq\mathcal V$ ，这说明 $\mathcal V_S$ 也是 $\mathcal V$ 的有限子覆盖，与 $\mathcal V\in\Phi$ 矛盾，所以 $\mathcal V\cap\mathcal S$ 不是开覆盖。也就是说，设 $\mathcal V\cap\mathcal S=\left\{ V_\lambda|\lambda\in\Gamma' \right\}(\Gamma'\subseteq\Gamma)$ ，那么 $\bigcup_{\lambda\in \Gamma'}V_\lambda\ne X$ ，于是存在点 $x_0\in (\bigcup_{\lambda\in \Gamma'}V_\lambda)^c$ 。而 $\mathcal V$ 是开覆盖，所以存在某个 $\lambda_0\in\Gamma$ ，使得 $x_0\in V_{\lambda_0}$ 。

另一方面，根据子基的定义， $\mathcal{B}_S=\left\{ \bigcap_{i=1}^nS_i|n\in\mathbb N_+,S_i\in\mathcal{S},i=1,2,\cdots,n \right\}$ 为 $X$ 的基。而 $V_{\lambda_0}$ 是开集，所以存在 $B\in\mathcal B_S$ 使得 $x_0\in B\subseteq V_{\lambda_0}$ ，即存在 $N\in\mathbb N_+$ 使得 $x_0\in \bigcap_{i=1}^N S_i\subseteq V_{\lambda_0}$ （这里的每个 $S_i\in\mathcal S$ ）。假设其中某个 $S_i\in\mathcal V$ ，那么 $S_i\in\mathcal V\cap\mathcal S$ ，即存在某个 $\lambda\in \Gamma'$ 使得 $S_i=V_\lambda$ 。于是 $x_0\in S_i=V_{\lambda}\subseteq\bigcup_{\lambda\in \Gamma'}V_\lambda$ ，与 $x_0\in (\bigcup_{\lambda\in \Gamma'}V_\lambda)^c$ 矛盾。这就说明对于任意 $i=1,2,\cdots,N,S_i\notin\mathcal V$ ，从而根据 $\mathcal V$ 的极大性，每个开覆盖 $\mathcal V\cup\left\{ S_i \right\}(i=1,2,\cdots,N)$ 一定具有有限子覆盖 $\mathcal V_i\subseteq\mathcal V\cup\left\{ S_i \right\}$ 。这里稍微解释一下。 $\mathcal V$ 本身为 $X$ 的开覆盖，所以往 $\mathcal V$ 中加入集合 $S_i$ 之后依然是开覆盖。如果 $\mathcal V\cup\left\{ S_i \right\}$ 没有有限子覆盖，那么 $\mathcal V\cup\left\{ S_i \right\}\in \Phi$ ，从而 $\Phi$ 中存在元素 $\mathcal V\cup\left\{ S_i \right\}$ ，使得 $\mathcal V\subset\mathcal V\cup\left\{ S_i \right\}\Rightarrow\mathcal V<\mathcal V\cup\left\{ S_i \right\}$ ，与 $\mathcal V$ 是极大元矛盾。

假设 $S_i\notin\mathcal V_i$ ，那么 $\mathcal V_i$ 中的所有开集都来自 $\mathcal V$ ，即 $\mathcal V$ 具有有限子覆盖 $\mathcal V_i$ ，矛盾，所以 $S_i\in\mathcal V_i$ 。于是有限子覆盖 $\mathcal V_i$ 可以写成 $\left\{ S_i,V^\lambda_{i_1},V^\lambda_{i_2},\cdots,V^\lambda_{i_k} \right\}$ 的形式，下标 $i_k$ 表示对于不同的 $i=1,2,\cdots,N$ ，开集 $V_\lambda$ 的数量 $k$ 会随着 $i$ 的变化而变化。利用关系式 $A\cup B=X\Leftrightarrow A^c\subseteq B$ ，得 $X=S_i\cup V^\lambda_{i_1}\cup V^\lambda_{i_2}\cup\cdots\cup V^\lambda_{i_k}\Rightarrow(V^\lambda_{i_1}\cup V^\lambda_{i_2}\cup\cdots\cup V^\lambda_{i_k})^c\subseteq S_i$ ，所以 $\bigcap_{i=1}^N(V^\lambda_{i_1}\cup V^\lambda_{i_2}\cup\cdots\cup V^\lambda_{i_k})^c\subseteq\bigcap_{i=1}^N S_i\subseteq V_{\lambda_0}$ 。如此，则 $X=[\bigcap_{i=1}^N(V^\lambda_{i_1}\cup V^\lambda_{i_2}\cup\cdots\cup V^\lambda_{i_k})^c]^c\cup V_{\lambda_0}=\bigcup_{i=1}^N(V^\lambda_{i_1}\cup V^\lambda_{i_2}\cup\cdots\cup V^\lambda_{i_k})\cup V_{\lambda_0}$ 。注意到每个 $i$ 所对应的开集 $V_\lambda$ 的数量 $i_k$ 是有限的（即 $V^\lambda_{i_1}\cup V^\lambda_{i_2}\cup\cdots\cup V^\lambda_{i_k}$ 是有限个开集之并），而 $i$ 也是有限的，因此等号右边括号内的开集是有限的（数量为 $1_k+2_k+\cdots+N_k$ ）。这有限个开集再加上 $V_{\lambda_0}$ 之后数量依然有限，并且这些开集全部来自 $\mathcal V$ 。这样就找到了 $\mathcal V$ 的有限子覆盖，矛盾。所以假设不成立， $X$ 是紧空间。

证毕。

在命题9.16中证明了 $X$ 是紧空间的充要条件是由基 $\mathcal B$ 中的开集所构成的任意开覆盖 $\mathcal V\subseteq\mathcal B$ 都具有有限子覆盖，而亚历山大子基定理则是进一步弱化了这个条件，把基改成子基之后依然能得到 $X$ 紧。同时，任何基都可以视为子基，所以亚历山大子基定理也验证了命题9.16的正确性。

下面利用亚历山大子基定理证明吉洪诺夫定理。

### 定理16.5（吉洪诺夫定理）

设 $(X_\lambda)_{\lambda\in\Lambda}$ 为一族紧空间，则积空间 $X=\prod_{\lambda\in\Lambda} X_\lambda$ 也是紧的。

证明：设 $p_\lambda:X\rightarrow X_\lambda$ 为投影映射，根据积拓扑的定义， $\mathcal S=\left\{ p_\lambda^{-1}(U)|U\in\mathcal O_\lambda,\lambda\in \Lambda\right\}\subseteq P(X)$ 为积空间 $X$ 的子基（定义8.10）。对于每个 $\lambda\in\Lambda$ ，如果把 $X_\lambda$ 的开集的原像所构成的集族记作 $\mathcal S_\lambda$ ，则 $\mathcal S=\bigcup_{\lambda\in \Lambda} \mathcal S_\lambda$ 。

设 $\mathcal U\subseteq\mathcal S$ 是由 $\mathcal S$ 中的开集所构成的任意开覆盖。对于每个 $\lambda\in\Lambda$ ，令 $\mathcal U_\lambda=\mathcal U\cap\mathcal S_\lambda$ （也就是 $\mathcal U_\lambda$ 中的开集均为 $X_\lambda$ 中的某些开集的原像），那么 $\mathcal U=\bigcup_{\lambda\in \Lambda} \mathcal U_\lambda$ 。顺便把 $X_\lambda$ 中的这些开集组成的集族记作 $\mathcal V_\lambda$ ，则 $\mathcal U_\lambda=\left\{ p_\lambda^{-1}(V) |V\in\mathcal V_\lambda\subseteq \mathcal O_\lambda\right\}$ 。

假设对于任意 $\lambda\in\Lambda,\mathcal V_\lambda$ 都不是 $X_\lambda$ 的开覆盖，即 $\forall\lambda\in\Lambda,\bigcup_{V\in \mathcal V_\lambda} V\ne X$ ，那么存在点 $x_\lambda\in (\bigcup_{V\in \mathcal V_\lambda} V)^c$ 。记 $x=(x_\lambda)_{\lambda\in\Lambda}$ ，由 $\mathcal U$ 是开覆盖得存在 $U\in \mathcal U$ ，使得 $x\in U$ 。而 $\mathcal U=\bigcup_{\lambda\in \Lambda} \mathcal U_\lambda$ ，所以存在 $\lambda\in\Lambda$ ，使得 $U\in\mathcal U_\lambda$ 。于是 $x\in U=p^{-1}_\lambda(V)\Rightarrow p_\lambda(x)=x_\lambda\in V$ ，和 $x_\lambda\in (\bigcup_{V\in \mathcal V_\lambda} V)^c$ 矛盾。所以假设不成立，存在某个 $\lambda\in\Lambda$ ，使得 $\mathcal V_\lambda$ 是 $X_\lambda$ 的开覆盖。

根据 $X_\lambda$ 的紧性，存在有限个 $V_1,V_2,\cdots,V_n\in V_\lambda$ ，使得 $X_\lambda=\bigcup_{i=1}^n V_i$ 。在 $X_\lambda=\bigcup_{i=1}^n V_i$ 的两边取原像， $X=p_\lambda^{-1}(\bigcup_{i=1}^n V_i)=\bigcup_{i=1}^n p_\lambda^{-1}(V_i)$ 。而每个 $p_\lambda^{-1}(V_i)\in\mathcal U_\lambda\subseteq\mathcal U$ ，这意味着 $\left\{ p_\lambda^{-1}(V_1),p_\lambda^{-1}(V_2),\cdots,p_\lambda^{-1}(V_n) \right\}\subseteq\mathcal U$ 为 $\mathcal U$ 的有限子覆盖。由 $\mathcal U$ 的任意性可知由 $\mathcal S$ 中的开集所构成的任意开覆盖都具有有限子覆盖，根据定理16.4， $X$ 是紧空间。

证毕。

吉洪诺夫定理的证明是通过选择公理的等价命题——佐恩引理来完成的（中间也借助了亚历山大子基定理），实际上吉洪诺夫定理本身也是选择公理的等价命题之一。因为直积 $X=\prod_{\lambda\in\Lambda} X_\lambda$ 中元素 $(x_\lambda)_{\lambda\in\Lambda}$ 的各个分量 $x_\lambda$ 分别来自每个 $X_\lambda$ ，换句话说， $(x_\lambda)_{\lambda\in\Lambda}$ 可以看成是从每个 $X_\lambda$ 中选择一个元素 $x_\lambda$ 之后，把它们组合在一起写成 $(x_\lambda)_{\lambda\in\Lambda}$ 。这个步骤需要选择公理，即 $(x_\lambda)_{\lambda\in\Lambda}$ 的存在性需要选择公理来保证，所以如果能证明 $X\ne\emptyset$ ，那就说明选择公理成立。

### 命题16.6（吉洪诺夫定理与选择公理的等价性）

以下命题等价：

1.  选择公理；
2.  吉洪诺夫定理。

证明： $1\Rightarrow2$ 见定理16.5，只证 $2\Rightarrow1$ 。

设 $(X_\lambda)_{\lambda\in\Lambda}$ 为一族非空集合，根据上面的提示可知只要证 $\prod_{\lambda\in\Lambda} X_\lambda\ne\emptyset$ 。事先说明，选择公理是集合论的内容之一，它不依赖于拓扑的有无，所以每个 $X_\lambda$ 上并未定义拓扑。

任取一点 $\infty\notin\bigcup_{\lambda\in\Lambda} X_\lambda$ （ $\infty$ 的存在性由注意9.25保证），并定义 $Y_\lambda=X_\lambda\cup\left\{\infty \right\}$ 。为了使用吉洪诺夫定理，需要定义每个 $Y_\lambda$ 上的拓扑使其成为拓扑空间。对每个 $\lambda\in\Lambda$ ，定义集族 $\mathcal F_\lambda=\left\{ F\subseteq Y_\lambda|F为有限集或F=X_\lambda,Y_\lambda \right\}$ ，易证它满足条件 $C1\sim C3$ 。于是由注意1.5可知，以 $\mathcal F_\lambda$ 为 $Y_\lambda$ 的闭集族定义了 $Y_\lambda$ 上的拓扑。此时 $X_\lambda$ 作为子空间是有限补空间（例1.8），根据例9.5可知 $X_\lambda\subset Y_\lambda$ 为紧集。而 $\left\{ \infty \right\}\subset Y_\lambda$ 也是紧的，根据命题9.8， $Y_\lambda=X_\lambda\cup\left\{ \infty\right\}$ 为紧空间。再根据吉洪诺夫定理， $Y=\prod_{\lambda\in\Lambda} Y_\lambda$ 是紧的。

设 $p_\lambda:Y\rightarrow Y_\lambda$ 为投影映射，根据积拓扑的定义， $p_\lambda$ 连续，所以 $p_\lambda^{-1}(X_\lambda)\subset Y$ 为闭集。记 $F_\lambda=p^{-1}_\lambda(X_\lambda)$ ，得到 $Y$ 中的闭集族 $\left\{F_\lambda|\lambda\in\Lambda \right\}$ 。任取其中有限个闭集 $F_{\lambda_1},F_{\lambda_2},\cdots,F_{\lambda_n}$ ，因为每个 $X_{\lambda_i}\ne\emptyset,i=1,2,\cdots,n$ ，所以能取得 $x_{\lambda_i}\in X_{\lambda_i}$ （注意这里是有限个集合，因此从每个集合中选择一个元素的行为无需使用选择公理）。于是 $Y$ 中存在元素 $y=(y_\lambda)_{\lambda\in\Lambda}$ ，它的第 $\lambda_i$ 分量为 $x_{\lambda_i}$ ，其余分量均为 $\infty$ （因为 $y$ 能具体构造出来，所以它的存在性也无需选择公理来保证）。即对于每个 $i=1,2,\cdots,n,p_{\lambda_i}(y)=x_{\lambda_i}\in X_{\lambda_i}$ ，从而 $y\in\bigcap_{i=1}^n p_{\lambda_i}^{-1}(X_{\lambda_i})=\bigcap_{i=1}^n F_{\lambda_i}\ne\emptyset$ 。由 $F_{\lambda_1},F_{\lambda_2},\cdots,F_{\lambda_n}$ 的任意性得到 $\left\{F_\lambda|\lambda\in\Lambda \right\}$ 为有限交的闭集族，根据命题9.12， $\bigcap_{\lambda\in\Lambda} F_\lambda=\bigcap_{\lambda\in\Lambda}p_\lambda^{-1}(X_\lambda)=\prod_{\lambda\in\Lambda} X_\lambda\ne\emptyset$ 。

证毕。

## 后记

下一章已更新：[sumeragi693：拓扑学入门17——滤子](https://zhuanlan.zhihu.com/p/558332980)