---
id: "1897509798750184075"
title: "P-空间"
author: "sumeragi693"
type: zhihu-article
source: "https://zhuanlan.zhihu.com/p/1897509798750184075"
created: "2025-05-11 14:12"
updated: "2025-05-12 14:13"
downloaded: "2026-04-20"
---
本文介绍P-空间的概念和性质。

## 1.P-空间的定义

众所周知，拓扑空间中一列开集之交不一定仍是开集。例如数轴上的一列开集 $\left\{ (-\frac{1}{n},\frac{1}{n}) |n\in\mathbb N_+\right\}$ ，它们的交集为单点集 $\left\{ 0 \right\}$ ，不再是开集。如果拓扑空间中任意一列开集之交，即任意 $G_\delta$ 型集仍是开集，这样的空间就称为P-空间。由德摩根定律，P-空间也可以定义为任意 $F_\sigma$ 型集仍是闭集的空间。

事先提醒，在某些文献中，P-空间的定义要求满足 $T_1$ 分离公理，本文不采用。

## 2.P-空间的特征

有时我们需要从邻域的角度研究拓扑空间，所以先考虑如何通过邻域来定义P-空间。下面的定理1表示，在P-空间中邻域对可数交运算封闭。

### 定理1（利用邻域定义P-空间）

设 $X$ 为拓扑空间，以下命题等价：

1.  $X$ 为P-空间；
2.  对于任意 $x\in X$ 和它的任意一列邻域 $\left\{ U_n|n\in\mathbb N_+ \right\}$ ，有 $\bigcap_{n=1}^\infty U_n$ 仍是 $x$ 的邻域。

证明： $1\Rightarrow2$ 。根据邻域的定义，对于每个 $n\in\mathbb N_+$ ，存在开集 $V_n\subseteq X$ ，使得 $x\in V_n\subseteq U_n$ ，所以 $x\in\bigcap_{n=1}^\infty V_n\subseteq \bigcap_{n=1}^\infty U_n$ 。而因为 $X$ 为P-空间，所以 $\bigcap_{n=1}^\infty V_n$ 为开集，于是 $\bigcap_{n=1}^\infty U_n$ 为 $x$ 的邻域。

$2\Rightarrow1$ 。任取一列开集 $\left\{ U_n|n\in\mathbb N_+ \right\}$ ，记 $U=\bigcap_{n=1}^\infty U_n$ ，则只要证明 $U$ 为开集，即证明 $U\subseteq U^\circ$ 。任取 $x\in U$ ，则 $\forall n\in\mathbb N_+,x\in U_n$ ，于是 $\left\{ U_n|n\in\mathbb N_+ \right\}$ 为 $x$ 的一列开邻域。根据条件2， $U$ 仍是 $x$ 的邻域，因此 $x\in U^\circ$ 。由 $x$ 的任意性得 $U\subseteq U^\circ$ 。

证毕。

## 3.P-空间的例子

由定义，任意离散空间或平凡空间都是P-空间。另外，由于开集对有限交运算封闭，所以当拓扑空间中的开集数量有限时，它也为P-空间。

又设 $X$ 为无限集，赋予特殊点拓扑，特殊点为 $p$ 。任取一列开集 $\left\{ U_n|n\in\mathbb N_+ \right\}$ ，如果其中含有空集，则 $\bigcap_{n=1}^\infty U_n=\emptyset$ 是开集。如果其中不含空集，则 $\forall n\in\mathbb N_+,p\in U_n\Rightarrow p\in \bigcap_{n=1}^\infty U_n\Rightarrow\bigcap_{n=1}^\infty U_n$ 是开集。因此 $X$ 为P-空间。又因为单点集 $\left\{ p \right\}$ 不是闭集，所以 $X$ 不是 $T_1$ 空间。

## 4.P-空间的构造

下面从已知的P-空间出发来构造新的P-空间。

### 定理2（P-空间的子空间）

设 $X$ 为P-空间， $A\subseteq X$ ，则子空间 $A$ 也是P-空间。

证明：任取子空间 $A$ 中一列开集 $\left\{ U_n|n\in\mathbb N_+ \right\}$ ，则对于每个 $n\in\mathbb N_+$ ，根据相对拓扑的定义，存在开集 $V_n\subseteq X$ ，使得 $U_n=A\cap V_n$ 。于是 $\bigcap_{n=1}^\infty U_n=\bigcap_{n=1}^\infty (A\cap V_n)=A\cap \bigcap_{n=1}^\infty V_n$ 。而 $X$ 是P-空间，所以 $\bigcap_{n=1}^\infty V_n$ 是 $X$ 的开集，那么 $\bigcap_{n=1}^\infty U_n=A\cap \bigcap_{n=1}^\infty V_n$ 是子空间 $A$ 的开集，从而 $A$ 是P-空间。

证毕。

仿照定理2的证明，还可以证明定理3和定理4。

### 定理3（P-空间的和空间）

设 $\left\{ X_\lambda|\lambda\in\Lambda \right\}$ 为一族P-空间，则直和 $X=\coprod_{\lambda\in \Lambda} X_\lambda$ 也是P-空间。

证明：记 $i_\lambda:X_\lambda\rightarrow  X$ 为包含映射。任取 $X$ 中一列开集 $\left\{ U_n|n\in\mathbb N_+ \right\}$ ，则对于每个 $n\in\mathbb N_+$ ，根据和拓扑的定义， $\forall\lambda\in\Lambda,i_\lambda^{-1}(U_n)\subseteq X_\lambda$ 都是开集。记 $U=\bigcap_{n=1}^\infty U$ ，则 $i_\lambda^{-1}(U)=i_\lambda^{-1}(\bigcap_{n=1}^\infty U_n)=\bigcap_{n=1}^\infty i_\lambda^{-1}(U_n)$ 。由 $X_\lambda$ 为P-空间可知 $i_\lambda^{-1}(U)$ 是开集，再由 $\lambda$ 的任意性和和拓扑的定义可知 $U$ 是 $X$ 的开集，所以 $X$ 为P-空间。

证毕。

### 定理4（P-空间的商空间）

设 $X$ 为拓扑空间， $\tilde X$ 为它的商集，则商空间 $\tilde X$ 也是P-空间。

证明：记 $p:X\rightarrow \tilde X$ 为自然映射。任取 $\tilde X$ 中一列开集 $\left\{ U_n|n\in\mathbb N_+ \right\}$ ，则对于每个 $n\in\mathbb N_+$ ，根据商拓扑的定义， $p^{-1}(U_n)$ 是 $X$ 的开集。记 $U=\bigcap_{n=1}^\infty U$ ，则 $p^{-1}(U)=p^{-1}(\bigcap_{n=1}^\infty U_n)=\bigcap_{n=1}^\infty p^{-1}(U_n)$ 。由 $X$ 为P-空间可知 $p^{-1}(U)$ 是开集，再由商拓扑的定义可知 $U$ 是 $\tilde X$ 的开集，所以 $\tilde X$ 为P-空间。

证毕。

由于积拓扑的特殊性（无限个开集的直积不一定是开集），P-空间只对有限个直积封闭。

### 定理5（有限个P-空间的积空间）

设 $X,Y$ 为P-空间，则直积 $X\times Y$ 也是P-空间。

证明：任取 $X\times Y$ 中一列开集 $\left\{ U_n|n\in\mathbb N_+ \right\}$ ，记 $U=\bigcap_{n=1}^\infty U$ 。对于任意 $(x,y)\in U$ 和 $n\in\mathbb N_+$ ，有 $(x,y)\in U_n$ 。根据积拓扑的定义，存在开集 $V_n \subseteq X,W_n\subseteq Y$ ，使得 $(x,y)\in V_n\times W_n\subseteq U_n$ ，那么 $(x,y)\in \bigcap_{n=1}^\infty(V_n\times W_n)=(\bigcap_{n=1}^\infty V_n)\times(\bigcap_{n=1}^\infty W_n)\subseteq U$ 。而因为 $X,Y$ 都是P-空间，所以 $\bigcap_{n=1}^\infty V_n,\bigcap_{n=1}^\infty W_n$ 分别为 $X,Y$ 的开集。同时， $\forall n\in\mathbb N_+,(x,y)\in V_n\times W_n\Rightarrow x\in\bigcap_{n=1}^\infty V_n,y\in\bigcap_{n=1}^\infty W_n$ ，所以 $\bigcap_{n=1}^\infty V_n,\bigcap_{n=1}^\infty W_n$ 分别为 $x,y$ 的开邻域。由 $(x,y)$ 的任意性和积拓扑的性质得 $U$ 为开集，所以 $X\times Y$ 为P-空间。

证毕。

### 例6（无限个P-空间的直积不再是P-空间的例子）

作为定理5的补充，现在来举例说明P-空间不是任意可乘的。对每个 $n\in\mathbb N_+$ ，定义 $X_n=\left\{ 0,1 \right\}$ 为离散空间，并令 $X=\prod_{n=1}^{\infty}X_n$ 。因为每个 $X_n$ 都可距离化，所以 $X$ 也可距离化，那么 $X$ 为完全正规空间。根据完全正规空间的性质，任意闭集都是 $G_\delta$ 型集。特别地，单点集 $\left\{ (0,0,\cdots) \right\}$ 也是 $G_{\delta}$ 型集。另一方面，定义集族 $\mathcal B=\left\{ B\subseteq X|B=\prod_{n=1}^{\infty} U_n，其中每个U_n都是X_n的开集，并且除了有限个U_n之外，其余所有U_n=X_n\right\}$ 。根据积拓扑的定义， $\mathcal B$ 为 $X$ 的基。显然，单点集 $\left\{ (0,0,\cdots) \right\}$ 无法包含任何 $B\in\mathcal B$ ，因此它不是开集，那么 $X$ 不是P-空间。

## 5.P-空间与分离公理

这一部分主要介绍P-空间搭配不同的分离公理后能获得的一些结论。事先声明，本文的 $T_i,i\ge 3$ 分离公理不要求 $T_1$ 。

### 定理7（ $T_1$ 的P-空间的可数子空间）

设 $X$ 为 $T_1$ 的P-空间， $A\subseteq X$ 为至多可数集，则 $A$ 为离散空间。

证明：因为 $T_1$ 分离公理可遗传，所以 $A$ 中任意单点集都是 $A$ 的闭集。对于任意 $B\subseteq A$ ，因为 $B$ 也是至多可数集，所以可以写成 $B=\left\{ x_1,x_2,x_3,\cdots \right\}=\bigcup_{n=1}^\infty\left\{ x_n \right\}$ 的形式，即 $B$ 为 $F_\sigma$ 型集。由定理2得 $A$ 为P-空间，所以 $B$ 是 $A$ 的闭集。由 $B$ 的任意性可知 $A$ 中任意子集都是闭集，所以 $A$ 是离散空间。

证毕。

### 定理8（ $T_3$ 的P-空间零维）

设 $X$ 为 $T_3$ 的P-空间，则 $X$ 是零维空间。

证明：定义集族 $\mathcal B=\left\{ B\subseteq X|B是开闭集 \right\}$ 。任取开集 $U \subseteq X$ 和 $x\in U$ ，由 $T_3$ 空间的性质可知存在 $x$ 的开邻域 $U_1$ ，使得 $\bar U_1\subseteq U$ 。同理，存在 $x$ 的开邻域 $U_2$ ，使得 $\bar U_2\subseteq U_1$ 。以此类推，得到一列 $x$ 的开邻域 $\left\{ U_n|n\in\mathbb N_+ \right\}$ ，满足 $U_{n+1}\subseteq \bar U_{n+1}\subseteq U_n$ ，那么 $\bigcap_{n=1}^\infty U_{n+1}\subseteq\bigcap_{n=1}^\infty \bar U_{n+1}\subseteq\bigcap_{n=1}^\infty U_n$ 。由 $\left\{ U_n|n\in\mathbb N_+ \right\}$ 是递降列可知 $\bigcap_{n=1}^\infty U_{n+1}=U_2\cap U_3\cap\cdots=U_1\cap U_2\cap\cdots=\bigcap_{n=1}^\infty U_{n}$ ，所以 $\bigcap_{n=1}^\infty \bar U_{n+1}=\bigcap_{n=1}^\infty U_n\Rightarrow\bigcap_{n=1}^\infty U_n$ 是闭集。又因为 $X$ 为P-空间，所以 $\bigcap_{n=1}^\infty U_n$ 是开集，那么集合 $\bigcap_{n=1}^\infty U_n\in\mathcal B$ 。于是集族 $\mathcal B$ 满足基的定义，所以 $X$ 是零维空间。

证毕。

### 系9（ $T_3$ 的P-空间中，点和闭集能用函数分离）

设 $X$ 为 $T_3$ 的P-空间， $x\in X,F\subseteq X$ 为闭集。如果 $x\notin F$ ，那么存在连续函数 $f:X\rightarrow[0,1]$ ，使得 $f(x)=0,f(F)=\left\{1\right\}$ 。

证明：当 $x\notin F$ 时， $F^c$ 为 $x$ 的开邻域。根据定理8，存在开闭集 $U \subseteq X$ ，使得 $x\in U\subseteq F^c$ 。定义 $f:X\rightarrow[0,1],f(t)=\left\{\begin{matrix} 0,t\in U \\ 1,t\notin U \end{matrix}\right.$ ，那么 $f(x)=0,f(F)=\left\{ 1 \right\}$ 。对于任意开集 $V\subseteq [0,1],f^{-1}(V)$ 必为 $\emptyset,X,U,U^c$ 之一，它们都是开集，所以 $f$ 连续。

证毕。

任意两点都能用函数分离的空间称为完全豪斯多夫空间，任意两点都能用开闭集分离的空间称为完全分离空间。

### 定理10（完全豪斯多夫的P-空间完全分离）

设 $X$ 为完全豪斯多夫的P-空间，则对于任意 $x,y\in X$ ，当 $x\ne y$ 时，存在开闭集 $A\subseteq X$ ，使得 $x\in A,y\notin A$ 。

证明：任取 $x,y\in X,x\ne y$ ，因为 $X$ 为完全豪斯多夫空间，所以存在连续函数 $f:X\rightarrow[0,1]$ ，使得 $f(x)=0,f(y)=1$ 。因为 $f^{-1}(\left\{ 0 \right\})=f^{-1}(\bigcap_{n=1}^\infty[0,\frac{1}{n}))=\bigcap_{n=1}^\infty f^{-1}([0,\frac{1}{n}))$ ，由 $f$ 的连续性得等号右边是 $X$ 中一列开集之交，所以 $f^{-1}(\left\{ 0 \right\})$ 是开集。同时， $f^{-1}(\left\{ 0 \right\})=f^{-1}(\bigcap_{n=1}^\infty[0,\frac{1}{n}])=\bigcap_{n=1}^\infty f^{-1}([0,\frac{1}{n}])$ ，那么 $f^{-1}(\left\{ 0 \right\})$ 还是闭集。令 $f^{-1}(\left\{ 0 \right\})=A$ ，则有 $x\in A,y\notin A$ 成立。

证毕。

任意开集的闭包仍是开集的空间称为极端不连通空间。

### 定理11（ $T_6$ 的P-空间极端不连通）

设 $X$ 为 $T_6$ 的P-空间， $U\subseteq X$ 为开集，则 $\bar U$ 也是开集（开闭集）。

证明：由 $T_6$ 分离公理的性质， $X$ 中任意闭集都是 $G_\delta$ 型集，所以 $\bar U$ 是 $G_\delta$ 型集。而 $X$ 是P-空间，所以 $\bar U$ 也是开集。

证毕。

### 例12（极端不连通但连通的空间）

需要注意的是当拓扑空间 $X$ 极端不连通时，它仍可能连通。例如3中所举特殊点空间的例子，对于任意非空真子集 $A\subseteq X$ ，要么特殊点 $p\in A$ ，要么 $p\notin A$ 。根据特殊点拓扑的定义，要么 $A$ 为开集，要么 $A$ 为闭集，即 $A$ 不可能是开闭集，所以 $X$ 连通。然而，对于任意开集 $U\subseteq X$ ，当 $U=\emptyset$ 时， $\bar U=\emptyset$ 是开闭集；当 $U\ne\emptyset$ 时， $\bar U= X$ 也是开闭集，所以 $X$ 极端不连通。

## 6.P-空间与连通性

实际上定理10和定理11已经暗示了P-空间与连通性的关系，只有当P-空间的分离性比较差时，它才可能连通。

### 定理13（P-空间连通的充要条件）

设 $X$ 为P-空间，则 $X$ 连通的充要条件是定义在 $X$ 上的任意连续实值函数都是常数函数。

证明：必要性。假设存在某个连续函数 $f:X\rightarrow\mathbb R$ 不是常数函数，那么存在 $x,y\in X,x\ne y$ ，使得 $f(x)\ne f(y)$ 。对每个 $n\in\mathbb N_+$ ，定义开球 $U_n=B(f(x),\frac{1}{n})$ ，则 $\left\{ f(x) \right\}=\bigcap_{n=1}^\infty B_n$ 。两边取原像，得 $A=\left\{ t\in X|f(t)=f(x) \right\}=\bigcap_{n=1}^\infty f^{-1}(B_n)$ 。由 $f$ 的连续性得等号右边是 $X$ 中一列开集之交，所以 $A$ 是开集。同时， $\left\{ f(x) \right\}=\bigcap_{n=1}^\infty \bar B_n$ ，那么 $A$ 还是闭集。又因为 $x\in A,y\notin A$ ，所以 $A\subseteq X$ 是既开又闭的非空真子集，那么 $X$ 不连通，与已知矛盾。

充分性。假设 $X$ 不连通，则存在连续函数 $f:X\rightarrow\left\{ 0,1 \right\}$ （赋予离散拓扑）和 $x,y\in X,x\ne y$ ，使得 $f(x)=0,f(y)=1$ 。又记 $i:\left\{ 0,1 \right\}\rightarrow \mathbb R$ 为包含映射，则复合映射 $i\circ f:X\rightarrow\mathbb R$ 也是连续函数，并且满足 $i\circ f(x)=i(0)=0,i\circ f(y)=i(1)=1$ ，与已知矛盾。

证毕。

## 7.P-空间与紧性

在各种紧性的加成下（必要时搭配一些分离公理），P-空间将表现出一些有趣的性质。

### 定理14（ $T_1$ 且聚点紧的P-空间是有限集）

设 $X$ 为 $T_1$ 的P-空间，如果 $X$ 聚点紧（特别地，紧、列紧、可数紧），那么 $X$ 为有限集。

证明：假设 $X$ 为无限集，那么存在 $X$ 的可数子集 $A=\left\{ x_1,x_2,\cdots \right\}=\bigcup_{n=1}^\infty \left\{ x_n \right\}$ 。由 $X$ 是 $T_1$ 空间得每个 $\left\{ x_n \right\}$ 都是闭集，所以 $A$ 是 $F_\sigma$ 型集；再由 $X$ 为P-空间得 $A$ 为闭集，因此 $A'\subseteq A$ 。又因为 $X$ 聚点紧， $A$ 为无限集，所以存在 $x\in A'\subseteq A$ 。然而，根据定理7， $A$ 作为子空间是离散空间，即 $\left\{ x \right\}$ 是子空间 $A$ 的开集。所以 $x$ 是 $A\subseteq X$ 的孤立点，与 $x\in A'$ 矛盾。所以假设不成立， $X$ 为有限集。

证毕。

结合定理7和定理14就得到下面的系15。

### 系15（ $T_1$ 且聚点紧的P-空间是离散空间）

除了聚点紧的条件外，附加局部紧的条件也可以得到P-空间为离散空间。

### 定理16（ $T_1$ 且局部紧的P-空间是离散空间）

设 $X$ 为 $T_1$ 的P-空间，如果 $X$ 局部紧，那么 $X$ 为离散空间。

证明：只要证任意单点集为开集。任取 $\left\{ x \right\}\subseteq X$ ，由 $X$ 局部紧可知存在某个紧集 $K\subseteq X$ 是 $x$ 的邻域。根据定理2和 $T_1$ 分离公理的可遗传性， $K$ 作为子空间是 $T_1$ 的P-空间；再根据系15， $K$ 为离散空间，所以 $\left\{ x \right\}$ 是子空间 $K$ 的开集。于是存在开集 $U\subseteq X$ ，使得 $K\cap U=\left\{ x \right\}$ 。而根据定理1， $\left\{ x \right\}$ 也是 $x$ 的邻域，所以 $\left\{ x \right\}$ 是开集。

证毕。

由于在任意无限集上定义离散拓扑之后都满足它是 $T_1$ 且局部紧的P-空间，所以仅通过局部紧的条件无法得到像定理14那样强的结论。

接下来看看P-空间与林德洛夫性质的配合。在紧空间中，任意开覆盖都有有限子覆盖，这有限个开集之交为开集；在林德洛夫的P-空间中，任意开覆盖都有至多可数的子覆盖，这至多可数个开集之交也是开集。所以P-空间搭配上林德洛夫性质之后，可以得到许多类似紧空间中的结论。以下列举几个命题，并给出相应的证明。

### 定理17（豪斯多夫的P-空间中，林德洛夫子集是闭集）

设 $X$ 为豪斯多夫的P-空间， $A\subseteq X$ 作为子空间是林德洛夫空间，则 $A$ 是 $X$ 的闭集。

※类比豪斯多夫空间中紧集是闭集。

证明：只要证 $A^c$ 为开集。任取 $x\in A^c$ 并固定，对于每个 $y\in A$ ，由 $X$ 为豪斯多夫空间得分别存在 $x,y$ 的不相交的开邻域 $U_y,V_y$ （下标 $y$ 表示固定 $x$ 之后，随着 $y\in A$ 的变化，相应的开集也在变化）。当 $y$ 取遍 $A$ 中每一点时，集族 $\left\{ V_y|y\in A \right\}$ 构成了 $A$ 在 $X$ 中的开覆盖。于是它具有至多可数的子覆盖，记作 $\left\{  V_{y_n} |y_n\in A\right\}$ 。又令 $U=\bigcap_{n=1}^\infty U_{y_n}$ ，由 $X$ 为P-空间可知 $U$ 是 $x$ 的开邻域。假设 $U\cap A\ne\emptyset$ ，取 $a\in U\cap A$ ，由 $\left\{  V_{y_n} |y_n\in A\right\}$ 是开覆盖得存在某个 $y_i\in A$ ，使得 $a\in V_{y_i}$ 。然而， $a\in U\subseteq U_{y_i}\Rightarrow  U_{y_i}\cap V_{y_i}\ne\emptyset$ ，与 $U_y,V_y$ 不相交矛盾。所以假设不成立， $U\cap A=\emptyset\Leftrightarrow U\subseteq A^c$ ，那么 $x$ 是 $A^c$ 的内点。由 $x$ 的任意性可知 $A^c$ 是开集。

证毕。

### 系18（林德洛夫空间到豪斯多夫的P-空间的连续映射为闭映射）

设 $X$ 为林德洛夫空间， $Y$ 为豪斯多夫空间， $f:X\rightarrow Y$ 连续。如果 $Y$ 为P-空间，那么 $f$ 为闭映射。

※类比紧空间到豪斯多夫空间的连续映射为闭映射。

证明：任取闭集 $F\subseteq X$ ，由定理17得只要证 $f(F)\subseteq Y$ 作为子空间是林德洛夫空间。因为林德洛夫空间中的闭子集也是林德洛夫的，即 $F$ 作为 $X$ 的子空间是林德洛夫空间；并且林德洛夫空间的连续像也是林德洛夫空间，所以 $f(F)$ 为林德洛夫空间得证。

证毕。

### 定理19（豪斯多夫的P-空间中，林德洛夫子集能用开集分离）

设 $X$ 为豪斯多夫的P-空间， $F,H\subseteq  X$ 为林德洛夫子集， $F\cap H=\emptyset$ 。此时存在开集 $U,V\subseteq X$ ，使得 $F\subseteq U,H\subseteq V$ ，并且 $U\cap V=\emptyset$ 。

※类比豪斯多夫空间中的紧集能用开集分离。

证明：首先证明 $F$ 为单点集的场合。设 $F=\left\{ x \right\}$ ，对于每个 $y\in H$ ，由 $X$ 为豪斯多夫空间得分别存在 $x,y$ 的不相交的开邻域 $U_y,V_y$ （下标 $y$ 表示固定 $x$ 之后，随着 $y\in H$ 的变化，相应的开集也在变化）。当 $y$ 取遍 $H$ 中每一点时，集族 $\left\{ V_y|y\in H \right\}$ 构成了 $H$ 在 $X$ 中的开覆盖。于是它具有至多可数的子覆盖，记作 $\left\{  V_{y_n} |y_n\in H\right\}$ ，即 $H\subseteq\bigcup_{n=1}^\infty V_{y_n}$ 。又令 $U=\bigcap_{n=1}^\infty U_{y_n},V=\bigcup_{n=1}^\infty V_{y_n}$ ，由 $X$ 为P-空间可知 $U$ 是 $x$ 的开邻域，且 $V$ 是开集。假设 $U\cap V\ne\emptyset$ ，取 $a\in U\cap V$ ，由 $V$ 的定义得存在某个 $y_i\in H$ ，使得 $a\in V_{y_i}$ 。然而， $a\in U\subseteq U_{y_i}\Rightarrow  U_{y_i}\cap V_{y_i}\ne\emptyset$ ，与 $U_y,V_y$ 不相交矛盾。所以假设不成立， $U\cap V=\emptyset$ 。

其次证明一般场合。对每个 $x\in F$ 都按照以上步骤得到两个开集 $U,V$ ，实际上 $U,V$ 也会随着 $x$ 的变化而变化，不妨记作 $U_x,V_x$ 。当 $x$ 取遍 $F$ 中每一点时，集族 $\left\{ U_x|x\in F \right\}$ 构成了 $F$ 在 $X$ 中的开覆盖。于是它具有至多可数的子覆盖，记作 $\left\{  U_{x_n} |x_n\in F\right\}$ ，即 $F\subseteq\bigcup_{n=1}^\infty U_{x_n}$ 。又令 $U'=\bigcup_{n=1}^\infty U_{x_n},V'=\bigcap_{n=1}^\infty V_{x_n}$ ，由 $X$ 为P-空间可知 $U',V'$ 都是开集。注意到每个 $V_{x_n}\supseteq H$ ，所以 $V'\supseteq H$ 。假设 $U'\cap V'\ne\emptyset$ ，取 $b\in U'\cap V'$ ，由 $U'$ 的定义得存在某个 $x_i\in F$ ，使得 $b\in U_{x_i}$ 。然而， $b\in V\subseteq V_{x_i}\Rightarrow  U_{x_i}\cap V_{x_i}\ne\emptyset$ ，与 $U_x,V_x$ 不相交矛盾。所以假设不成立， $U'\cap V'=\emptyset$ 。

证毕。

### 系20（豪斯多夫且林德洛夫的P-空间正规）

设 $X$ 为豪斯多夫且林德洛夫的P-空间，则 $X$ 为正规空间。

※类比紧豪斯多夫空间是正规空间。

证明：因为 $X$ 为豪斯多夫空间，所以为 $T_1$ 空间。任取闭集 $F,H\subseteq X$ 使得 $F\cap H=\emptyset$ ，则因为 $X$ 为林德洛夫空间，所以 $F,H$ 为林德洛夫子集。根据定理19，存在开集 $U,V\subseteq X$ ，使得 $F\subseteq U,H\subseteq V$ ，并且 $U\cap V=\emptyset$ 。这就是正规空间的定义。

证毕。

为了给出P-空间的另一条等价叙述，需要以下引理。拓扑空间 $X$ 的一族子集 $\mathcal F$ 称为局部有限的，如果对于任意 $x\in X$ ，总是存在它的邻域 $U$ ，使得 $U$ 仅和 $\mathcal F$ 中的有限个集合相交。

### 引理21（局部有限的闭集族之并仍是闭集）

设 $X$ 为拓扑空间， $\mathcal F=\left\{ F_\lambda|\lambda\in\Lambda \right\}$ 为一族局部有限的闭集，则 $\bigcup_{\lambda\in\Lambda}F_\lambda$ 为闭集。

证明：记 $F=\bigcup_{\lambda\in\Lambda} F_\lambda$ ，则只要证 $F^c$ 为开集。任取 $x\in F^c$ ，则存在 $x$ 的某个邻域 $U$ ，使得 $U$ 仅和 $\left\{ F_\lambda|\lambda\in\Lambda \right\}$ 中有限个集合相交，记作 $F_1,F_2,\cdots,F_n$ 。设集族 $\left\{ F_\lambda|\lambda\in\Lambda \right\}$ 去掉这有限个闭集之后剩余集合之并为 $H$ ，则 $U\cap H=\emptyset$ 。对每个 $i=1,2,\cdots,n$ ，由于 $x\in F^c=(\bigcup_{\lambda\in\Lambda} F_\lambda)^c=\bigcap_{\lambda\in \Lambda} F_\lambda^c\Rightarrow x\in F_{i}^c$ ，且 $F_{i}^c$ 是开集，因此存在 $x$ 的邻域 $U_i$ ，使得 $x\in U_i\subseteq F^c_{i}\Rightarrow U_i\cap F_i=\emptyset$ 。记 $V_i=U\cap U_i$ ，则 $V_i$ 也是 $x$ 的邻域。对每个 $i=1,2,\cdots,n$ 找到相应的邻域 $V_i$ 后，则 $V=\bigcap_{i=1}^n V_i=\bigcap_{i=1}^n(U\cap U_i)\subseteq U$ 也是 $x$ 的邻域，并且 $V\subseteq U\Rightarrow  V\cap H=\emptyset$ 。同时，每个 $U_i\cap F_i=\emptyset$ 也意味着 $V\cap \bigcup_{i=1}^n F_i=\emptyset$ 。而 $F=H\cup \bigcup_{i=1}^n F_i$ ，这说明 $V\cap F=\emptyset\Rightarrow x\in V\subseteq F^c$ ，所以 $x$ 是 $F^c$ 的内点。由 $x$ 的任意性可知 $F^c$ 是开集。

证毕。

### 定理22（利用闭映射描述P-空间）

设 $X$ 为拓扑空间，则 $X$ 为P-空间的充要条件是：对于任意林德洛夫空间 $Y$ ，投影映射 $p:X\times Y\rightarrow X$ 为闭映射。

※类比利用闭映射描述紧空间，即 $Y$ 为紧空间的充要条件是对于任意拓扑空间 $X$ ，投影映射 $p:X\times Y\rightarrow X$ 为闭映射。

证明：必要性。设 $F\subseteq X\times Y$ 为任意闭集，则只要证 $[p(F)]^c\subseteq X$ 为开集。任取 $x\in [p(F)]^c$ 并固定，根据投影映射的定义， $\forall y\in Y,(x,y)\notin F$ ，即 $F^c$ 是 $(x,y)$ 的开邻域。所以存在开集 $U_y\subseteq X,V_y\subseteq Y$ ，使得 $(x,y)\in U_y\times V_y\subseteq F^c$ （下标 $y$ 表示固定 $x$ 之后，随着 $y\in Y$ 的变化，相应的开集也在变化）。当 $y$ 取遍 $Y$ 中每一点时，集族 $\left\{ U_y\times V_y|y\in Y \right\}$ 构成了 $\left\{ x \right\}\times Y$ 在 $X\times Y$ 中的开覆盖。由于 $\left\{ x \right\}\times Y\cong Y$ ，而 $Y$ 是林德洛夫空间，所以 $\left\{ x \right\}\times Y$ 作为 $X\times Y$ 的子空间也是林德洛夫空间。于是它具有至多可数的子覆盖，记作 $\left\{ U_{y_n}\times V_{y_n} |y_n\in Y\right\}$ 。又令 $U=\bigcap_{n=1}^\infty U_{y_n}$ ，由 $X$ 为P-空间可知 $U$ 是 $x$ 的开邻域。假设 $U\cap p(F)\ne\emptyset$ ，取 $a\in U\cap p(F)$ ，则存在 $b\in Y$ ，使得 $(a,b)\in F$ 。考虑点 $(x,b)\in \left\{ x \right\}\times Y$ ，由 $\left\{ U_{y_n}\times V_{y_n} |y_n\in Y\right\}$ 是开覆盖得存在某个 $y_i\in Y$ ，使得 $(x,b)\in U_{y_i}\times V_{y_i}\subseteq F^c$ ，那么 $b\in V_{y_i}$ 。然而， $a\in U\subseteq U_{y_i}\Rightarrow (a,b)\in U_{y_i}\times V_{y_i}\subseteq F^c$ ，与 $(a,b)\in F$ 矛盾。所以假设不成立， $U\cap p(F)=\emptyset\Leftrightarrow U\subseteq [p(F)]^c$ ，那么 $x$ 是 $[p(F)]^c$ 的内点。由 $x$ 的任意性可知 $[p(F)]^c$ 是开集。

充分性。不妨证明它的逆否命题，即如果 $X$ 不是P-空间，那么存在某个林德洛夫空间 $Y$ ，使得投影映射 $p:X\times Y\rightarrow X$ 不是闭映射。取 $Y=\mathbb R$ ，它是林德洛夫空间。对每个 $n\in\mathbb N_+$ ，定义 $B_n=(-\infty,-n]\cup[n,+\infty)$ ，得到一列闭集 $\left\{ B_n|n\in\mathbb N_+ \right\}$ 。对于任意 $y\in\mathbb R$ ，根据实数的阿基米德性质，存在 $N\in\mathbb N_+$ ，使得 $N>|y|$ ，即 $y\in(-N,N)$ ，所以存在开球 $B(y,\varepsilon)\subseteq(-N,N)$ 。那么当 $n>N$ 时， $B(y,\varepsilon)\cap B_n=\emptyset$ ，换句话说集族 $\left\{ B_n|n\in\mathbb N_+ \right\}$ 中最多只有有限个集合与 $B(y,\varepsilon)$ 相交。由 $y$ 的任意性可知 $\left\{ B_n|n\in\mathbb N_+ \right\}$ 为局部有限的闭集族。另一方面，因为 $X$ 不是P-空间，所以存在一列闭集 $\left\{ A_n|n\in\mathbb N_+ \right\}$ ，使得 $\bigcup_{n=1}^\infty A_n$ 不是闭集。令 $F_n=A_n\times B_n\subseteq X\times Y$ ，因为它是两个闭集的直积，所以是闭集。对于任意 $(x,y)\in X\times Y$ ，因为 $\left\{ B_n|n\in\mathbb N_+ \right\}$ 局部有限，所以存在 $y$ 的邻域 $V$ 仅和有限个 $B_n$ 相交，那么 $(x,y)$ 的邻域 $X\times V$ 也仅和有限个 $A_n\times B_n=F_n$ 相交，于是 $\left\{ F_n|n\in\mathbb N_+ \right\}$ 为局部有限的闭集族。根据引理21， $F=\bigcup_{n=1}^\infty F_n$ 是闭集。然而， $p(F)=p(\bigcup_{n=1}^\infty (A_n\times B_n))=\bigcup_{n=1}^\infty p(A_n\times B_n)=\bigcup_{n=1}^\infty A_n$ 不是闭集，这就说明 $p$ 不是闭映射。

证毕。

### 注意23（林德洛夫的P-空间与紧空间的区别）

上述几个命题介绍了林德洛夫的P-空间具有和紧空间相同的性质，但不能因此认为林德洛夫的P-空间就是紧空间。实际上存在林德洛夫的P-空间不是紧空间，也存在紧空间不是P-空间。

例如设 $X$ 为可数集，赋予离散拓扑，则它不是紧空间，但是是P-空间。同时，因为 $X$ 具有可数稠密子集 $X$ ，即它可分；且离散空间可距离化，所以 $X$ 林德洛夫。

又设 $X$ 为无限集，赋予有限补拓扑，则它是紧空间，也是 $T_1$ 空间。假设它是P-空间，根据定理14， $X$ 为有限集，矛盾。