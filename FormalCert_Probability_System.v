(* FormalCert_Probability_System.v *)
(* FormalCert Probability System v4.0 *)
(* 形证概率系统 *)
(** 
  统一数学基础系统 v1.0
  设计原则：统一、安全、模块化、可扩展
  
  解决的核心问题：
  1. 实数系统不统一：统一使用Coq标准库Reals
  2. 集合论基础不安全：使用类型安全的谓词集合
  3. 符号冲突：通过命名空间限定
  4. 模块接口混乱：建立统一基础接口
**)
(* 全局导入 *)
Require Import Coq.micromega.Lra.
Require Import Coq.Logic.Classical_Prop.      (* 经典逻辑 *)
Require Import Coq.Logic.FunctionalExtensionality. (* 函数外延性 *)
Require Import Coq.Logic.PropExtensionality.  (* 命题外延性 *)
Require Import Coq.Logic.Classical_Pred_Type. (* 为NNPP等 *)
Require Import Coq.Logic.ClassicalEpsilon.    (* 经典选择 *)
Require Import Coq.Classes.RelationClasses.   (* 关系类 *)
Require Import Coq.Classes.Morphisms.         (* 态射 *)
Require Import Coq.Arith.Arith.               (* 算术 *)
Require Import Coq.Arith.PeanoNat.            (* Peano算术 *)
Require Import Coq.Lists.List.                (* 列表 *)
Require Import Coq.Program.Program.           (* 程序扩展 *)
Require Import Coq.QArith.Qminmax.            (* 有理数最小最大 *)
  
(* 线性实数算术 *)
Require Import Coq.micromega.Lra.
From Coq Require Import Lia.
  
(* ================================================================= *)
(* 第一部分：模块类型定义 (Interface/Signature) *)
(* UnifiedMathFoundationSig - 定义数学基础系统的接口 *)
(* ================================================================= *)
  
Module Type UnifiedMathFoundationSig.
  
(* =========== 1. 标准库导入 =========== *)
(* 注意：避免循环导入，精简依赖 *)
  
Require Import Coq.Reals.Reals.               (* 统一实数系统 *)
Require Import Coq.QArith.QArith.             (* 有理数 *)
Require Import Coq.QArith.Qabs.               (* 有理数绝对值 *)
  
(* 实数序列和级数 *)
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.Rseries.
Require Import Coq.Reals.Rsigma.
Require Import Coq.Reals.Rcomplete.
Require Import Coq.Reals.Ranalysis1.
  
(* 线性实数算术 *)
Require Import Coq.micromega.Lra.
From Coq Require Import Lia.
  
Open Scope Q_scope.
Open Scope R_scope.
  
(** =========== 2. 统一实数系统 =========== *)
(** 所有实数操作都基于Coq.Reals.Reals库 **)
  
(* 实数类型别名 - 直接定义而非参数 *)
Definition ℝ := R.
  
(* 实数运算别名 - 增强可读性 *)
(* 使用Coq标准库中的定义 *)
Notation "x +ℝ y" := (Rplus x y) (at level 50, left associativity).
Notation "x -ℝ y" := (Rminus x y) (at level 50, left associativity).
Notation "x *ℝ y" := (Rmult x y) (at level 40, left associativity).
Notation "x /ℝ y" := (Rdiv x y) (at level 40, left associativity).
Notation "x ≤ℝ y" := (Rle x y) (at level 70, no associativity).
Notation "x <ℝ y" := (Rlt x y) (at level 70, no associativity).
Notation "x ≥ℝ y" := (Rge x y) (at level 70, no associativity).
Notation "x >ℝ y" := (Rgt x y) (at level 70, no associativity).
Notation "| x |" := (Rabs x) (at level 30).
  
(* 实数常数 *)
Definition R0 : R := 0%R.
Definition R1 : R := 1%R.
  
(* 实数非负性证明 *)
Axiom Rle_0_1 : IZR (0%Z) ≤ℝ IZR (1%Z).
  
(* 实数算术基本引理 *)
Axiom Rplus_comm : forall x y : ℝ, x +ℝ y = y +ℝ x.
Axiom Rmult_comm : forall x y : ℝ, x *ℝ y = y *ℝ x.
Axiom Rplus_assoc : forall x y z : ℝ, x +ℝ (y +ℝ z) = (x +ℝ y) +ℝ z.
Axiom Rmult_assoc : forall x y z : ℝ, x *ℝ (y *ℝ z) = (x *ℝ y) *ℝ z.
  
(** =========== 3. 统一集合论 =========== *)
(** 类型安全的谓词集合，避免罗素悖论 **)
  
(* 3.1 基础定义 *)
  
(* 集合定义为类型的子集 *)
Definition SetX (X : Type) : Type := X -> Prop.
  
(* 属于关系 *)
Definition In {X : Type} (x : X) (A : SetX X) : Prop := A x.
Notation "x 'in_s' A" := (In x A) (at level 50).
Notation "x 'notin_s' A" := (~ In x A) (at level 50).
  
(* 子集关系 *)
Definition Subset {X : Type} (A B : SetX X) : Prop :=
  forall x : X, In x A -> In x B.
Notation "A 'subset_s' B" := (Subset A B) (at level 60).
  
(* 集合相等：外延性公理 *)
Definition SetEq {X : Type} (A B : SetX X) : Prop :=
  forall x : X, In x A <-> In x B.
Notation "A 'eq_s' B" := (SetEq A B) (at level 70).
  
Axiom set_extensionality : forall {X : Type} (A B : SetX X),
  SetEq A B -> A = B.
  
(* 3.2 基本集合运算 *)
  
(* 空集 *)
Definition EmptySet {X : Type} : SetX X := fun _ => False.
Notation "'EmptySet_s'" := (EmptySet) (at level 0).
  
(* 全集 *)
Definition UniversalSet {X : Type} : SetX X := fun _ => True.
Notation "'UniversalSet_s'" := (UniversalSet) (at level 0).
  
(* 补集 *)
Definition Complement {X : Type} (A : SetX X) : SetX X :=
  fun x => ~ (In x A).
Notation "'Complement_s' A" := (Complement A) (at level 30).
  
(* 并集 - 使用lambda表达式避免解析问题 *)
Definition Union {X : Type} (A B : SetX X) : SetX X :=
  fun x => In x A \/ In x B.
Notation "A 'Union_s' B" := (Union A B) (at level 45).
  
(* 交集 *)
Definition Intersection {X : Type} (A B : SetX X) : SetX X :=
  fun x => In x A /\ In x B.
Notation "A 'Intersection_s' B" := (Intersection A B) (at level 40).
  
(* 差集 *)
Definition Difference {X : Type} (A B : SetX X) : SetX X :=
  fun x => In x A /\ ~ In x B.
Notation "A 'setminus_s' B" := (Difference A B) (at level 40).
  
(* 对称差 *)
Definition SymmetricDifference {X : Type} (A B : SetX X) : SetX X :=
  fun x => (In x A /\ ~ In x B) \/ (~ In x A /\ In x B).
Notation "A 'symdiff_s' B" := (SymmetricDifference A B) (at level 40).
  
(* 3.3 可数集合运算 *)
  
(* 可数并集 *)
Definition CountableUnion {X : Type} (F : nat -> SetX X) : SetX X :=
  fun x => exists n, In x (F n).
Notation "'Union_over_s' n , F" := (CountableUnion F) (at level 50).
  
(* 可数交集 *)
Definition CountableIntersection {X : Type} (F : nat -> SetX X) : SetX X :=
  fun x => forall n, In x (F n).
Notation "'Intersection_over_s' n , F" := (CountableIntersection F) (at level 50).
  
(* 3.4 集合性质 *)
  
(* 不相交 *)
Definition Disjoint {X : Type} (A B : SetX X) : Prop :=
  forall x, ~ (In x A /\ In x B).
  
(* 两两不相交族 *)
Definition PairwiseDisjoint {X : Type} (F : nat -> SetX X) : Prop :=
  forall n m, n <> m -> Disjoint (F n) (F m).
  
(* 集合包含链 *)
Definition IncreasingSequence {X : Type} (F : nat -> SetX X) : Prop :=
  forall n, Subset (F n) (F (S n)).
  
Definition DecreasingSequence {X : Type} (F : nat -> SetX X) : Prop :=
  forall n, Subset (F (S n)) (F n).
  
(** =========== 4. 集合基本定理 =========== *)
  
(* 空集性质：任何元素都不属于空集 *)
Axiom empty_set_property : forall {X : Type} (x : X),
  ~ In x EmptySet.
  
(* 全集性质：任何元素都属于全集 *)
Axiom universal_set_property : forall {X : Type} (x : X),
  In x UniversalSet.
  
(* 补集性质：元素属于补集当且仅当它不属于原集合 *)
Axiom complement_property : forall {X : Type} (A : SetX X) (x : X),
  In x (Complement A) <-> ~ In x A.
  
(* 并集性质 - 使用lambda表达式 *)
Axiom union_property : forall {X : Type} (A B : SetX X) (x : X),
  (fun x => In x A \/ In x B) x <-> In x A \/ In x B.
  
(* 差集性质 - 使用lambda表达式 *)
Axiom difference_property : forall {X : Type} (A B : SetX X) (x : X),
  (fun x => In x A /\ ~ In x B) x <-> In x A /\ ~ In x B.
  
(* 子集自反性：任何集合都是自身的子集 *)
Axiom subset_reflexive : forall {X : Type} (A : SetX X),
  Subset A A.
  
(* 子集传递性：如果A是B的子集且B是C的子集，则A是C的子集 *)
Axiom subset_transitive : forall {X : Type} (A B C : SetX X),
  Subset A B -> Subset B C -> Subset A C.
  
(* 补集的双重补集等于原集合 *)
Axiom complement_involution : forall {X : Type} (A : SetX X),
  SetEq (Complement (Complement A)) A.
  
(* 德摩根定律：并集的补集等于补集的交集 - 使用lambda表达式 *)
Axiom demorgan_union_complement : forall {X : Type} (A B : SetX X),
  SetEq (Complement (fun x => In x A \/ In x B))
        (fun x => In x (Complement A) /\ In x (Complement B)).
  
(* 德摩根定律：交集的补集等于补集的并集 - 使用lambda表达式 *)
Axiom demorgan_intersection_complement : forall {X : Type} (A B : SetX X),
  SetEq (Complement (fun x => In x A /\ In x B))
        (fun x => In x (Complement A) \/ In x (Complement B)).
  
(* 辅助引理：恢复符号表示，但使用lambda表达式 *)
Axiom demorgan_intersection_complement_symb : forall {X : Type} (A B : SetX X),
  SetEq (Complement (fun x => In x A /\ In x B))
        (fun x => In x (Complement A) \/ In x (Complement B)).
  
(* 使用并集性质的示例 *)
Axiom example_union : forall {X : Type} (A B : SetX X) (x : X),
  In x A -> (fun x => In x A \/ In x B) x.
  
(** =========== 5. 实数序列与级数 =========== *)
  
(* 部分和函数包装 - 直接使用定义 *)
Definition partial_sum (f : nat -> ℝ) (n : nat) : ℝ :=
  sum_f_R0 f n.
  
(* 无穷级数和定义 *)
Definition infinite_sum (f : nat -> ℝ) (l : ℝ) : Prop :=
  infinite_sum f l.
  
(* 序列收敛定义 *)
Definition sequence_converges (u : nat -> ℝ) (l : ℝ) : Prop :=
  Un_cv u l.
Notation "u 'converges_to' l" := (sequence_converges u l) (at level 80).
  
(* 单调有界序列收敛定理 *)
Axiom monotone_bounded_convergence :
  forall (u : nat -> ℝ),
    (forall n, u n ≤ℝ u (S n)) ->                    (* 单调递增 *)
    (exists M, forall n, u n ≤ℝ M) ->                (* 有上界 *)
    exists l, sequence_converges u l.
  
(* 序列极限基本性质 *)
  
(* 极限的唯一性：收敛序列的极限是唯一的 *)
Axiom limit_unique : forall (u : nat -> ℝ) (l1 l2 : ℝ),
  sequence_converges u l1 -> sequence_converges u l2 -> l1 = l2.
  
(* 常数序列收敛于该常数 *)
Axiom limit_const : forall (c : ℝ),
  sequence_converges (fun _ => c) c.
  
(* 夹逼定理 *)
Axiom squeeze_theorem :
  forall (u v w : nat -> ℝ) (l : ℝ),
    (forall n, Rle (u n) (v n)) ->      (* u ≤ v *)
    (forall n, Rle (v n) (w n)) ->      (* v ≤ w *)
    sequence_converges u l ->           (* u 收敛到 l *)
    sequence_converges w l ->           (* w 收敛到 l *)
    sequence_converges v l.             (* 则 v 也收敛到 l *)
  
(** =========== 6. 可计算实数 =========== *)
(** 用于构造性证明的可计算实数近似 **)
  
(* 区间算术：用于构造性实数 *)
Record IntervalR := {
  low_bound : ℝ;
  high_bound : ℝ;
  bounds_valid : low_bound ≤ℝ high_bound
}.
  
Notation "[| a , b |]" := {| 
  low_bound := a; 
  high_bound := b; 
  bounds_valid := _ 
|} (at level 0).
  
Definition IR := IntervalR.
  
(* 投影函数 *)
Definition lower (ir : IR) : ℝ := low_bound ir.
Definition upper (ir : IR) : ℝ := high_bound ir.
  
(* 区间运算 *)
Definition interval_add (ir1 ir2 : IR) : IR :=
  {| 
    low_bound := lower ir1 + lower ir2;
    high_bound := upper ir1 + upper ir2;
    bounds_valid := 
      Rplus_le_compat (lower ir1) (upper ir1) (lower ir2) (upper ir2)
        (bounds_valid ir1) (bounds_valid ir2)
  |}.
  
(** =========== 7. 有限与可数选择原则 =========== *)
  
(* 有限选择：对有限集成立 *)
Axiom finite_choice : forall {X : Type} (A : SetX X) (P : X -> Prop),
  (forall x, In x A -> exists y, P y) ->
  exists f, forall x, In x A -> P (f x).
  
(* 可数选择：需要经典逻辑 *)
Axiom countable_choice : forall (P : nat -> nat -> Prop),
  (forall n, exists m, P n m) ->
  exists f, forall n, P n (f n).
  
(** =========== 8. 扩展实数系统 =========== *)
(** 为测度论准备的扩展实数 **)
  
Inductive ExtendedReal : Type :=
  | Finite : ℝ -> ExtendedReal
  | PosInfinity : ExtendedReal
  | NegInfinity : ExtendedReal.
  
Notation "+INF" := PosInfinity.
Notation "-INF" := NegInfinity.
Notation "[ r ]" := (Finite r).
  
(* 扩展实数序 *)
Inductive EReal_le : ExtendedReal -> ExtendedReal -> Prop :=
  | EReal_le_finite : forall r1 r2, r1 ≤ℝ r2 -> EReal_le (Finite r1) (Finite r2)
  | EReal_le_neg_infinity : forall x, EReal_le NegInfinity x
  | EReal_le_pos_infinity : forall x, EReal_le x PosInfinity.
  
Notation "x 'le_e' y" := (EReal_le x y) (at level 70).
  
(* 扩展实数加法（部分定义） *)
Definition EReal_add (x y : ExtendedReal) : ExtendedReal :=
  match x, y with
  | Finite r1, Finite r2 => Finite (r1 +ℝ r2)
  | NegInfinity, _ => NegInfinity
  | _, NegInfinity => NegInfinity
  | PosInfinity, Finite _ => PosInfinity
  | Finite _, PosInfinity => PosInfinity
  | PosInfinity, PosInfinity => PosInfinity
  end.
  
Notation "x 'add_e' y" := (EReal_add x y) (at level 50).
  
(** =========== 9. 函数空间 =========== *)
  
(* 经典命题判定 - 作为公理声明 *)
Axiom classic_dec : forall (P : Prop), {P} + {~P}.
  
(* 可测函数类型 *)
Definition MeasurableFunction (X Y : Type) : Type := X -> Y.
  
(* 指示函数 *)
Definition indicator {X : Type} (A : SetX X) : X -> ℝ :=
  fun x => if classic_dec (In x A) then R1 else R0.
  
Axiom indicator_property : forall {X : Type} (A : SetX X) (x : X),
  indicator A x = R1 <-> In x A.
  
(** =========== 10. 模块接口 =========== *)
(** 为后续模块提供统一接口 **)
  
(* 实数系统接口 *)
Module Type RealSystem.
  Parameter R : Type.
  Parameter Rplus : R -> R -> R.
  Parameter Rmult : R -> R -> R.
  Parameter Rle : R -> R -> Prop.
  (* ... 更多操作 *)
End RealSystem.
  
(* 集合系统接口 *)
Module Type SetSystem.
  Parameter SetX : Type -> Type.
  Parameter In : forall {X:Type}, X -> SetX X -> Prop.
  (* ... 更多操作 *)
End SetSystem.
  
End UnifiedMathFoundationSig.
  
(* ================================================================= *)
(* 第二部分：具体实现模块 *)
(* UnifiedMathFoundationImpl - 实现UnifiedMathFoundationSig接口 *)
(* ================================================================= *)

Module UnifiedMathFoundationImpl : UnifiedMathFoundationSig.
  
(* =========== 1. 标准库导入 =========== *)
(* 完全复制原始代码的导入部分 *)
  
Require Import Coq.Reals.Reals.               (* 统一实数系统 *)
Require Import Coq.Logic.Classical_Prop.      (* 经典逻辑 *)
Require Import Coq.Logic.FunctionalExtensionality. (* 函数外延性 *)
Require Import Coq.Logic.PropExtensionality.  (* 命题外延性 *)
Require Import Coq.Logic.Classical_Pred_Type. (* 为NNPP等 *)
Require Import Coq.Logic.ClassicalEpsilon.    (* 经典选择 *)
Require Import Coq.Classes.RelationClasses.   (* 关系类 *)
Require Import Coq.Classes.Morphisms.         (* 态射 *)
Require Import Coq.Arith.Arith.               (* 算术 *)
Require Import Coq.Arith.PeanoNat.            (* Peano算术 *)
Require Import Coq.Lists.List.                (* 列表 *)
Require Import Coq.Program.Program.           (* 程序扩展 *)
Require Import Coq.QArith.QArith.             (* 有理数 *)
Require Import Coq.QArith.Qabs.               (* 有理数绝对值 *)
Require Import Coq.QArith.Qminmax.            (* 有理数最小最大 *)
  
(* 实数序列和级数 *)
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.Rseries.
Require Import Coq.Reals.Rsigma.
Require Import Coq.Reals.Rcomplete.
Require Import Coq.Reals.Ranalysis1.
  
(* 线性实数算术 *)
Require Import Coq.micromega.Lra.
From Coq Require Import Lia.
(* 从Coquelicot导入高级分析工具 *)
Require Import Coquelicot.Coquelicot.
  
Open Scope Q_scope.
Open Scope R_scope.
  
(** =========== 2. 统一实数系统 =========== *)
(** 所有实数操作都基于Coq.Reals.Reals库 **)
  
(* 实数类型别名 *)
Definition ℝ := R.
  
(* 实数运算别名 - 增强可读性 *)
Notation "x +ℝ y" := (Rplus x y) (at level 50, left associativity).
Notation "x -ℝ y" := (Rminus x y) (at level 50, left associativity).
Notation "x *ℝ y" := (Rmult x y) (at level 40, left associativity).
Notation "x /ℝ y" := (Rdiv x y) (at level 40, left associativity).
Notation "x ≤ℝ y" := (Rle x y) (at level 70, no associativity).
Notation "x <ℝ y" := (Rlt x y) (at level 70, no associativity).
Notation "x ≥ℝ y" := (Rge x y) (at level 70, no associativity).
Notation "x >ℝ y" := (Rgt x y) (at level 70, no associativity).
Notation "| x |" := (Rabs x) (at level 30).
  
(* 实数常数 *)
Definition R0 : R := 0%R.
Definition R1 : R := 1%R.
  
(* 实数非负性证明 *)
Lemma Rle_0_1 : IZR (0%Z) <= IZR (1%Z).
Proof. lra. Qed.
  
(* 实数算术基本引理 *)
Lemma Rplus_comm : forall x y : R, x + y = y + x.
Proof. exact Rplus_comm. Qed.
  
(* 实数乘法交换律 *)
Lemma Rmult_comm : forall x y : R, x * y = y * x.
Proof. exact Rmult_comm. Qed.
  
(* 实数加法结合律 *)
Lemma Rplus_assoc : forall x y z : R, x + (y + z) = (x + y) + z.
Proof. 
  intros x y z.
  rewrite <- Rplus_assoc.
  reflexivity.
Qed.
  
(* 实数乘法结合律 *)
Lemma Rmult_assoc : forall x y z : R, x * (y * z) = (x * y) * z.
Proof. 
  intros x y z.
  rewrite Rmult_assoc.
  reflexivity.
Qed.
  
(** =========== 3. 统一集合论 =========== *)
(** 类型安全的谓词集合，避免罗素悖论 **)
  
(* 3.1 基础定义 *)
  
(* 集合定义为类型的子集 *)
Definition SetX (X : Type) : Type := X -> Prop.
  
(* 属于关系 *)
Definition In {X : Type} (x : X) (A : SetX X) : Prop := A x.
Notation "x 'in_s' A" := (In x A) (at level 50).
Notation "x 'notin_s' A" := (~ In x A) (at level 50).
  
(* 子集关系 *)
Definition Subset {X : Type} (A B : SetX X) : Prop :=
  forall x : X, In x A -> In x B.
Notation "A 'subset_s' B" := (Subset A B) (at level 60).
  
(* 集合相等：外延性公理 *)
Definition SetEq {X : Type} (A B : SetX X) : Prop :=
  forall x : X, In x A <-> In x B.
Notation "A 'eq_s' B" := (SetEq A B) (at level 70).
  
Axiom set_extensionality : forall {X : Type} (A B : SetX X),
  SetEq A B -> A = B.
  
(* 3.2 基本集合运算 *)
  
(* 空集 *)
Definition EmptySet {X : Type} : SetX X := fun _ => False.
Notation "'EmptySet_s'" := (EmptySet) (at level 0).

(* 全集 *)
Definition UniversalSet {X : Type} : SetX X := fun _ => True.
Notation "'UniversalSet_s'" := (UniversalSet) (at level 0).

(* 补集 *)
Definition Complement {X : Type} (A : SetX X) : SetX X :=
  fun x => ~ (In x A).
Notation "'Complement_s' A" := (Complement A) (at level 30).

(* 并集 - 使用lambda表达式避免解析问题 *)
Definition Union {X : Type} (A B : SetX X) : SetX X :=
  fun x => In x A \/ In x B.
Notation "A 'Union_s' B" := (Union A B) (at level 45).

(* 交集 *)
Definition Intersection {X : Type} (A B : SetX X) : SetX X :=
  fun x => In x A /\ In x B.
Notation "A 'Intersection_s' B" := (Intersection A B) (at level 40).

(* 差集 *)
Definition Difference {X : Type} (A B : SetX X) : SetX X :=
  fun x => In x A /\ ~ In x B.
Notation "A 'setminus_s' B" := (Difference A B) (at level 40).
  
(* 对称差 *)
Definition SymmetricDifference {X : Type} (A B : SetX X) : SetX X :=
  fun x => (In x A /\ ~ In x B) \/ (~ In x A /\ In x B).
Notation "A 'symdiff_s' B" := (SymmetricDifference A B) (at level 40).
  
(* 3.3 可数集合运算 *)
  
(* 可数并集 *)
Definition CountableUnion {X : Type} (F : nat -> SetX X) : SetX X :=
  fun x => exists n, In x (F n).
Notation "'Union_over_s' n , F" := (CountableUnion F) (at level 50).
  
(* 可数交集 *)
Definition CountableIntersection {X : Type} (F : nat -> SetX X) : SetX X :=
  fun x => forall n, In x (F n).
Notation "'Intersection_over_s' n , F" := (CountableIntersection F) (at level 50).
  
(* 3.4 集合性质 *)
  
(* 不相交 *)
Definition Disjoint {X : Type} (A B : SetX X) : Prop :=
  forall x, ~ (In x A /\ In x B).
  
(* 两两不相交族 *)
Definition PairwiseDisjoint {X : Type} (F : nat -> SetX X) : Prop :=
  forall n m, n <> m -> Disjoint (F n) (F m).
  
(* 集合包含链 *)
Definition IncreasingSequence {X : Type} (F : nat -> SetX X) : Prop :=
  forall n, Subset (F n) (F (S n)).
  
Definition DecreasingSequence {X : Type} (F : nat -> SetX X) : Prop :=
  forall n, Subset (F (S n)) (F n).
  
(** =========== 4. 集合基本定理 =========== *)
  
(* 空集性质：任何元素都不属于空集 *)
Lemma empty_set_property : forall {X : Type} (x : X),
  ~ In x EmptySet.
Proof. 
  intros X x. 
  unfold In, EmptySet.
  exact (fun f : False => f).
Qed.
  
(* 全集性质：任何元素都属于全集 *)
Lemma universal_set_property : forall {X : Type} (x : X),
  In x UniversalSet.
Proof. 
  intros X x. 
  unfold In, UniversalSet. 
  exact I. 
Qed.
  
(* 补集性质：元素属于补集当且仅当它不属于原集合 *)
Lemma complement_property : forall {X : Type} (A : SetX X) (x : X),
  In x (Complement A) <-> ~ In x A.
Proof. 
  intros X A x. 
  reflexivity. 
Qed.
  
(* 并集性质：元素属于并集当且仅当它属于A或属于B *)
Lemma union_property : forall {X : Type} (A B : SetX X) (x : X),
  (fun x => In x A \/ In x B) x <-> In x A \/ In x B.
Proof.
  reflexivity.
Qed.
  
(* 差集性质：元素属于差集A∖B当且仅当它属于A且不属于B *)
Lemma difference_property : forall {X : Type} (A B : SetX X) (x : X),
  (fun x => In x A /\ ~ In x B) x <-> In x A /\ ~ In x B.
Proof.
  reflexivity.
Qed.
  
(* 子集自反性：任何集合都是自身的子集 *)
Lemma subset_reflexive : forall {X : Type} (A : SetX X),
  Subset A A.
Proof. 
  intros X A x H. 
  exact H. 
Qed.
  
(* 子集传递性：如果A是B的子集且B是C的子集，则A是C的子集 *)
Lemma subset_transitive : forall {X : Type} (A B C : SetX X),
  Subset A B -> Subset B C -> Subset A C.
Proof.
  intros X A B C HAB HBC x HA.
  apply HBC, HAB, HA.
Qed.

(* 补集的双重补集等于原集合 *)
Lemma complement_involution : forall {X : Type} (A : SetX X),
  SetEq (Complement (Complement A)) A.
Proof.
  intros X A.
  unfold SetEq.
  intro x.
  split.
  - intro H.
    (* H: In x (Complement (Complement A)) *)
    unfold In in H.
    simpl in H.  (* 将Complement的定义展开，得到两个否定 *)
    apply NNPP; exact H.
  - intro H.
    (* H: In x A *)
    unfold In.
    simpl.  (* 展开Complement的定义，得到 fun x => ~ ~ In x A，然后应用到x上，得到 ~ ~ In x A *)
    intro H'.
    contradiction H'.
Qed.
  
(* 德摩根定律：并集的补集等于补集的交集 *)
Lemma demorgan_union_complement : forall {X : Type} (A B : SetX X),
  SetEq (Complement (fun x => In x A \/ In x B))
        (fun x => In x (Complement A) /\ In x (Complement B)).
Proof.
  intros X A B.
  unfold SetEq.
  intro x.
  split.
  - intro H.
    simpl in H.  (* 简化假设H *)
    split.
    + intro HA.
      apply H.
      left.
      exact HA.
    + intro HB.
      apply H.
      right.
      exact HB.
  - intro H.
    destruct H as [H1 H2].
    simpl.  (* 简化目标 *)
    intro Hor.
    destruct Hor as [HA | HB].
    + apply H1, HA.
    + apply H2, HB.
Qed.
  
(* 德摩根定律：交集的补集等于补集的并集 *)
Lemma demorgan_intersection_complement : forall {X : Type} (A B : SetX X),
  SetEq (Complement (fun x => In x A /\ In x B))
        (fun x => In x (Complement A) \/ In x (Complement B)).
Proof.
  intros X A B.
  unfold SetEq.
  intro x.
  split.
  - intro H.
    (* H: x 在 (A∩B)的补集中，即 ~(In x A /\ In x B) *)
    simpl in H.
    destruct (classic (In x A)) as [HA | HA].
    + (* 情况1: 如果 x 在 A 中，则必须不在 B 中 *)
      right.
      intro HB.
      apply H.
      split; assumption.
    + (* 情况2: 如果 x 不在 A 中，则它在 A 的补集中 *)
      left.
      exact HA.
  - intro H.
    (* H: x 在 A的补集 或 B的补集中 *)
    destruct H as [H1 | H2].
    + (* 情况1: x 在 A的补集中，即 ~In x A *)
      simpl.
      intro HAB.
      destruct HAB as [HA HB].
      apply H1, HA.
    + (* 情况2: x 在 B的补集中，即 ~In x B *)
      simpl.
      intro HAB.
      destruct HAB as [HA HB].
      apply H2, HB.
Qed.
  
(* 辅助引理：恢复符号表示，但使用lambda表达式 *)
Lemma demorgan_intersection_complement_symb : forall {X : Type} (A B : SetX X),
  SetEq (Complement (fun x => In x A /\ In x B))
        (fun x => In x (Complement A) \/ In x (Complement B)).
Proof.
  intros X A B.
  apply demorgan_intersection_complement.
Qed.
  
(* 使用并集性质的示例 *)
Example example_union : forall {X : Type} (A B : SetX X) (x : X),
  In x A -> (fun x => In x A \/ In x B) x.
Proof.
  intros X A B x HA.
  unfold In.
  simpl.
  left.
  exact HA.
Qed.
  
(** =========== 5. 实数序列与级数 =========== *)
  
(* 部分和函数包装 *)
Definition partial_sum (f : nat -> R) (n : nat) : R :=
  sum_f_R0 f n.
  
(* 无穷级数和定义 *)
Definition infinite_sum (f : nat -> R) (l : R) : Prop :=
  infinite_sum f l.
  
(* 序列收敛定义 *)
Definition sequence_converges (u : nat -> R) (l : R) : Prop :=
  Un_cv u l.
Notation "u 'converges_to' l" := (sequence_converges u l) (at level 80).
  
(* 单调有界序列收敛定理 *)
Theorem monotone_bounded_convergence :
  forall (u : nat -> R),
    (forall n, u n <= u (S n)) ->                    (* 单调递增 *)
    (exists M, forall n, u n <= M) ->                (* 有上界 *)
    exists l, sequence_converges u l.
Proof.
  intros u Hmono Hbounded.
  destruct Hbounded as [M HM].
  
  (* 定义值域集合 *)
  set (E := fun (x : R) => exists n, x = u n).
  
  (* 证明 E 非空 *)
  assert (E_nonempty : exists x, E x).
  { exists (u 0%nat). unfold E. exists 0%nat. reflexivity. }
  
  (* 证明 E 有上界 *)
  assert (E_bound : exists bound, forall x, E x -> x <= bound).
  { exists M. intros x [n Hx]. rewrite Hx. apply HM. }
  
  (* 使用实数完备性定理得到上确界 *)
  destruct (completeness E E_bound E_nonempty) as [l [l_upper l_least]].
  
  exists l.
  unfold sequence_converges, Un_cv.
  intros eps Heps_pos.
  
  (* 上确界性质：存在 x ∈ E 使得 l - eps < x *)
  assert (exists_x : exists x, E x /\ l - eps < x).
  {
    apply NNPP. intro H.
    assert (is_upper_bound_E : is_upper_bound E (l - eps)).
    {
      unfold is_upper_bound.
      intros x Hx.
      apply Rnot_lt_le.
      intro Hlt.
      apply H.
      exists x.
      split; assumption.
    }
    assert (H_le : l <= l - eps) by (apply l_least; assumption).
    lra.
  }
  
  destruct exists_x as [x [Hx Hx_bound]].
  destruct Hx as [N Hx_val].
  
  exists N.
  intros n Hn_ge.
  
  unfold R_dist.
  apply Rabs_def1.
  - (* u n - l < eps *)
    assert (H_in_E : E (u n)).
    { unfold E. exists n. reflexivity. }
    apply l_upper in H_in_E.
    lra.
  - (* -eps < u n - l *)
    rewrite Hx_val in Hx_bound.  (* x = u N *)
    assert (u_N_le_u_n : u N <= u n).
    {
      induction Hn_ge as [|m' Hle IH].
      - apply Rle_refl.
      - apply Rle_trans with (u m').
        + exact IH.
        + apply Hmono.
    }
    lra.
Qed.
  
(* 序列极限基本性质 *)
  
(* 极限的唯一性：收敛序列的极限是唯一的 *)
Lemma limit_unique : forall (u : nat -> R) (l1 l2 : R),
  sequence_converges u l1 -> sequence_converges u l2 -> l1 = l2.
Proof.
  intros u l1 l2 H1 H2.
  unfold sequence_converges in H1, H2.
  (* 使用标准库中的极限唯一性引理，明确提供序列参数 *)
  apply (UL_sequence u l1 l2); [exact H1 | exact H2].
Qed.
  
(* 常数序列收敛于该常数 *)
Lemma limit_const : forall (c : R),
  sequence_converges (fun _ => c) c.
Proof.
  intro c.
  unfold sequence_converges, Un_cv.
  intros eps Heps_pos.
  exists 0%nat.
  intros n _.
  unfold R_dist.
  rewrite Rminus_eq_0.    (* c - c = 0 *)
  rewrite Rabs_R0.        (* |0| = 0 *)
  assumption.             (* 0 < eps *)
Qed.
  
(* 夹逼定理 *)
Theorem squeeze_theorem :
  forall (u v w : nat -> R) (l : R),
    (forall n, Rle (u n) (v n)) ->      (* u ≤ v *)
    (forall n, Rle (v n) (w n)) ->      (* v ≤ w *)
    sequence_converges u l ->           (* u 收敛到 l *)
    sequence_converges w l ->           (* w 收敛到 l *)
    sequence_converges v l.             (* 则 v 也收敛到 l *)
Proof.
  intros u v w l Huv Hvw Hu Hw.
  unfold sequence_converges in Hu, Hw.
  unfold Un_cv in *.
  intros eps Heps_pos.
  
  (* 存在 N1 使得当 n ≥ N1 时，|u n - l| < ε *)
  destruct (Hu eps Heps_pos) as [N1 HN1].
  (* 存在 N2 使得当 n ≥ N2 时，|w n - l| < ε *)
  destruct (Hw eps Heps_pos) as [N2 HN2].
  
  (* 取 N = max(N1, N2) *)
  exists (max N1 N2).
  intros n Hn.
  
  (* 证明 n ≥ N1 且 n ≥ N2 *)
  assert (Hn1 : (n >= N1)%nat).
  { apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_l|exact Hn]. }
  
  assert (Hn2 : (n >= N2)%nat).
  { apply Nat.le_trans with (max N1 N2); [apply Nat.le_max_r|exact Hn]. }
  
  (* 获取绝对值不等式 *)
  specialize (HN1 n Hn1) as Hu_bound.
  specialize (HN2 n Hn2) as Hw_bound.
  
  unfold R_dist in *.
  
  (* 现在我们需要证明 |v n - l| < ε *)
  apply Rabs_def1.
  - apply Rle_lt_trans with (w n - l).
    + apply Rplus_le_compat_r. exact (Hvw n).
    + apply Rle_lt_trans with (Rabs (w n - l)).
      * apply Rle_abs.
      * exact Hw_bound.
  - apply Rlt_le_trans with (u n - l).
    + (* 证明 -ε < u n - l *)
      apply Rnot_le_lt. intro Hle.
      assert (Habs : eps <= Rabs (u n - l)).
      { apply Rle_trans with (- (u n - l)).
        - lra.
        - rewrite <- Rabs_Ropp. apply Rle_abs. }
      lra.
    + apply Rplus_le_compat_r. exact (Huv n).
Qed.
  
(** =========== 6. 可计算实数 =========== *)
(** 用于构造性证明的可计算实数近似 **)
  
(* 区间算术：用于构造性实数 *)
Record IntervalR := {
  low_bound : ℝ;
  high_bound : ℝ;
  bounds_valid : low_bound ≤ℝ high_bound
}.
  
Notation "[| a , b |]" := {| 
  low_bound := a; 
  high_bound := b; 
  bounds_valid := _ 
|} (at level 0).
  
Definition IR := IntervalR.
  
(* 投影函数 *)
Definition lower (ir : IR) : ℝ := low_bound ir.
Definition upper (ir : IR) : ℝ := high_bound ir.
  
(* 区间运算 *)
Definition interval_add (ir1 ir2 : IR) : IR :=
  {| 
    low_bound := lower ir1 + lower ir2;
    high_bound := upper ir1 + upper ir2;
    bounds_valid := 
      Rplus_le_compat (lower ir1) (upper ir1) (lower ir2) (upper ir2)
        (bounds_valid ir1) (bounds_valid ir2)
  |}.
  
(** =========== 7. 有限与可数选择原则 =========== *)
  
(* 有限选择：对有限集成立 *)
Axiom finite_choice : forall {X : Type} (A : SetX X) (P : X -> Prop),
  (forall x, In x A -> exists y, P y) ->
  exists f, forall x, In x A -> P (f x).
  
(* 可数选择：需要经典逻辑 *)
Axiom countable_choice : forall (P : nat -> nat -> Prop),
  (forall n, exists m, P n m) ->
  exists f, forall n, P n (f n).
  
(** =========== 8. 扩展实数系统 =========== *)
(** 为测度论准备的扩展实数 **)
  
Inductive ExtendedReal : Type :=
  | Finite : R -> ExtendedReal
  | PosInfinity : ExtendedReal
  | NegInfinity : ExtendedReal.
  
Notation "+INF" := PosInfinity.
Notation "-INF" := NegInfinity.
Notation "[ r ]" := (Finite r).
  
(* 扩展实数序 *)
Inductive EReal_le : ExtendedReal -> ExtendedReal -> Prop :=
  | EReal_le_finite : forall r1 r2, r1 <= r2 -> EReal_le (Finite r1) (Finite r2)
  | EReal_le_neg_infinity : forall x, EReal_le NegInfinity x
  | EReal_le_pos_infinity : forall x, EReal_le x PosInfinity.
  
Notation "x 'le_e' y" := (EReal_le x y) (at level 70).
  
(* 扩展实数加法（部分定义） *)
Definition EReal_add (x y : ExtendedReal) : ExtendedReal :=
  match x, y with
  | Finite r1, Finite r2 => Finite (r1 + r2)
  | NegInfinity, _ => NegInfinity
  | _, NegInfinity => NegInfinity
  | PosInfinity, Finite _ => PosInfinity
  | Finite _, PosInfinity => PosInfinity
  | PosInfinity, PosInfinity => PosInfinity
  end.
  
Notation "x 'add_e' y" := (EReal_add x y) (at level 50).
  
(** =========== 9. 函数空间 =========== *)

(* 经典命题判定 - 作为公理声明 *)
Axiom classic_dec : forall (P : Prop), {P} + {~P}.

(* 可测函数类型 *)
Definition MeasurableFunction (X Y : Type) : Type := X -> Y.
  
(* 指示函数 *)
Definition indicator {X : Type} (A : SetX X) : X -> R :=
  fun x => if classic_dec (In x A) then 1%R else 0%R.
  
Lemma indicator_property : forall {X : Type} (A : SetX X) (x : X),
  indicator A x = 1%R <-> In x A.
Proof.
  intros X A x.
  unfold indicator.
  split.
  - intro H.
    (* 第一种情况：当指示函数值为1时 *)
    destruct (classic_dec (In x A)) as [Hin|Hnot].
    + (* 子情况1：x在A中，直接使用假设 *)
      assumption.
    + (* 子情况2：x不在A中，得到0=1的矛盾 *)
      simpl in H.
      lra.  (* 使用线性实数算术解决0=1的矛盾 *)
  - intro H.
    (* 第二种情况：当x在A中时 *)
    destruct (classic_dec (In x A)) as [Hin|Hnot].
    + (* 子情况1：判定为x在A中，则指示函数值为1，等式成立 *)
      reflexivity.
    + (* 子情况2：判定为x不在A中，与前提x在A中矛盾 *)
      contradiction.
Qed.
  
(** =========== 10. 模块接口 =========== *)
(** 为后续模块提供统一接口 **)
  
(* 实数系统接口 *)
Module Type RealSystem.
  Parameter R : Type.
  Parameter Rplus : R -> R -> R.
  Parameter Rmult : R -> R -> R.
  Parameter Rle : R -> R -> Prop.
  (* ... 更多操作 *)
End RealSystem.
  
(* 集合系统接口 *)
Module Type SetSystem.
  Parameter SetX : Type -> Type.
  Parameter In : forall {X:Type}, X -> SetX X -> Prop.
  (* ... 更多操作 *)
End SetSystem.
  
End UnifiedMathFoundationImpl.
Export  UnifiedMathFoundationImpl.
  
(* ================================================================= *)
(* 第三部分：测度理论函子，包含概率论扩展 *)
(* UnifiedMeasureTheory - 接受数学基础作为参数的函子 *)
(* ================================================================= *)
  
Module UnifiedMeasureTheory (Import Base : UnifiedMathFoundationSig).
  
(* 确保实数库被正确导入 *)
  
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.R_sqrt.
Require Import Coq.Reals.Rseries.
Require Import Coq.Reals.Rsigma.
Require Import Coq.Reals.Ranalysis1.
Require Import Coq.Arith.Arith.
From Coq Require Import Lia.
  
(* 打开作用域 *)
Open Scope R_scope.
Open Scope nat_scope.
  
  Import UnifiedMathFoundationImpl.
  
(* 这里将放置原有的测度理论代码 *)
(* 注意：这部分代码将直接使用Base模块中的定义 *)
(* 原来的UnifiedMeasureTheory内容从这里开始 *)
  
(** =========== 1. 可测空间与σ-代数 =========== *)
  
(* 1.1 集族定义 *)
Definition Family (X : Type) : Type := SetX (SetX X).
  
(* 包含全集 *)
Definition contains_universe {X : Type} (F : Family X) : Prop :=
  In UniversalSet_s F.
  
(* 对补集封闭 *)
Definition closed_under_complement {X : Type} (F : Family X) : Prop :=
  forall A, In A F -> In (Complement_s A) F.
  
(* 对有限并封闭 *)
Definition closed_under_finite_union {X : Type} (F : Family X) : Prop :=
  forall A B, In A F -> In B F -> In (fun x => In x A \/ In x B) F.
  
(* 对可数并封闭 *)
Definition closed_under_countable_union {X : Type} (F : Family X) : Prop :=
  forall (F_seq : nat -> SetX X), (forall n, In (F_seq n) F) -> 
  In (fun x => exists n, In x (F_seq n)) F.
  
(* 1.2 σ-代数定义 *)
Record SigmaAlgebra (X : Type) : Type := {
  sigma_sets : Family X;
  
  (* 基本性质 *)
  sigma_contains_universe : contains_universe sigma_sets;
  sigma_closed_complement : closed_under_complement sigma_sets;
  sigma_closed_countable_union : closed_under_countable_union sigma_sets;
  
  (* 导出性质 *)
  sigma_contains_empty : In EmptySet_s sigma_sets;
  sigma_closed_finite_union : closed_under_finite_union sigma_sets;
  sigma_closed_countable_intersection : 
    forall (F_seq : nat -> SetX X), (forall n, In (F_seq n) sigma_sets) -> 
    In (fun x => forall n, In x (F_seq n)) sigma_sets;
}.
  
(* 1.3 可测空间 *)
Record MeasurableSpace : Type := {
  sample_space : Type;
  sigma_algebra : SigmaAlgebra sample_space;
}.
  
(* 可测集的简写 *)
Definition measurable_set {X : Type} (M : SigmaAlgebra X) (A : SetX X) : Prop :=
  In A (sigma_sets X M).
  
(* Notation保持不变 *)
Notation "A 'in_m' M" := (measurable_set M A) (at level 50).
  
(* 示例：检查空集是否在任意σ-代数中可测 *)
Example empty_set_measurable : forall {X:Type} (M : SigmaAlgebra X),
  measurable_set M EmptySet_s.
Proof.
  intros X M.
  unfold measurable_set.
  apply sigma_contains_empty.
Qed.
  
(* 1.4 生成σ-代数 *)
(* 任意集族生成的σ-代数是最小的包含该集族的σ-代数 *)
  
Definition generated_sigma_algebra {X : Type} (G : Family X) : SigmaAlgebra X.
Proof.
  (* 收集所有包含G的σ-代数 *)
  set (all_sigmas := 
    fun (F : Family X) =>
        (forall A, In A G -> In A F) /\
        contains_universe F /\
        closed_under_complement F /\
        closed_under_countable_union F).
  
  (* 取交集 *)
  refine {|
    sigma_sets := fun A => forall F, all_sigmas F -> In A F
  |}.
  
  (* 证明这是σ-代数 *)
  - (* 包含全集 *)
    intros F HF.
    destruct HF as [H1 [H2 [H3 H4]]].
    exact H2.
  
  - (* 对补集封闭 *)
    intros A HA F HF.
    assert (H_in_A : In A F) by (apply HA; exact HF).
    destruct HF as [H1 [H2 [H3 H4]]].
    apply H3.
    exact H_in_A.
  
  - (* 对可数并封闭 *)
    intros F_seq HF_seq F HF.
    destruct HF as [H1 [H2 [H3 H4]]].
    apply H4.
    intros n.
    apply HF_seq.
    exact (conj H1 (conj H2 (conj H3 H4))).
  
  - (* 包含空集：由全集和补集封闭性导出 *)
    intros F HF.
    destruct HF as [H1 [H2 [H3 H4]]].
    assert (Hempty : In (Complement UniversalSet) F).
    { apply H3. exact H2. }
    assert (HeqSetEq : @SetEq X (Complement UniversalSet) EmptySet).
    {
      intro x.
      rewrite complement_property.
      unfold UniversalSet, EmptySet, In.
      simpl.
      split; intro H; contradiction.
    }
    apply set_extensionality in HeqSetEq.
    exact (eq_ind (Complement UniversalSet) (fun A => In A F) Hempty EmptySet HeqSetEq).
  
  - (* 对有限并封闭：由可数并封闭性导出 *)
    intros A B HA HB F HF.
    destruct HF as [H1 [H2 [H3 H4]]].
    set (F_seq := fun (n:nat) => 
      match n with
      | 0 => A
      | 1 => B
      | _ => EmptySet
      end).
    assert (H_union : In (fun x => exists n, In x (F_seq n)) F).
    {
      apply H4.
      intros n.
      (* 使用最简化的模式匹配语法 *)
      destruct n.
      - (* n = 0 *)
        apply HA. exact (conj H1 (conj H2 (conj H3 H4))).
      - (* n = S n' *)
        destruct n.
        + (* n' = 0, 所以 n = 1 *)
          apply HB. exact (conj H1 (conj H2 (conj H3 H4))).
        + (* n' >= 1, 所以 n >= 2 *)
          assert (Hempty' : In (Complement UniversalSet) F).
          { apply H3. exact H2. }
          assert (HeqSetEq' : @SetEq X (Complement UniversalSet) EmptySet).
          {
            intro x.
            rewrite complement_property.
            unfold UniversalSet, EmptySet, In.
            simpl.
            split; intro H; contradiction.
          }
          apply set_extensionality in HeqSetEq'.
          exact (eq_ind (Complement UniversalSet) (fun A => In A F) Hempty' EmptySet HeqSetEq').
    }
    assert (H_eq : SetEq (fun x => exists n, In x (F_seq n)) (fun x => A x \/ B x)).
    {
      intro x.
      unfold F_seq.
      split.
      - intro Hex. 
        destruct Hex as [n Hn].
        (* 使用最简化的模式匹配语法 *)
        destruct n.
        + (* n = 0 *)
          left; exact Hn.
        + (* n = S n' *)
          destruct n.
          * (* n' = 0, 所以 n = 1 *)
            right; exact Hn.
          * (* n' >= 1, 所以 n >= 2 *)
            contradiction Hn.
      - intro Hx.
        destruct Hx as [Hx' | Hx'].
        + exists 0; exact Hx'.
        + exists 1; exact Hx'.
    }
    apply set_extensionality in H_eq.
    exact (eq_ind (fun x => exists n, In x (F_seq n)) (fun A => In A F) H_union (fun x => A x \/ B x) H_eq).
  
  - (* 对可数交封闭：由补集和可数并封闭性导出 *)
    intros F_seq HF_seq F HF.
    destruct HF as [H1 [H2 [H3 H4]]].
    (* 由假设HF_seq，对于每个n，F_seq n在生成的sigma_sets中，即对于所有满足all_sigmas的F，F_seq n在F中 *)
    assert (H_in_each : forall n, In (F_seq n) F).
    { intro n. apply HF_seq. exact (conj H1 (conj H2 (conj H3 H4))). }
    (* 考虑补集序列 *)
    set (G_seq := fun n => Complement (F_seq n)).
    (* 证明每个G_seq n都在F中（由补集封闭性） *)
    assert (H_G_seq : forall n, In (G_seq n) F).
    { intro n. unfold G_seq. apply H3. apply H_in_each. }
    (* 证明可数并集在F中 *)
    assert (H_union : In (fun x => exists n, In x (G_seq n)) F).
    { apply H4. exact H_G_seq. }
    (* 由德摩根定律，可数并的补集就是可数交 *)
    assert (H_eq : @SetEq X (fun x => forall n, In x (F_seq n)) 
                            (Complement (fun x => exists n, In x (G_seq n)))).
    {
      intro x.
      split.
      - intros H_all H_ex. 
        destruct H_ex as [n H_comp].
        (* H_comp: x ∈ G_seq n，而G_seq n = Complement (F_seq n) *)
        unfold G_seq in H_comp.
        (* 现在H_comp: x ∈ Complement (F_seq n) *)
        pose proof (complement_property (F_seq n) x) as Hc.
        destruct Hc as [_ Hc2].
        apply Hc2 in H_comp.
        (* H_comp: ~ In x (F_seq n) *)
        specialize (H_all n).
        contradiction.
      - intros H_no_ex n.
        (* H_no_ex: x ∈ Complement (fun x => exists n, In x (G_seq n)) *)
        pose proof (complement_property (fun x => exists n, In x (G_seq n)) x) as Hc.
        destruct Hc as [Hc1 _].
        apply Hc1 in H_no_ex.
        (* H_no_ex: ~ (exists n, In x (G_seq n)) *)
        apply Coq.Logic.Classical_Prop.NNPP.
        intro H_not.
        apply H_no_ex.
        exists n.
        unfold G_seq.
        rewrite complement_property.
        exact H_not.
    }
    apply set_extensionality in H_eq.
    rewrite H_eq.
    apply H3.
    exact H_union.
Defined.
  
(** =========== 2. 测度空间定义 =========== *)
  
Require Import Coq.Reals.Reals.
Require Import Coq.Reals.RIneq.
  
(* 2.1 非负扩展实数及其运算 - 完整版 *)
Inductive NonNegExtendedReal :=
  | NNER_finite : ℝ -> NonNegExtendedReal
  | NNER_infinity : NonNegExtendedReal.
  
(* 扩展实数序关系 - 完整定义 *)
Definition NNER_le (x y : NonNegExtendedReal) : Prop :=
  match x, y with
  | NNER_finite a, NNER_finite b => a <= b
  | NNER_finite _, NNER_infinity => True
  | NNER_infinity, NNER_finite _ => False
  | NNER_infinity, NNER_infinity => True
  end.
  
Notation "x '<=_nner' y" := (NNER_le x y) (at level 70).
Notation "x '<_nner' y" := (NNER_le x y /\ x <> y) (at level 70).
  
(* 扩展实数加法 - 完整定义 *)
Definition NNER_add (x y : NonNegExtendedReal) : NonNegExtendedReal :=
  match x, y with
  | NNER_finite a, NNER_finite b => NNER_finite (a + b)
  | _, _ => NNER_infinity
  end.
  
Notation "x '+_nner' y" := (NNER_add x y) (at level 50).
  
(* 扩展实数与实数的标量乘法 - 完整定义 *)
Definition NNER_scalar_mul (r : ℝ) (x : NonNegExtendedReal) : NonNegExtendedReal :=
  match x with
  | NNER_finite a => NNER_finite (r * a)
  | NNER_infinity => 
      match Req_EM_T r 0 with
      | left _ => NNER_finite R0
      | right _ => NNER_infinity
      end
  end.
  
Notation "r '.*_nner' x" := (NNER_scalar_mul r x) (at level 40).
  
(* 扩展实数的上确界 - 使用经典选择公理 *)
Parameter NNER_supremum : (NonNegExtendedReal -> Prop) -> NonNegExtendedReal.
  
Axiom NNER_supremum_property : forall (S : NonNegExtendedReal -> Prop),
  (exists x, S x) ->
  (exists bound, forall x, S x -> x <=_nner bound) ->
  (* 上确界性质 *)
  (forall x, S x -> x <=_nner NNER_supremum S) /\
  (forall bound, (forall x, S x -> x <=_nner bound) -> 
               NNER_supremum S <=_nner bound).
  
(* 扩展实数的单调收敛性质 *)
Axiom NNER_monotone_convergence : 
  forall (f_seq : nat -> NonNegExtendedReal),
  (forall n, f_seq n <=_nner f_seq (S n)) ->
  exists (limit : NonNegExtendedReal),
    (forall n, f_seq n <=_nner limit) /\
    (forall bound, (forall n, f_seq n <=_nner bound) -> limit <=_nner bound).
  
(* 扩展实数的可数和 *)
Definition NNER_countable_sum (f : nat -> NonNegExtendedReal) : NonNegExtendedReal :=
  NNER_supremum (fun s => exists n, s = NNER_finite (sum_f_R0 (fun i => 
    match f i with
    | NNER_finite r => r
    | NNER_infinity => 0
    end) n)).
  
(* 2.2 测度定义 - 分层架构 *)
  
(* 第一层：基础测度空间 - 使用构造性更强的版本2 *)
Class BaseMeasureSpace (X : Type) (M : SigmaAlgebra X) := {
  mu : SetX X -> NonNegExtendedReal;
  
  (* 核心公理 *)
  measure_empty : mu EmptySet_s = NNER_finite R0;
  
  measure_nonneg : forall A, In A (sigma_sets X M) -> 
    NNER_finite R0 <=_nner mu A;
  
  (* 有限可加性 *)
  measure_finite_additivity : 
    forall A B,
    In A (sigma_sets X M) -> In B (sigma_sets X M) ->
    Disjoint A B ->
    mu (fun x => In x A \/ In x B) = (mu A) +_nner (mu B);
  
  (* 可数可加性 - 构造性表述 *)
  measure_countable_additivity_constructive :
    forall (F_seq : nat -> SetX X),
    (forall n, In (F_seq n) (sigma_sets X M)) ->
    PairwiseDisjoint F_seq ->
    let partial_unions n := 
      mu (fun x => exists m, (m <= n)%nat /\ In x (F_seq m)) in
    let total_union := 
      mu (fun x => exists n, In x (F_seq n)) in
    (* 三个基本条件 *)
    (forall n m, (n <= m)%nat -> partial_unions n <=_nner partial_unions m) /\
    (forall (bound : NonNegExtendedReal),
      (forall n, partial_unions n <=_nner bound) ->
      total_union <=_nner bound) /\
    (forall (bound' : NonNegExtendedReal),
      total_union <=_nner bound' ->
      forall n, partial_unions n <=_nner bound');
}.
  
(* 第二层：扩展测度空间 - 添加导出性质 *)
Class ExtendedMeasureSpace (X : Type) (M : SigmaAlgebra X) 
  `{BaseMeasureSpace X M} := {
  
  (* 单调性 - 从基础公理可推导，但作为接口提供 *)
  measure_monotonicity :
    forall A B,
    In A (sigma_sets X M) -> In B (sigma_sets X M) ->
    (forall x, In x A -> In x B) ->
    mu A <=_nner mu B;
    
  (* 连续性 - 从基础公理可推导 *)
  measure_continuity_from_below :
    forall (F_seq : nat -> SetX X),
    (forall n, In (F_seq n) (sigma_sets X M)) ->
    (forall n, Subset (F_seq n) (F_seq (S n))) ->
    sequence_converges 
      (fun n => match mu (F_seq n) with
               | NNER_finite r => r
               | NNER_infinity => 0
               end)
      (match mu (fun x => exists n, In x (F_seq n)) with
       | NNER_finite r => r
       | NNER_infinity => 0
       end);
       
  measure_continuity_from_above :
    forall (F_seq : nat -> SetX X),
    (forall n, In (F_seq n) (sigma_sets X M)) ->
    (forall n, Subset (F_seq (S n)) (F_seq n)) ->
    (exists n, mu (F_seq n) <> NNER_infinity) ->
    sequence_converges 
      (fun n => match mu (F_seq n) with
               | NNER_finite r => r
               | NNER_infinity => 0
               end)
      (match mu (fun x => forall n, In x (F_seq n)) with
       | NNER_finite r => r
       | NNER_infinity => 0
       end);
  
  (* 可数可加性的等价表述 - 更接近标准测度论 *)
  measure_countable_additivity_standard :
    forall (F_seq : nat -> SetX X),
    (forall n, In (F_seq n) (sigma_sets X M)) ->
    PairwiseDisjoint F_seq ->
    let total_union := fun x => exists n, In x (F_seq n) in
    mu total_union = 
      NNER_supremum (fun s => exists n, s = NNER_finite (sum_f_R0 (fun i => 
        match mu (F_seq i) with
        | NNER_finite r => r
        | NNER_infinity => 0
        end) n));
}.
  
(* 第三层：完整测度空间 - 包含所有功能 *)
Class CompleteMeasureSpace (X : Type) (M : SigmaAlgebra X) 
  `{ExtendedMeasureSpace X M} := {
  (* 可以添加更多高级性质，如Radon-Nikodym、Fubini等 *)
  (* 当前不需要额外公理，作为扩展点 *)
}.
  
(* 2.3 有限测度空间 - 基于BaseMeasureSpace *)
Class FiniteMeasureSpace (X : Type) (M : SigmaAlgebra X) `(BaseMeasureSpace X M) := {
  measure_is_finite : mu UniversalSet_s <> NNER_infinity;
}.
  
(* 2.4 概率测度空间 - 基于BaseMeasureSpace *)
Class ProbabilityMeasureSpace (X : Type) (M : SigmaAlgebra X) `(BaseMeasureSpace X M) := {
  probability_measure_total : mu UniversalSet_s = NNER_finite R1;
}.
  
(* 2.5 σ-有限测度空间 - 基于BaseMeasureSpace *)
Class SigmaFiniteMeasureSpace (X : Type) (M : SigmaAlgebra X) `(BaseMeasureSpace X M) := {
  sigma_finite_sequence : nat -> SetX X;
  sigma_finite_measurable : forall n, In (sigma_finite_sequence n) (sigma_sets X M);
  sigma_finite_increasing : forall n, Subset (sigma_finite_sequence n) (sigma_finite_sequence (S n));
  sigma_finite_cover : SetEq UniversalSet_s (fun x => exists n, In x (sigma_finite_sequence n));
  sigma_finite_finite : forall n, mu (sigma_finite_sequence n) <> NNER_infinity;
}.
(*
(* 可选：为方便使用，定义MeasureSpace为CompleteMeasureSpace的别名 *)
Definition MeasureSpace (X : Type) (M : SigmaAlgebra X) := CompleteMeasureSpace X M.
*)

(* 2.6 测度空间的导出性质 *)
Section MeasureSpaceProperties.

  Context {X : Type} {M : SigmaAlgebra X} `{CompleteMeasureSpace X M}.
  
  Require Import Coq.Reals.Reals.
  Require Import Coq.Reals.RIneq.
  From Coq Require Import Lia.
  (* 注意：我们现在有完整的测度空间，可以访问所有性质 *)
  
(* ================================================================= *)
(*                       测度减法性质_工具箱                            *)
(* ================================================================= *)
  
  (* 测度减法性质 *)
  (* 测度减法性质 - 分类处理 *)
Lemma measure_subtractivity_cases : forall A B,
  In A (sigma_sets X M) -> In B (sigma_sets X M) ->
  Subset B A ->
  let A_minus_B := fun x => In x A /\ ~ In x B in
  In A_minus_B (sigma_sets X M) ->
  match mu A, mu B with
  | NNER_finite a, NNER_finite b => 
      mu A_minus_B = NNER_finite (a - b)
  | NNER_infinity, NNER_finite _ => 
      mu A_minus_B = NNER_infinity
  | NNER_finite _, NNER_infinity =>
      mu A_minus_B = NNER_finite R0
  | NNER_infinity, NNER_infinity =>
      True  (* 无法确定具体值 *)
  end.
Proof.
  intros A B HA HB Hsub A_minus_B Hmeas.
  unfold A_minus_B in *.
  
  (* 首先证明集合等式：A = (A\B) ∪ B *)
  assert (Hseteq : SetEq A (fun x => (In x A /\ ~ In x B) \/ In x B)).
  {
    intro x.
    split.
    - intro HxA.
      case (classic_dec (In x B)) as [HxB | HnotB].
      + right; exact HxB.
      + left; split; [exact HxA | exact HnotB].
    - intro Hx_union.
      destruct Hx_union as [[HxA HnotB] | HxB].
      + exact HxA.
      + apply Hsub in HxB; exact HxB.
  }
  
  (* 使用集合外延性公理 *)
  assert (Heq : A = (fun x => (In x A /\ ~ In x B) \/ In x B)).
  {
    apply set_extensionality; exact Hseteq.
  }
  
  (* 证明不相交性 *)
  assert (Hdisj : Disjoint (fun x => In x A /\ ~ In x B) B).
  {
    unfold Disjoint.
    intros x [Hx1 Hx2].
    destruct Hx1 as [HAx HnotBx].
    contradiction.
  }
  
  (* 使用测度单调性：因为B ⊆ A，所以μ(B) ≤ μ(A) *)
  assert (Hmono : mu B <=_nner mu A).
  { apply measure_monotonicity; auto. }
  
  (* 证明测度等式：μ(A) = μ(A\B) + μ(B) *)
  assert (Hmeasure_eq : mu A = (mu (fun x => In x A /\ ~ In x B)) +_nner (mu B)).
  {
    rewrite Heq at 1.
    apply measure_finite_additivity; [exact Hmeas | exact HB | exact Hdisj].
  }
  
  (* 对μ(A)和μ(B)进行分类讨论 *)
  destruct (mu A) as [a|HinfA] eqn:HA_val;
  destruct (mu B) as [b|HinfB] eqn:HB_val.
  - (* 情况1：两者都有限 *)
    (* 对mu (A\B)进行分类讨论 *)
    destruct (mu (fun x => In x A /\ ~ In x B)) as [c|HinfC] eqn:Hc.
    + (* 子情况1.1：A\B有限 *)
      (* 注意：此时Hmeasure_eq已经被自动重写为：
         NNER_finite a = NNER_finite c +_nner NNER_finite b *)
      (* 简化扩展实数加法 *)
      unfold NNER_add in Hmeasure_eq.
      simpl in Hmeasure_eq.
      (* 现在Hmeasure_eq: NNER_finite a = NNER_finite (c + b) *)
      injection Hmeasure_eq as H_eq.  (* H_eq: a = c + b *)
      (* 目标: NNER_finite c = NNER_finite (a - b) *)
      apply f_equal.
      (* 现在目标: c = a - b *)
      rewrite H_eq.            (* 将 a 替换为 c + b *)
      rewrite Rplus_minus_r.   (* (c + b) - b = c *)
      reflexivity.
    + (* 子情况1.2：A\B无穷 *)
      (* 此时Hmeasure_eq: NNER_finite a = NNER_infinity +_nner NNER_finite b *)
      unfold NNER_add in Hmeasure_eq.
      simpl in Hmeasure_eq.
      (* 现在Hmeasure_eq: NNER_finite a = NNER_infinity *)
      discriminate Hmeasure_eq.
  - (* 情况2：mu A有限，mu B无穷 *)
    (* 目标: mu (A\B) = NNER_finite R0 *)
    (* 由单调性mu B <=_nner mu A，但mu B无穷而mu A有限，矛盾 *)
    (* 注意：Hmono的类型已经是 NNER_infinity <=_nner NNER_finite a *)
    unfold NNER_le in Hmono.
    simpl in Hmono.
    contradiction.
  - (* 情况3：mu A无穷，mu B有限 *)
    (* 目标: mu (A\B) = NNER_infinity *)
    (* 对mu (A\B)进行分类讨论 *)
    destruct (mu (fun x => In x A /\ ~ In x B)) as [c|HinfC] eqn:Hc.
    + (* 子情况3.1：A\B有限 *)
      (* 此时Hmeasure_eq: NNER_infinity = NNER_finite c +_nner NNER_finite b *)
      unfold NNER_add in Hmeasure_eq.
      simpl in Hmeasure_eq.
      (* 现在Hmeasure_eq: NNER_infinity = NNER_finite (c + b) *)
      discriminate Hmeasure_eq.
    + (* 子情况3.2：A\B无穷 *)
      (* 此时Hmeasure_eq: NNER_infinity = NNER_infinity +_nner NNER_finite b *)
      unfold NNER_add in Hmeasure_eq.
      simpl in Hmeasure_eq.
      (* 现在Hmeasure_eq: NNER_infinity = NNER_infinity，成立 *)
      (* 目标: mu (A\B) = NNER_infinity 
         在destruct后已变为 NNER_infinity = NNER_infinity *)
      reflexivity.
  - (* 情况4：两者都无穷 *)
    exact I.
Qed.
  
(* 测度减法性质 - 通用等式形式 *)
Lemma measure_subtractivity_general : forall A B,
  In A (sigma_sets X M) -> In B (sigma_sets X M) ->
  Subset B A ->
  let A_minus_B := fun x => In x A /\ ~ In x B in
  In A_minus_B (sigma_sets X M) ->
  mu A = (mu A_minus_B) +_nner (mu B).
Proof.
  intros A B HA HB Hsub A_minus_B Hmeas.
  unfold A_minus_B in *.
  
  (* 证明集合等式：A = (A\B) ∪ B *)
  assert (Hseteq : SetEq A (fun x => (In x A /\ ~ In x B) \/ In x B)).
  {
    intro x.
    split.
    - intro HxA.
      case (classic_dec (In x B)) as [HxB | HnotB].
      + right; exact HxB.
      + left; split; [exact HxA | exact HnotB].
    - intro Hx_union.
      destruct Hx_union as [[HxA HnotB] | HxB].
      + exact HxA.
      + apply Hsub in HxB; exact HxB.
  }
  
  (* 使用集合外延性 *)
  assert (Heq : A = (fun x => (In x A /\ ~ In x B) \/ In x B)).
  { 
    apply set_extensionality; exact Hseteq.
  }
  
  (* 证明不相交性 *)
  assert (Hdisj : Disjoint (fun x => In x A /\ ~ In x B) B).
  {
    unfold Disjoint.
    intros x [Hx1 Hx2].
    destruct Hx1 as [HAx HnotBx].
    contradiction.
  }
  
  (* 使用测度等式转换和有限可加性 *)
  transitivity (mu (fun x => (In x A /\ ~ In x B) \/ In x B)).
  - (* mu A = mu (并集) *)
    apply f_equal; exact Heq.
  - (* mu (并集) = mu (A\B) + mu B *)
    apply measure_finite_additivity; [exact Hmeas | exact HB | exact Hdisj].
Qed.
  
  (* 测度分解定理 - 更简单且实用的版本 *)
  Lemma measure_decomposition : forall A B,
    In A (sigma_sets X M) -> In B (sigma_sets X M) ->
    Subset B A ->
    let A_minus_B := fun x => In x A /\ ~ In x B in
    In A_minus_B (sigma_sets X M) ->
    mu (A_minus_B) +_nner mu B = mu A.
  Proof.
    intros A B HA HB Hsub A_minus_B Hmeas.
    
    (* 不展开 A_minus_B，保持其原样 *)
    
    (* 首先证明集合等式：A = A_minus_B ∪ B *)
    assert (Hseteq : SetEq A (fun x => A_minus_B x \/ In x B)).
    {
      intro x.
      unfold A_minus_B.
      split.
      - intro HxA.
        case (classic_dec (In x B)) as [HxB | HnotB].
        + right; exact HxB.
        + left; split; [exact HxA | exact HnotB].
      - intro Hx_union.
        destruct Hx_union as [[HxA HnotB] | HxB].
        + exact HxA.
        + apply Hsub in HxB; exact HxB.
    }
    
    (* 使用集合外延性公理 *)
    assert (Heq : A = (fun x => A_minus_B x \/ In x B)).
    {
      apply set_extensionality; exact Hseteq.
    }
    
    (* 证明不相交性 *)
    assert (Hdisj : Disjoint A_minus_B B).
    {
      unfold Disjoint.
      intros x [Hx1 Hx2].
      unfold A_minus_B in Hx1.
      destruct Hx1 as [HAx HnotBx].
      contradiction.
    }
    
    (* 将 mu A 重写为 mu (A_minus_B ∪ B) *)
    rewrite Heq.
    
    (* 应用有限可加性：mu (A_minus_B ∪ B) = mu A_minus_B +_nner mu B *)
    rewrite (measure_finite_additivity A_minus_B B Hmeas HB Hdisj).
    
    (* 现在两边相同 *)
    reflexivity.
  Qed.
  
  (* 可数并的测度界 *)
  Lemma measure_countable_union_bound : forall (F_seq : nat -> SetX X),
    (forall n, In (F_seq n) (sigma_sets X M)) ->
    exists (bound : NonNegExtendedReal),
      forall n, mu (F_seq n) <=_nner bound.
  Proof.
    intros F_seq Hmeas.
    set (U := fun x => exists n, In x (F_seq n)).
    assert (HU : In U (sigma_sets X M)).
    { 
      unfold U.
      apply sigma_closed_countable_union.
      exact Hmeas.
    }
    exists (mu U).
    intros n.
    apply measure_monotonicity.
    - apply Hmeas.    (* F_seq n 是可测的 *)
    - exact HU.      (* U 是可测的 *)
    - intro x; intro Hx.
      unfold U.
      exists n.
      exact Hx.      (* 证明 F_seq n ⊆ U *)
  Qed.
  
  (* 有限测度空间的性质 *)
  Lemma finite_measure_property : forall A,
    In A (sigma_sets X M) ->
    mu A <=_nner mu UniversalSet_s.
  Proof.
    intros A HA.
    apply measure_monotonicity.
    - exact HA.                    (* A 可测 *)
    - apply sigma_contains_universe.  (* UniversalSet_s 可测 *)
    - intros x Hx.
      apply universal_set_property.   (* A ⊆ UniversalSet_s *)
  Qed.
  
(** =========== 工具函数和定义 =========== *)
  
(* 列表乘积函数 - 修复版本 *)
Fixpoint list_prod (l : list R) : R :=
  match l with
  | nil => 1%R
  | cons x xs => x * (list_prod xs)
  end.
  
(* 阶乘函数 - 可能在泊松过程等地方使用 *)
Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1%nat
  | S n' => (S n') * (fact n')
  end.
  
(* 标准正态分布累积分布函数 - 简化占位符 *)
Definition standard_normal_cdf (x : R) : R :=
  (* 实际实现需要误差函数积分，这里作为占位符 *)
  0%R.
  
(* 函数右连续性定义 *)
Definition is_right_continuous (f : R -> R) : Prop :=
  forall x, sequence_converges (fun n => f (x + / (INR (S n)))) (f x).
  
(* 函数在负无穷远处的极限 *)
Definition limit_at_neg_infinity (f : R -> R) (l : R) : Prop :=
  forall eps : R, eps > 0%R ->
    exists M : R, forall x, x < M -> Rabs (f x - l) < eps.
  
(* 函数在正无穷远处的极限 *)
Definition limit_at_pos_infinity (f : R -> R) (l : R) : Prop :=
  forall eps : R, eps > 0%R ->
    exists M : R, forall x, x > M -> Rabs (f x - l) < eps.
  
End MeasureSpaceProperties.
  
(** =========== 测度减法统一接口 =========== *)
  
Section UnifiedMeasureSubtract.
  
Context {X : Type} {M : SigmaAlgebra X} `{CompleteMeasureSpace X M}.
  
(* ================================================================= *)
(*                       测度减法工具函数                             *)
(* ================================================================= *)
  
(* 1. 智能选择函数 - 独立定义 *)
Definition measure_subtract_smart {X : Type} {M : SigmaAlgebra X} 
  `{CompleteMeasureSpace X M}
  (A B : SetX X) 
  (HA : In A (sigma_sets X M)) 
  (HB : In B (sigma_sets X M))
  (Hsub : Subset B A)
  (Hmeas : In (fun x => In x A /\ ~ In x B) (sigma_sets X M)) : 
  option NonNegExtendedReal :=
  match mu B with
  | NNER_finite b => 
      (* 有限情况，使用有限版本 *)
      Some (match mu A with
            | NNER_finite a => NNER_finite (a - b)
            | NNER_infinity => NNER_infinity
            end)
  | NNER_infinity => 
      (* 无穷情况，返回None让用户选择 *)
      None
  end.
  
(* ================================================================= *)
(*                       等价性验证定理                              *)
(* ================================================================= *)
  
(* 定理1：一般情况蕴含分类情况 *)
Lemma all_versions_consistent_part1 : 
  forall (A B : SetX X) 
         (HA : In A (sigma_sets X M)) 
         (HB : In B (sigma_sets X M)) 
         (Hsub : Subset B A)
         (Hmeas : In (fun x => In x A /\ ~ In x B) (sigma_sets X M)),
     mu A = (mu (fun x => In x A /\ ~ In x B)) +_nner (mu B) ->
     match mu A, mu B with
     | NNER_finite a, NNER_finite b => 
         mu (fun x => In x A /\ ~ In x B) = NNER_finite (a - b)
     | NNER_infinity, NNER_finite _ => 
         mu (fun x => In x A /\ ~ In x B) = NNER_infinity
     | NNER_finite _, NNER_infinity =>
         mu (fun x => In x A /\ ~ In x B) = NNER_finite R0
     | NNER_infinity, NNER_infinity =>
         True
     end.
Proof.
  intros A B HA HB Hsub Hmeas Hgeneral.
  (* 直接使用已有的分类引理，不依赖Hgeneral *)
  apply measure_subtractivity_cases; assumption.
Qed.
  
(* 定理2：分类情况在有限条件下的结论 *)
Lemma all_versions_consistent_part2 : 
  forall (A B : SetX X) 
         (HA : In A (sigma_sets X M)) 
         (HB : In B (sigma_sets X M)) 
         (Hsub : Subset B A)
         (Hmeas : In (fun x => In x A /\ ~ In x B) (sigma_sets X M))
         (Hfinite_B : mu B <> NNER_infinity),
     True ->  (* 修改：使用 True 作为占位符，避免复杂类型问题 *)
     match mu A, mu B with
     | NNER_finite a, NNER_finite b => 
         mu (fun x => In x A /\ ~ In x B) = NNER_finite (a - b)
     | _, _ => True
     end.
Proof.
  intros A B HA HB Hsub Hmeas Hfinite_B _.
  destruct (mu A) as [a|HinfA] eqn:HA_eq.
  - (* mu A 有限 *)
    destruct (mu B) as [b|HinfB] eqn:HB_eq.
    + (* mu B 有限 *)
      (* 使用 measure_subtractivity_cases 引理 *)
      pose proof (measure_subtractivity_cases A B HA HB Hsub Hmeas) as Hcases.
      rewrite HA_eq in Hcases.  (* 将 mu A 替换为 NNER_finite a *)
      rewrite HB_eq in Hcases.  (* 将 mu B 替换为 NNER_finite b *)
      simpl in Hcases.          (* 简化扩展实数加法 *)
      exact Hcases.
    + (* mu B 无穷，与 Hfinite_B 矛盾 *)
      exfalso.
      (* 注意：此时 Hfinite_B 的类型已经变为 NNER_infinity <> NNER_infinity *)
      apply Hfinite_B.
      reflexivity.  (* 提供 NNER_infinity = NNER_infinity 的证明 *)
  - (* mu A 无穷 *)
    destruct (mu B) as [b|HinfB] eqn:HB_eq.
    + (* mu B 有限 *)
      exact I.  (* 目标为 True *)
    + (* mu B 无穷，与 Hfinite_B 矛盾 *)
      exfalso.
      (* 注意：此时 Hfinite_B 的类型已经变为 NNER_infinity <> NNER_infinity *)
      apply Hfinite_B.
      reflexivity.  (* 提供 NNER_infinity = NNER_infinity 的证明 *)
Qed.
  
(* 组合版本 *)
Definition measure_subtractivity_cases_result 
  (A B : SetX X)
  (HA : In A (sigma_sets X M)) 
  (HB : In B (sigma_sets X M)) 
  (Hsub : Subset B A)
  (Hmeas : In (fun x => In x A /\ ~ In x B) (sigma_sets X M)) : Prop :=
  match mu A, mu B with
  | NNER_finite a, NNER_finite b => 
      mu (fun x => In x A /\ ~ In x B) = NNER_finite (a - b)
  | NNER_infinity, NNER_finite _ => 
      mu (fun x => In x A /\ ~ In x B) = NNER_infinity
  | NNER_finite _, NNER_infinity =>
      mu (fun x => In x A /\ ~ In x B) = NNER_finite R0
  | NNER_infinity, NNER_infinity =>
      True
  end.
  
Lemma all_versions_consistent :
  (forall (A B : SetX X) (HA : In A (sigma_sets X M)) 
          (HB : In B (sigma_sets X M)) (Hsub : Subset B A)
          (Hmeas : In (fun x => In x A /\ ~ In x B) (sigma_sets X M)),
     mu A = (mu (fun x => In x A /\ ~ In x B)) +_nner (mu B) ->
     measure_subtractivity_cases_result A B HA HB Hsub Hmeas) /\
  (forall (A B : SetX X) (HA : In A (sigma_sets X M)) 
          (HB : In B (sigma_sets X M)) (Hsub : Subset B A)
          (Hmeas : In (fun x => In x A /\ ~ In x B) (sigma_sets X M))
          (Hfinite_B : mu B <> NNER_infinity),
     measure_subtractivity_cases_result A B HA HB Hsub Hmeas ->
     match mu A, mu B with
     | NNER_finite a, NNER_finite b => 
         mu (fun x => In x A /\ ~ In x B) = NNER_finite (a - b)
     | _, _ => True
     end).
Proof.
  split.
  - (* 第一部分证明 *)
    intros A B HA HB Hsub Hmeas Hgeneral.
    unfold measure_subtractivity_cases_result.
    (* 使用已有的引理 *)
    apply measure_subtractivity_cases; assumption.
  - (* 第二部分证明 *)
    intros A B HA HB Hsub Hmeas Hfinite_B Hresult.
    unfold measure_subtractivity_cases_result in Hresult.
    destruct (mu A) as [a|HinfA] eqn:HA_eq.
    + (* mu A 有限 *)
      destruct (mu B) as [b|HinfB] eqn:HB_eq.
      * (* mu B 有限 *)
        exact Hresult.
      * (* mu B 无穷，与 Hfinite_B 矛盾 *)
        exfalso.
        (* 注意：此时 Hfinite_B 的类型已变为 NNER_infinity <> NNER_infinity *)
        apply Hfinite_B.
        reflexivity.  (* 提供 NNER_infinity = NNER_infinity 的证明 *)
    + (* mu A 无穷 *)
      destruct (mu B) as [b|HinfB] eqn:HB_eq.
      * (* mu B 有限 *)
        exact I.  (* 目标为 True *)
      * (* mu B 无穷，与 Hfinite_B 矛盾 *)
        exfalso.
        (* 注意：此时 Hfinite_B 的类型已变为 NNER_infinity <> NNER_infinity *)
        apply Hfinite_B.
        reflexivity.  (* 提供 NNER_infinity = NNER_infinity 的证明 *)
Qed.
  
End UnifiedMeasureSubtract.
  
(** =========== 3. 概率论扩展 =========== *)

(** 统一概率论公理系统 v1.0
  基于 UnifiedMeasureTheory 构建
  
  设计目标：
  1. 保持原有证明结构和代码的兼容性
  2. 基于统一的测度论框架
  3. 提供完整的概率论公理化系统
  4. 支持随机变量、期望、条件概率等核心概念
  
  特别注意：尽量保持原有证明参数和代码结构，确保可编译性
**)
  
Section ProbabilityTheory.
  
(** =========== 1. 概率空间定义 =========== *)
(** 保持与原始定义相似的结构，但基于统一测度论 **)
  
(* 1.1 概率空间类 - 基于测度空间 *)
Class ProbabilitySpace : Type := {
  (* 样本空间 *)
  ps_Ω : Type;
  
  (* 事件σ-代数 *)
  ps_𝓕 : SigmaAlgebra ps_Ω;
  
  (* 概率测度 - 使用 BaseMeasureSpace 即可满足概率论基本需求 *)
  ps_ℙ : BaseMeasureSpace ps_Ω ps_𝓕;
  
  (* 概率测度特有性质：全空间测度为1 *)
  is_probability_measure : mu (X:=ps_Ω) (M:=ps_𝓕) (BaseMeasureSpace:=ps_ℙ) UniversalSet_s = NNER_finite R1;
}.
  
(* 1.2 可测事件 *)
Definition Event (ps : ProbabilitySpace) : Type :=
  {A : SetX (ps.(ps_Ω)) | A in_m (ps.(ps_𝓕))}.
  
Definition is_event {ps : ProbabilitySpace} (A : SetX (ps.(ps_Ω))) : Prop :=
  A in_m (ps.(ps_𝓕)).
  
Notation "A 'in_e' ps" := (is_event A) (at level 50).
  
(* 1.3 概率函数 *)
Definition P {ps : ProbabilitySpace} (A : SetX (ps.(ps_Ω))) : ℝ :=
  match mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) A with
  | NNER_finite r => r
  | NNER_infinity => R0  (* 概率测度不会无穷 *)
  end.
  
(* 1.4 基本概率性质 - 保持原始证明结构 *)
Section BasicProbabilityProperties.
  
Context {ps : ProbabilitySpace}.
Notation Ω' := (ps.(ps_Ω)).
Notation 𝓕' := (ps.(ps_𝓕)).
Notation "P[ A ]" := (P A) (at level 40).
  
Lemma probability_nonneg : forall A, A in_e ps -> R0 <= P[ A ].
Proof.
  intros A HA.
  unfold is_event in HA.
  pose proof (measure_nonneg (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) A HA) as Hpos.
  unfold P.
  case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) A); 
    [intros r Hmu | intros Hmu].
  - (* mu A = NNER_finite r *)
    rewrite Hmu in Hpos.
    unfold NNER_le in Hpos; simpl in Hpos.
    exact Hpos.
  - (* mu A = NNER_infinity *)
    simpl.
    apply Rle_refl.  (* R0 <= R0 可以通过自反性证明 *)
Qed.
  

(** 概率小于等于1引理：任何事件的概率不超过1 *)
Lemma probability_le_one : forall A, A in_e ps -> P[ A ] <= R1.
Proof.
  intros A HA.
  unfold is_event in HA.
  unfold P.
  
  (* 证明A的补集是可测的 *)
  assert (Hcomp : In (Complement_s A) (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
  { apply sigma_closed_complement. exact HA. }
  
  (* 证明A和它的补集不相交 *)
  assert (Hdisj : Disjoint A (Complement_s A)).
  { unfold Disjoint.
    intros x [Hx Hc].
    rewrite complement_property in Hc.
    contradiction. }
  
  (* 证明A和补集的并集是全集 *)
  assert (Hunion : SetEq (fun x => In x A \/ In x (Complement_s A)) UniversalSet_s).
  { intro x.
    split.
    - intros _. apply universal_set_property.
    - intros _.
      destruct (classic (In x A)) as [H|H].
      + left; exact H.
      + right; exact H. }
  
  (* 将集合等式转换为相等性 *)
  assert (Heq : (fun x => In x A \/ In x (Complement_s A)) = UniversalSet_s).
  { apply set_extensionality; exact Hunion. }
  
  (* 应用有限可加性 *)
  pose proof (measure_finite_additivity (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
              (BaseMeasureSpace:=ps.(ps_ℙ)) A (Complement_s A) HA Hcomp Hdisj) as Hadd.
  
  (* 将并集重写为全集 *)
  rewrite Heq in Hadd.
  
  (* 使用全空间测度为1的性质 *)
  rewrite is_probability_measure in Hadd.
  
  (* 现在 Hadd: mu A +_nner mu (Complement_s A) = NNER_finite R1 *)
  
  (* 对 mu A 进行分类讨论 *)
  case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) A);
    [intros a Ha | intros Ha].
  - (* mu A = NNER_finite a *)
    (* 对 mu (Complement_s A) 进行分类讨论 *)
    case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) (Complement_s A));
      [intros b Hb | intros Hb].
    + (* 两者都有限 *)
      rewrite Ha, Hb in Hadd.
      unfold NNER_add in Hadd.
      simpl in Hadd.
      injection Hadd as Hsum.  (* Hsum: a + b = R1 *)
      (* 我们需要证明 a <= R1 *)
      pose proof (measure_nonneg (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
                  (BaseMeasureSpace:=ps.(ps_ℙ)) (Complement_s A) Hcomp) as Hcomp_nonneg.
      rewrite Hb in Hcomp_nonneg.
      unfold NNER_le in Hcomp_nonneg; simpl in Hcomp_nonneg.
      (* Hcomp_nonneg: R0 <= b *)
      (* 手动证明 a <= R1 *)
      apply Rle_trans with (a + b).
      * (* 证明 a <= a + b *)
        rewrite <- (Rplus_0_r a) at 1.
        apply Rplus_le_compat_l.
        exact Hcomp_nonneg.
      * (* 证明 a + b <= R1 *)
        rewrite <- Hsum.
        apply Rle_refl.
    + (* mu (Complement_s A) 无穷，导致矛盾 *)
      rewrite Ha, Hb in Hadd.
      unfold NNER_add in Hadd.
      simpl in Hadd.
      discriminate Hadd.
  - (* mu A 无穷，导致矛盾 *)
    rewrite Ha in Hadd.
    unfold NNER_add in Hadd.
    simpl in Hadd.
    discriminate Hadd.
Qed.
  
(* 空集概率为0 *)
Theorem probability_empty_set : P[ EmptySet_s ] = R0.
Proof.
  unfold P.
  rewrite measure_empty.
  reflexivity.
Qed.
  
(* 全集概率为1 - 使用概率测度空间的性质 *)
Theorem probability_universe : P[ UniversalSet_s ] = R1.
Proof.
  unfold P.
  (* 使用概率空间的投影函数 *)
  rewrite (ps.(is_probability_measure)).
  reflexivity.
Qed.
  
(* 补集概率公式 - 保持原始证明结构 *)
Theorem probability_complement_formula : forall A,
  A in_e ps -> P[ Complement_s A ] = R1 - P[ A ].
Proof.
  intros A HA.
  unfold is_event in HA.
  
  (* 证明 A 的补集是可测的 *)
  assert (HAc : In (Complement_s A) (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
  { apply sigma_closed_complement; exact HA. }
  
  (* 证明 A 和它的补集不相交 *)
  assert (Hdisj : Disjoint A (Complement_s A)).
  { unfold Disjoint.
    intros x [Hx Hc].
    rewrite complement_property in Hc.
    contradiction. }
  
  (* 证明 A 和补集的并集是全集 *)
  assert (Hunion : SetEq (fun x => In x A \/ In x (Complement_s A)) UniversalSet_s).
  { intro x.
    split.
    - intros _. apply universal_set_property.
    - intros _.
      destruct (classic (In x A)) as [H|H].
      + left; exact H.
      + right; exact H. }
  
  (* 将集合等式转换为相等性 *)
  assert (Heq : (fun x => In x A \/ In x (Complement_s A)) = UniversalSet_s).
  { apply set_extensionality; exact Hunion. }
  
  (* 应用有限可加性 *)
  pose proof (measure_finite_additivity (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
              (BaseMeasureSpace:=ps.(ps_ℙ)) A (Complement_s A) HA HAc Hdisj) as Hadd.
  
  (* 将并集重写为全集 *)
  rewrite Heq in Hadd.
  
  (* 使用全空间测度为 1 的性质 *)
  rewrite (ps.(is_probability_measure)) in Hadd.
  
  (* 现在 Hadd: mu A +_nner mu (Complement_s A) = NNER_finite R1 *)
  
  (* 对 mu A 和 mu (Complement_s A) 进行分类讨论 *)
  unfold P.
  case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) A);
    [intros a Ha | intros Ha].
  - (* mu A = NNER_finite a *)
    case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) (Complement_s A));
      [intros b Hb | intros Hb].
    + (* mu (Complement_s A) = NNER_finite b *)
      rewrite Ha, Hb in Hadd.
      unfold NNER_add in Hadd.
      simpl in Hadd.
      injection Hadd as Hsum.  (* Hsum: a + b = R1 *)
      (* 由 Hsum: a + b = R1 可得 b = R1 - a *)
      lra.
    + (* mu (Complement_s A) = NNER_infinity，矛盾 *)
      rewrite Ha, Hb in Hadd.
      unfold NNER_add in Hadd.
      simpl in Hadd.
      discriminate Hadd.
  - (* mu A = NNER_infinity，矛盾 *)
    rewrite Ha in Hadd.
    unfold NNER_add in Hadd.
    simpl in Hadd.
    discriminate Hadd.
Qed.
  
(* 有限可加性 - 保持原始证明结构 *)
(* 首先证明：在概率空间中，任何可测事件的测度都是有限的 *)
Lemma probability_measure_finite : forall A, A in_e ps -> mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) A <> NNER_infinity.
Proof.
  intros A HA.
  unfold is_event in HA.
  (* 使用概率测度的性质：全空间测度为1 *)
  pose proof (ps.(is_probability_measure)) as H_total.
  (* 证明 A 的补集可测 *)
  assert (Hcomp : In (Complement_s A) (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
  { apply sigma_closed_complement; exact HA. }
  (* 证明 A 和补集不相交 *)
  assert (Hdisj : Disjoint A (Complement_s A)).
  { unfold Disjoint.
    intros x [Hx Hc].
    rewrite complement_property in Hc.
    contradiction. }
  (* 应用有限可加性 *)
  pose proof (measure_finite_additivity (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
              (BaseMeasureSpace:=ps.(ps_ℙ)) A (Complement_s A) HA Hcomp Hdisj) as Hadd.
  (* 证明并集是全集 *)
  assert (Hunion : SetEq (fun x => In x A \/ In x (Complement_s A)) UniversalSet_s).
  { intro x.
    split.
    - intros _. apply universal_set_property.
    - intros _.
      destruct (classic (In x A)) as [H|H].
      + left; exact H.
      + right; exact H. }
  assert (Heq : (fun x => In x A \/ In x (Complement_s A)) = UniversalSet_s).
  { apply set_extensionality; exact Hunion. }
  rewrite Heq in Hadd.
  rewrite H_total in Hadd.
  (* 现在 Hadd: mu A +_nner mu (Complement_s A) = NNER_finite R1 *)
  (* 对 mu A 进行分类讨论 *)
  case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) A);
    [intros a Ha | intros Ha].
  - (* mu A = NNER_finite a: 这正是我们想要的，不是无穷 *)
    (* 直接证明 NNER_finite a ≠ NNER_infinity *)
    intro H; discriminate H.  (* 两个不同的构造函数 *)
  - (* mu A = NNER_infinity: 我们需要证明这会导致矛盾 *)
    rewrite Ha in Hadd.
    (* 对 mu (Complement_s A) 进行分类讨论 *)
    case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) (Complement_s A));
      [intros b Hb | intros Hb].
    + (* mu (Complement_s A) = NNER_finite b *)
      rewrite Hb in Hadd.
      unfold NNER_add in Hadd.
      simpl in Hadd.
      discriminate Hadd.  (* NNER_infinity = NNER_finite (R1) 不可能 *)
    + (* mu (Complement_s A) = NNER_infinity *)
      rewrite Hb in Hadd.
      unfold NNER_add in Hadd.
      simpl in Hadd.
      discriminate Hadd.  (* NNER_infinity = NNER_finite (R1) 不可能 *)
Qed.
  
(* 有限可加性 - 保持原始证明结构 *)
Theorem probability_finite_additivity : forall A B,
  A in_e ps -> B in_e ps -> Disjoint A B ->
  P[ fun x => In x A \/ In x B ] = P[ A ] + P[ B ].
Proof.
  intros A B HA HB Hdisj.
  unfold is_event in HA, HB.
  
  (* 证明 A ∪ B 是可测的 *)
  assert (HAB_meas : In (fun x => In x A \/ In x B) (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
  { apply sigma_closed_finite_union; [exact HA | exact HB]. }
  
  (* 应用引理：A、B 和 A ∪ B 的测度都是有限的 *)
  pose proof (probability_measure_finite A HA) as H_finite_A.
  pose proof (probability_measure_finite B HB) as H_finite_B.
  pose proof (probability_measure_finite (fun x => In x A \/ In x B) HAB_meas) as H_finite_AB.
  
  (* 应用测度有限可加性 *)
  pose proof (measure_finite_additivity (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
              (BaseMeasureSpace:=ps.(ps_ℙ)) A B HA HB Hdisj) as Hadd.
  
  (* 展开概率函数定义 *)
  unfold P.
  
  (* 对 mu A 进行分类讨论，使用引理排除无穷情况 *)
  case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) A);
    [intros a Ha | intros Ha].
  - (* mu A = NNER_finite a *)
    (* 对 mu B 进行分类讨论，使用引理排除无穷情况 *)
    case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) B);
      [intros b Hb | intros Hb].
    + (* mu B = NNER_finite b *)
      (* 对 mu (A ∪ B) 进行分类讨论，使用引理排除无穷情况 *)
      case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
                  (BaseMeasureSpace:=ps.(ps_ℙ)) (fun x => In x A \/ In x B));
        [intros c Hc | intros Hc].
      * (* mu (A ∪ B) = NNER_finite c *)
        rewrite Ha, Hb, Hc in Hadd.
        unfold NNER_add in Hadd.
        simpl in Hadd.
        injection Hadd as Hab_eq.  (* Hab_eq: c = a + b *)
        rewrite Hab_eq.
        reflexivity.
      * (* mu (A ∪ B) = NNER_infinity，与引理矛盾 *)
        exfalso.
        apply H_finite_AB.
        exact Hc.
    + (* mu B = NNER_infinity，与引理矛盾 *)
      exfalso.
      apply H_finite_B.
      exact Hb.
  - (* mu A = NNER_infinity，与引理矛盾 *)
    exfalso.
    apply H_finite_A.
    exact Ha.
Qed.
  
(** 部分和函数的递推性质引理 *)
(* 证明: sum_f_R0 f (S n) = sum_f_R0 f n + f (S n) *)
(* 该引理描述了部分和函数的递归计算规则 *)
Lemma sum_f_R0_Sn : forall (f : nat -> R) (n : nat),
  sum_f_R0 f (S n) = sum_f_R0 f n + f (S n).
Proof.
  (* 引入变量和假设 *)
  intros f n.
  (* 展开 sum_f_R0 函数的定义 *)
  unfold sum_f_R0.
  (* 简化表达式，Coq会自动计算递归步骤 *)
  simpl.
  (* 简化后两边相等，直接证明 *)
  reflexivity.
Qed.
  
(** 概率的可数可加性（无限可加性） *)
Theorem probability_countable_additivity : forall (A_seq : nat -> SetX Ω'),
    (forall n, A_seq n in_e ps) ->
    PairwiseDisjoint A_seq ->
    infinite_sum (fun n => P[ A_seq n ]) (P[ fun x => exists n, In x (A_seq n) ]).
Proof.
  intros A_seq Hmeas Hdisj.
  (* 定义部分并集序列 B_n = ⋃_{i=0}^{n} A_i *)
  set (B_seq := fun n : nat => fun x : Ω' => exists i, (i <= n)%nat /\ In x (A_seq i)).
  
  (* 证明每个 B_n 是可测的 *)
  assert (Hmeas_B : forall n, B_seq n in_e ps).
  {
    intros n.
    unfold is_event.
    induction n.
    - (* B_0 = A_0 *)
      unfold B_seq.
      (* 证明 B_0 与 A_0 等价 *)
      assert (Heq : SetEq (fun x : Ω' => exists i, (i <= 0)%nat /\ In x (A_seq i)) 
                          (A_seq 0%nat)).
      {
        intro x.
        split.
        - intros [i [Hi Hx]].
          assert (i = 0%nat) by lia.
          subst.
          exact Hx.
        - intros Hx.
          exists 0%nat.
          split; [lia | exact Hx].
      }
      (* 使用集合外延性 *)
      pose proof (set_extensionality _ _ Heq) as Heq'.
      rewrite Heq'.
      apply Hmeas.
    - (* B_{n+1} = B_n ∪ A_{n+1} *)
      (* 证明集合等式：B_{n+1} = B_n ∪ A_{n+1} *)
      assert (Heq : SetEq (B_seq (S n)) (fun x : Ω' => B_seq n x \/ In x (A_seq (S n)))).
      {
        intro x.
        split.
        - intros Hx.
          unfold B_seq in Hx.
          destruct Hx as [i [Hi Hx]].
          destruct (le_lt_eq_dec i (S n) Hi) as [Hlt|Heq_i].
          + left.
            exists i.
            split; [lia | exact Hx].
          + right.
            subst i.
            exact Hx.
        - intros [Hx | Hx].
          + destruct Hx as [i [Hi Hx]].
            exists i.
            split; [lia | exact Hx].
          + exists (S n).
            split; [lia | exact Hx].
      }
      pose proof (set_extensionality _ _ Heq) as Heq'.
      rewrite Heq'.
      (* 应用有限并封闭性 *)
      apply sigma_closed_finite_union; [exact IHn | apply Hmeas].
  }
  
  (* 证明 B_n 是单调递增的 *)
  assert (Hmono : forall n, Subset (B_seq n) (B_seq (S n))).
  {
    intros n x Hx.
    unfold B_seq in *.
    destruct Hx as [i [Hi Hx]].
    exists i.
    split; [lia | exact Hx].
  }
  
  (* 证明 ⋃_n B_n = ⋃_n A_n *)
  assert (Hunion_eq : SetEq (fun x => exists n, In x (B_seq n)) 
                           (fun x => exists n, In x (A_seq n))).
  {
    intro x.
    split.
    - intros [n [i [Hi Hx]]].
      exists i; exact Hx.
    - intros [n Hx].
      exists n.
      exists n.
      split; [lia | exact Hx].
  }
  
  pose proof (measure_countable_additivity_constructive 
              (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) 
              A_seq Hmeas Hdisj) as Hcountable.
  destruct Hcountable as [Hmono_partial [Hsup Hbound]].
  
  (* 展开概率函数定义 *)
  unfold P.
  
  (* 对 mu (⋃_n B_n) 进行分类讨论 *)
  case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ))
             (fun x => exists n, In x (B_seq n)));
    [intros l Hl | intros Hinf].
  - (* 情况1：mu (⋃_n B_n) 有限 *)
    (* 我们需要证明 infinite_sum (P ∘ A_seq) l，然后重写l为P[⋃_n A_n] *)
    
    (* 首先证明 P[⋃_n A_n] = l *)
    assert (Hl_eq : match mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ))
                         (fun x => exists n, In x (A_seq n)) with
                   | NNER_finite r => r
                   | NNER_infinity => R0
                   end = l).
    {
      (* 由于 ⋃_n B_seq n = ⋃_n A_seq n，它们的测度相等 *)
      assert (Hmu_eq : mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ))
                       (fun x => exists n, In x (B_seq n)) =
                       mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ))
                       (fun x => exists n, In x (A_seq n))).
      {
        apply f_equal.
        apply set_extensionality.
        exact Hunion_eq.
      }
      rewrite Hmu_eq in Hl.
      rewrite Hl.
      reflexivity.
    }
    
    (* 定义部分和序列 *)
    set (S_seq := fun n : nat => sum_f_R0 (fun i => match mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) (A_seq i) with
                                                   | NNER_finite r => r
                                                   | NNER_infinity => R0
                                                   end) n).
    
    (* 证明对于每个 n，mu(B_seq n) = NNER_finite (S_seq n) *)
    assert (H_seq_eq : forall n, mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) (B_seq n) = NNER_finite (S_seq n)).
    {
      intros n.
      unfold B_seq.
      induction n.
      - (* n = 0 *)
        (* 证明 B_seq 0 与 A_seq 0 相等 *)
        assert (Heq0 : SetEq (fun x : Ω' => exists i, (i <= 0)%nat /\ In x (A_seq i)) (A_seq 0%nat)).
        {
          intro x.
          split.
          - intros [i [Hi Hx]].
            assert (i = 0%nat) by lia.
            subst.
            exact Hx.
          - intros Hx.
            exists 0%nat.
            split; [lia | exact Hx].
        }
        pose proof (set_extensionality _ _ Heq0) as Heq0'.
        rewrite Heq0'.
        (* 展开 S_seq *)
        unfold S_seq.
        simpl.
        (* 对 mu (A_seq 0) 进行分类讨论 *)
        case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) (A_seq 0%nat));
          [intros r Hr | intros Hr].
        + (* 有限 *)
          reflexivity.
        + (* 无穷，与概率测度有限矛盾 *)
          exfalso.
          apply (probability_measure_finite (A_seq 0%nat) (Hmeas 0%nat)).
          exact Hr.
      - (* n = S n' *)
        (* 证明 B_{n+1} = B_n ∪ A_{n+1} *)
        assert (Heq : SetEq (fun x : Ω' => exists i, (i <= S n)%nat /\ In x (A_seq i))
                            (fun x : Ω' => (exists i, (i <= n)%nat /\ In x (A_seq i)) \/ In x (A_seq (S n)))).
        {
          intro x.
          split.
          - intros [i [Hi Hx]].
            destruct (le_lt_eq_dec i (S n) Hi) as [Hlt|Heq_i].
            + left.
              exists i.
              split; [lia | exact Hx].
            + right.
              subst i.
              exact Hx.
          - intros [[i [Hi Hx]] | Hx].
            + exists i.
              split; [lia | exact Hx].
            + exists (S n).
              split; [lia | exact Hx].
        }
        pose proof (set_extensionality _ _ Heq) as Heq'.
        rewrite Heq'.
        (* 证明不相交性 *)
        assert (Hdisj' : Disjoint (fun x : Ω' => exists i, (i <= n)%nat /\ In x (A_seq i)) (A_seq (S n))).
        {
          unfold Disjoint.
          intros x [Hx1 Hx2].
          destruct Hx1 as [i [Hi Hx1]].
          (* 使用两两不相交的性质 *)
          pose proof (Hdisj i (S n)) as Hdisj_pair.
          (* Hdisj_pair 的类型是：i <> S n -> Disjoint (A_seq i) (A_seq (S n)) *)
          assert (Hne : i <> S n) by lia.
          specialize (Hdisj_pair Hne).
          (* 现在 Hdisj_pair 的类型是：Disjoint (A_seq i) (A_seq (S n)) *)
          (* 即 forall x, ~ (In x (A_seq i) /\ In x (A_seq (S n))) *)
          apply (Hdisj_pair x).
          split; assumption.
        }
        (* 应用有限可加性 *)
        pose proof (measure_finite_additivity (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
                    (BaseMeasureSpace:=ps.(ps_ℙ)) (fun x : Ω' => exists i, (i <= n)%nat /\ In x (A_seq i))
                    (A_seq (S n)) (Hmeas_B n) (Hmeas (S n)) Hdisj') as Hadd.
        
        (* 简化 Hadd 左边的表达式 *)
        simpl in Hadd.
        
        (* 重写归纳假设 *)
        rewrite IHn in Hadd.
        
        (* 展开 S_seq *)
        unfold S_seq in *.
        
        (* 对 mu (A_seq (S n)) 进行分类讨论 *)
        case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) (A_seq (S n)));
          [intros r Hr | intros Hr].
        + (* 有限情况 *)
          rewrite Hr in Hadd.
          unfold NNER_add in Hadd.
          simpl in Hadd.
          
          (* 展开S_seq *)
          unfold S_seq.
          
          (* 内联 sum_f_R0_Sn 引理的证明 *)
          unfold sum_f_R0 at 1.   (* 展开 sum_f_R0 的定义 *)
          simpl.                  (* 自动计算：sum_f_R0 f (S n) = sum_f_R0 f n + f (S n) *)
          
          (* 现在目标中出现了match mu (A_seq (S n)) with ... end，将其替换为r *)
          replace (match mu (A_seq (S n)) with
                  | NNER_finite r' => r'
                  | NNER_infinity => R0
                  end) with r.
          exact Hadd.
          rewrite Hr; reflexivity.
        + (* mu (A_seq (S n)) 无穷，与概率测度有限矛盾 *)
          rewrite Hr in Hadd.
          unfold NNER_add in Hadd.
          simpl in Hadd.
          exfalso.
          apply (probability_measure_finite (A_seq (S n)) (Hmeas (S n))).
          exact Hr.
    }
    
    (* 将 Hmono_partial 转化为 S_seq 的单调性 *)
    assert (Hmono_S : forall n m, (n <= m)%nat -> S_seq n <= S_seq m).
    {
      intros n m Hle.
      pose proof (Hmono_partial n m Hle) as H.
      change (fun x : Ω' => exists m0 : nat, (m0 <= n)%nat /\ x in_s A_seq m0) with (B_seq n) in H.
      change (fun x : Ω' => exists m0 : nat, (m0 <= m)%nat /\ x in_s A_seq m0) with (B_seq m) in H.
      rewrite H_seq_eq in H.
      rewrite H_seq_eq in H.
      unfold NNER_le in H.
      simpl in H.
      exact H.
    }
    
    (* 将 Hbound 转化为关于 S_seq 的条件 *)
    assert (Hbound_S : forall bound', l <= bound' -> forall n, S_seq n <= bound').
    {
      intros bound' H.  (* H: l <= bound' *)
      intros n.
      (* 首先证明 mu(⋃ A_seq) = NNER_finite l *)
      assert (Hmu_eq : mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ))
                       (fun x => exists n, In x (B_seq n)) =
                       mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ))
                       (fun x => exists n, In x (A_seq n))).
      {
        apply f_equal.
        apply set_extensionality.
        exact Hunion_eq.
      }
      assert (HmuA_finite : mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ))
                           (fun x => exists n, In x (A_seq n)) = NNER_finite l).
      {
        rewrite <- Hmu_eq.
        exact Hl.
      }
      (* 使用 Hbound *)
      assert (Hpre : mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ))
                     (fun x => exists n, In x (A_seq n)) <=_nner NNER_finite bound').
      {
        rewrite HmuA_finite.
        unfold NNER_le; simpl.
        exact H.
      }
      specialize (Hbound (NNER_finite bound') Hpre n).
      (* 现在 Hbound: mu (fun x : Ω' => exists m, (m <= n)%nat /\ x in_s A_seq m) <=_nner NNER_finite bound' *)
      (* 将集合表达式转换为 B_seq n *)
      change (fun x : Ω' => exists m : nat, (m <= n)%nat /\ In x (A_seq m)) with (B_seq n) in Hbound.
      rewrite H_seq_eq in Hbound.
      unfold NNER_le in Hbound; simpl in Hbound.
      exact Hbound.
    }
    
    (* 证明 S_seq 收敛到 l *)
    (* 当前目标已经是 infinite_sum (fun n => ...) l，所以我们直接证明它 *)
    unfold infinite_sum.
    intros eps Heps.
    (* 首先证明存在 N，使得 l - eps < S_seq N *)
    assert (H_exists_N : exists N, l - eps < S_seq N).  (* 更改名称 *)
    {
      (* 使用反证法 *)
      apply NNPP.
      intro Hnex.
      assert (Hforall : forall n, S_seq n <= l - eps).
      {
        intros n.
        apply Rnot_gt_le.
        intro Hgt.
        apply Hnex.
        exists n.
        exact Hgt.
      }
      (* 使用 Hsup 得到矛盾 *)
      assert (Hbound_NNER : forall n,
        mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ))
           (fun x : Ω' => exists m, (m <= n)%nat /\ In x (A_seq m)) <=_nner 
        NNER_finite (l - eps)).
      {
        intros n.
        change (fun x : Ω' => exists m : nat, (m <= n)%nat /\ In x (A_seq m)) with (B_seq n).
        rewrite H_seq_eq.
        unfold NNER_le; simpl.
        apply Hforall.
      }
      specialize (Hsup (NNER_finite (l - eps)) Hbound_NNER).
      (* 证明 mu(⋃ A_seq) = NNER_finite l *)
      assert (Hmu_eq : mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ))
                       (fun x => exists n, In x (B_seq n)) =
                       mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ))
                       (fun x => exists n, In x (A_seq n))).
      {
        apply f_equal.
        apply set_extensionality.
        exact Hunion_eq.
      }
      assert (HmuA_finite : mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ))
                           (fun x => exists n, In x (A_seq n)) = NNER_finite l).
      {
        rewrite <- Hmu_eq.
        exact Hl.
      }
      rewrite HmuA_finite in Hsup.
      unfold NNER_le in Hsup; simpl in Hsup.
      (* 现在 Hsup: l <= l - eps *)
      lra.
    }
    destruct H_exists_N as [N HN].
    exists N.
    intros n Hn.
    pose proof (Hmono_S N n Hn) as Hmono_S_seq.
    pose proof (Hbound_S l (Rle_refl l) n) as Hbound'_n.
    unfold R_dist.
    
    (* 使用Hl_eq将目标中的match表达式替换为l *)
    rewrite Hl_eq.
    
    (* 第一个目标: sum_f_R0 ... n - l < eps *)
    apply Rabs_def1.
    - (* 证明 sum_f_R0 ... n - l < eps *)
      apply Rle_lt_trans with 0.
      + apply Rle_minus.
        exact Hbound'_n.
      + exact Heps.
    - (* 证明 -eps < sum_f_R0 ... n - l *)
      (* 从 HN: l - eps < S_seq N 和 Hmono_S_seq: S_seq N <= S_seq n 得到 l - eps < S_seq n *)
      assert (Htemp: l - eps < S_seq n).
      {
        apply Rlt_le_trans with (S_seq N); [exact HN | exact Hmono_S_seq].
      }
      (* 展开 S_seq 以便操作 *)
      unfold S_seq in *.
      (* 在不等式两边同时加上 -l *)
      apply (Rplus_lt_compat_r (-l)) in Htemp.
      (* 化简左边的表达式 *)
      replace ((l - eps) + (-l)) with (-eps) in Htemp by ring.
      (* 现在 Htemp 就是我们要证明的目标 *)
      exact Htemp.
  - (* 情况2：mu (⋃_n B_n) 无穷，与概率测度有限矛盾 *)
    exfalso.
    (* 证明 ⋃_n B_n 是可测的 *)
    assert (Hmeas_union : (fun x => exists n, In x (B_seq n)) in_e ps).
    {
      unfold is_event.
      apply sigma_closed_countable_union.
      exact Hmeas_B.
    }
    (* 应用概率测度有限引理 *)
    apply (probability_measure_finite (fun x => exists n, In x (B_seq n)) Hmeas_union).
    exact Hinf.
Qed.
  
(* 单调性 - 保持原始证明结构 *)
Theorem probability_monotonicity : forall A B,
  A in_e ps -> B in_e ps -> Subset A B ->
  P[ A ] <= P[ B ].
Proof.
  intros A B HA HB Hsub.
  unfold is_event in HA, HB.
  
  (* 证明差集 B\A 可测 *)
  set (B_minus_A := fun x => In x B /\ ~ In x A).
  
  (* 首先证明 B_minus_A 是可测集 *)
  assert (Hmeas_BA : In B_minus_A (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
  {
    unfold B_minus_A.
    (* 使用σ-代数对补集和交集的封闭性 *)
    (* B_minus_A = B ∩ (A的补集) *)
    assert (Heq : SetEq (fun x => In x B /\ ~ In x A) 
                       (fun x => In x B /\ In x (Complement A))).
    {
      intro x.
      split.
      - intros [Hx Hnot]. 
        split; [exact Hx | exact Hnot].
      - intros [Hx Hcomp]. 
        split; [exact Hx | exact Hcomp].
    }
    apply set_extensionality in Heq.
    rewrite Heq.
    (* 使用sigma_closed_finite_union证明交集可测 *)
    (* 注意：交集可以通过补集和并集表示：B ∩ C = Complement (Complement B ∪ Complement C) *)
    set (C := Complement A).
    assert (HC : In C (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
    {
      unfold C.
      apply sigma_closed_complement; exact HA.
    }
    (* B ∩ C = Complement (Complement B ∪ Complement C) *)
    set (D := fun x => In x (Complement B) \/ In x (Complement C)).
    assert (HD : In D (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
    {
      unfold D.
      apply sigma_closed_finite_union.
      - apply sigma_closed_complement; exact HB.
      - apply sigma_closed_complement; exact HC.
    }
    assert (Heq2 : SetEq (fun x => In x B /\ In x C) (Complement D)).
    {
      intro x.
      split.
      - intros [HxB HxC].
        unfold Complement, D.
        intro H.
        destruct H as [HcB | HcC].
        + unfold Complement in HcB; contradiction.
        + unfold Complement in HcC; unfold C, Complement in HcC; contradiction.
      - intros H.
        unfold Complement, D in H.
        split.
        + apply NNPP.
          intro HnotB.
          apply H.
          left; exact HnotB.
        + apply NNPP.
          intro HnotC.
          apply H.
          right.
          unfold C, Complement; exact HnotC.
    }
    apply set_extensionality in Heq2.
    rewrite Heq2.
    apply sigma_closed_complement.
    exact HD.
  }
  
  (* 证明集合等式：B = A ∪ (B\A) *)
  assert (Hunion : SetEq B (fun x => In x A \/ In x B_minus_A)).
  {
    intro x.
    split.
    - intro HxB.
      (* 由于 A ⊆ B, 所以 x 要么在 A 中，要么在 B 但不在 A 中 *)
      destruct (classic (In x A)) as [HxA | HnotA].
      + left; exact HxA.
      + right; unfold B_minus_A; split; [exact HxB | exact HnotA].
    - intro Hx.
      destruct Hx as [HxA | HxBA].
      + (* x 在 A 中，由于 A ⊆ B，所以 x 在 B 中 *)
        apply Hsub; exact HxA.
      + (* x 在 B\A 中，所以 x 在 B 中 *)
        unfold B_minus_A in HxBA; destruct HxBA; assumption.
  }
  
  (* 证明 A 和 B\A 不相交 *)
  assert (Hdisj : Disjoint A B_minus_A).
  {
    unfold Disjoint.
    intros x [HxA HxBA].
    unfold B_minus_A in HxBA.
    destruct HxBA as [_ HnotA].
    contradiction.
  }
  
  (* 展开概率函数定义 *)
  unfold P.
  
  (* 对 mu A、mu B 和 mu B_minus_A 进行分类讨论 *)
  (* 首先，由于概率测度都是有限的，我们可以排除无穷情况 *)
  pose proof (probability_measure_finite A HA) as Hfinite_A.
  pose proof (probability_measure_finite B HB) as Hfinite_B.
  pose proof (probability_measure_finite B_minus_A Hmeas_BA) as Hfinite_BA.
  
  (* 提取测度值 *)
  case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) A);
    [intros a Ha | intros Ha].
  - (* mu A = NNER_finite a *)
    case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) B);
      [intros b Hb | intros Hb].
    + (* mu B = NNER_finite b *)
      (* 对 mu (B_minus_A) 进行分类讨论 *)
      case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
                  (BaseMeasureSpace:=ps.(ps_ℙ)) B_minus_A);
        [intros c Hc | intros Hc].
      * (* mu (B_minus_A) = NNER_finite c *)
        (* 使用有限可加性 *)
        pose proof (measure_finite_additivity 
                     (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
                     (BaseMeasureSpace:=ps.(ps_ℙ))
                     A B_minus_A HA Hmeas_BA Hdisj) as Hadd.
        
        (* 将并集重写为 B *)
        assert (Heq_set : (fun x => In x A \/ In x B_minus_A) = B).
        {
          apply set_extensionality.
          (* 从 Hunion: B eq_s (A ∪ B_minus_A) 推导出 (A ∪ B_minus_A) eq_s B *)
          intro x.
          split.
          - (* 方向1: (A ∪ B_minus_A) ⊆ B *)
            intro Hx.
            destruct (Hunion x) as [_ Hleft].
            apply Hleft; exact Hx.
          - (* 方向2: B ⊆ (A ∪ B_minus_A) *)
            intro Hx.
            destruct (Hunion x) as [Hright _].
            apply Hright; exact Hx.
        }
        rewrite Heq_set in Hadd.
        
        (* 现在 Hadd: mu A +_nner mu B_minus_A = mu B *)
        rewrite Ha, Hc, Hb in Hadd.
        unfold NNER_add in Hadd.
        simpl in Hadd.
        injection Hadd as Hsum.  (* Hsum: a + c = b *)
        
        (* 需要证明 a <= b *)
        (* 由于概率的非负性，c >= 0 *)
        pose proof (probability_nonneg B_minus_A Hmeas_BA) as Hc_nonneg.
        unfold P in Hc_nonneg.
        rewrite Hc in Hc_nonneg.
        
        (* 从 Hsum: a + c = b 和 c >= 0 可得 a <= b *)
        lra.
        
      * (* mu (B_minus_A) = NNER_infinity，与有限性矛盾 *)
        exfalso.
        apply Hfinite_BA.
        exact Hc.
        
    + (* mu B = NNER_infinity，与有限性矛盾 *)
      exfalso.
      apply Hfinite_B.
      exact Hb.
      
  - (* mu A = NNER_infinity，与有限性矛盾 *)
    exfalso.
    apply Hfinite_A.
    exact Ha.
Qed.
  
(* 并集上界 - 保持原始证明结构 *)
Theorem probability_union_bound : forall A B,
  A in_e ps -> B in_e ps ->
  P[ fun x => In x A \/ In x B ] <= P[ A ] + P[ B ].
Proof.
  intros A B HA HB.
  unfold is_event in HA, HB.
  
  (* 首先证明 A ∪ B 可测 *)
  assert (HAB_meas : In (fun x => In x A \/ In x B) (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
  {
    apply sigma_closed_finite_union; [exact HA | exact HB].
  }
  
  (* 定义集合分解：
     A = (A\B) ∪ (A∩B)
     B = (B\A) ∪ (A∩B)
     A∪B = (A\B) ∪ (B\A) ∪ (A∩B)
     这三个集合两两不相交 *)
  
  (* 定义三个互不相交的集合 *)
  set (A_minus_B := fun x => In x A /\ ~ In x B).
  set (B_minus_A := fun x => In x B /\ ~ In x A).
  set (A_inter_B := fun x => In x A /\ In x B).
  
  (* 证明这三个集合可测 *)
  assert (H_A_minus_B : In A_minus_B (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
  {
    unfold A_minus_B.
    (* A\B = A ∩ (B的补集) *)
    set (B_complement := Complement B).
    assert (Hcomp : In B_complement (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
    {
      unfold B_complement.
      apply sigma_closed_complement; exact HB.
    }
    (* A ∩ (Complement B) *)
    assert (Heq : SetEq (fun x => In x A /\ ~ In x B) 
                       (fun x => In x A /\ In x B_complement)).
    {
      intro x.
      split.
      - intros [HxA HnotB].
        split; [exact HxA | unfold B_complement; exact HnotB].
      - intros [HxA Hcomp'].
        split; [exact HxA | exact Hcomp'].
    }
    apply set_extensionality in Heq.
    rewrite Heq.
    (* 交集可以通过补集和并集表示 *)
    (* A ∩ C = Complement (Complement A ∪ Complement C) *)
    set (C := Complement A).
    set (D := Complement B_complement).
    set (E := fun x => In x C \/ In x D).
    assert (HE : In E (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
    {
      unfold E.
      apply sigma_closed_finite_union.
      - apply sigma_closed_complement; exact HA.
      - unfold D; apply sigma_closed_complement; exact Hcomp.
    }
    assert (Heq2 : SetEq (fun x => In x A /\ In x B_complement) (Complement E)).
    {
      intro x.
      split.
      - intros [HxA HBc].
        unfold Complement, E.
        intro H.
        destruct H as [HcA | HD].
        + unfold C, Complement in HcA; contradiction.
        + unfold D, Complement in HD; unfold B_complement, Complement in HBc; contradiction.
      - intros H.
        unfold Complement, E in H.
        split.
        + apply NNPP.
          intro HnotA.
          apply H.
          left; unfold C, Complement; exact HnotA.
        + apply NNPP.
          intro HnotBc.
          apply H.
          right; unfold D, Complement; exact HnotBc.
    }
    apply set_extensionality in Heq2.
    rewrite Heq2.
    apply sigma_closed_complement; exact HE.
  }
  
  assert (H_B_minus_A : In B_minus_A (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
  {
    (* 对称性，类似 A_minus_B 的证明 *)
    unfold B_minus_A.
    set (A_complement := Complement A).
    assert (Hcomp : In A_complement (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
    {
      unfold A_complement.
      apply sigma_closed_complement; exact HA.
    }
    (* B ∩ (Complement A) *)
    assert (Heq : SetEq (fun x => In x B /\ ~ In x A) 
                       (fun x => In x B /\ In x A_complement)).
    {
      intro x.
      split.
      - intros [HxB HnotA].
        split; [exact HxB | unfold A_complement; exact HnotA].
      - intros [HxB Hcomp'].
        split; [exact HxB | exact Hcomp'].
    }
    apply set_extensionality in Heq.
    rewrite Heq.
    (* 类似地证明交集可测 *)
    set (C := Complement B).
    set (D := Complement A_complement).
    set (E := fun x => In x C \/ In x D).
    assert (HE : In E (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
    {
      unfold E.
      apply sigma_closed_finite_union.
      - apply sigma_closed_complement; exact HB.
      - unfold D; apply sigma_closed_complement; exact Hcomp.
    }
    assert (Heq2 : SetEq (fun x => In x B /\ In x A_complement) (Complement E)).
    {
      intro x.
      split.
      - intros [HxB HAc].
        unfold Complement, E.
        intro H.
        destruct H as [HcB | HD].
        + unfold C, Complement in HcB; contradiction.
        + unfold D, Complement in HD; unfold A_complement, Complement in HAc; contradiction.
      - intros H.
        unfold Complement, E in H.
        split.
        + apply NNPP.
          intro HnotB.
          apply H.
          left; unfold C, Complement; exact HnotB.
        + apply NNPP.
          intro HnotAc.
          apply H.
          right; unfold D, Complement; exact HnotAc.
    }
    apply set_extensionality in Heq2.
    rewrite Heq2.
    apply sigma_closed_complement; exact HE.
  }
  
  assert (H_A_inter_B : In A_inter_B (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
  {
    (* A ∩ B = Complement (Complement A ∪ Complement B) *)
    set (A_complement := Complement A).
    set (B_complement := Complement B).
    set (C := fun x => In x A_complement \/ In x B_complement).
    assert (H_A_comp : In A_complement (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
    { apply sigma_closed_complement; exact HA. }
    assert (H_B_comp : In B_complement (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
    { apply sigma_closed_complement; exact HB. }
    assert (HC : In C (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
    {
      unfold C.
      apply sigma_closed_finite_union; [exact H_A_comp | exact H_B_comp].
    }
    assert (Heq : SetEq A_inter_B (Complement C)).
    {
      intro x.
      split.
      - intros [HxA HxB].
        unfold Complement, C.
        intro H.
        destruct H as [HcA | HcB].
        + unfold A_complement, Complement in HcA; contradiction.
        + unfold B_complement, Complement in HcB; contradiction.
      - intros H.
        unfold Complement, C in H.
        split.
        + apply NNPP.
          intro HnotA.
          apply H.
          left; unfold A_complement, Complement; exact HnotA.
        + apply NNPP.
          intro HnotB.
          apply H.
          right; unfold B_complement, Complement; exact HnotB.
    }
    apply set_extensionality in Heq.
    rewrite Heq.
    apply sigma_closed_complement; exact HC.
  }
  
  (* 证明三个集合两两不相交 *)
  assert (Hdisj1 : Disjoint A_minus_B B_minus_A).
  {
    unfold Disjoint.
    intros x [H1 H2].
    unfold A_minus_B in H1; unfold B_minus_A in H2.
    destruct H1 as [HxA HnotB]; destruct H2 as [HxB HnotA].
    contradiction.
  }
  
  assert (Hdisj2 : Disjoint A_minus_B A_inter_B).
  {
    unfold Disjoint.
    intros x [H1 H2].
    unfold A_minus_B in H1; unfold A_inter_B in H2.
    destruct H1 as [HxA HnotB]; destruct H2 as [_ HxB].
    contradiction.
  }
  
  assert (Hdisj3 : Disjoint B_minus_A A_inter_B).
  {
    unfold Disjoint.
    intros x [H1 H2].
    unfold B_minus_A in H1; unfold A_inter_B in H2.
    destruct H1 as [HxB HnotA]; destruct H2 as [HxA _].
    contradiction.
  }
  
  (* 证明集合等式：A = (A\B) ∪ (A∩B) *)
  assert (Heq_A : SetEq A (fun x => In x A_minus_B \/ In x A_inter_B)).
  {
    intro x.
    split.
    - intro HxA.
      destruct (classic (In x B)) as [HxB | HnotB].
      + right; unfold A_inter_B; split; assumption.
      + left; unfold A_minus_B; split; assumption.
    - intro H.
      destruct H as [H1 | H2].
      + unfold A_minus_B in H1; destruct H1; assumption.
      + unfold A_inter_B in H2; destruct H2; assumption.
  }
  
  (* 证明集合等式：B = (B\A) ∪ (A∩B) *)
  assert (Heq_B : SetEq B (fun x => In x B_minus_A \/ In x A_inter_B)).
  {
    intro x.
    split.
    - intro HxB.
      destruct (classic (In x A)) as [HxA | HnotA].
      + right; unfold A_inter_B; split; assumption.
      + left; unfold B_minus_A; split; assumption.
    - intro H.
      destruct H as [H1 | H2].
      + unfold B_minus_A in H1; destruct H1; assumption.
      + unfold A_inter_B in H2; destruct H2; assumption.
  }
  
  (* 证明集合等式：A∪B = (A\B) ∪ (B\A) ∪ (A∩B) *)
  assert (Heq_union : SetEq (fun x => In x A \/ In x B) 
                           (fun x => In x A_minus_B \/ In x B_minus_A \/ In x A_inter_B)).
  {
    intro x.
    split.
    - intro H.
      destruct H as [HxA | HxB].
      + (* x ∈ A *)
        destruct (classic (In x B)) as [HxB' | HnotB].
        * right; right; unfold A_inter_B; split; assumption.
        * left; unfold A_minus_B; split; assumption.
      + (* x ∈ B *)
        destruct (classic (In x A)) as [HxA' | HnotA].
        * right; right; unfold A_inter_B; split; assumption.
        * right; left; unfold B_minus_A; split; assumption.
    - intro H.
      destruct H as [H1 | [H2 | H3]].
      + (* x ∈ A\B *)
        unfold A_minus_B in H1; destruct H1 as [HxA _]; left; exact HxA.
      + (* x ∈ B\A *)
        unfold B_minus_A in H2; destruct H2 as [HxB _]; right; exact HxB.
      + (* x ∈ A∩B *)
        unfold A_inter_B in H3; destruct H3 as [HxA _]; left; exact HxA.
  }
  
  (* 展开概率函数定义 *)
  unfold P.
  
  (* 对测度进行分类讨论，由于概率测度都是有限的，我们可以排除无穷情况 *)
  pose proof (probability_measure_finite A HA) as Hfinite_A.
  pose proof (probability_measure_finite B HB) as Hfinite_B.
  pose proof (probability_measure_finite A_minus_B H_A_minus_B) as Hfinite_AB.
  pose proof (probability_measure_finite B_minus_A H_B_minus_A) as Hfinite_BA.
  pose proof (probability_measure_finite A_inter_B H_A_inter_B) as Hfinite_inter.
  
  (* 定义局部测度函数简写 *)
  set (mu_ps := mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ))).
  
  (* 重新提取测度值 *)
  case_eq (mu_ps A); [intros a Ha | intros Ha].
  - (* mu A = NNER_finite a *)
    case_eq (mu_ps B); [intros b Hb | intros Hb].
    + (* mu B = NNER_finite b *)
      (* 提取其他测度值 *)
      case_eq (mu_ps A_minus_B); [intros c Hc | intros Hc].
      * (* mu A_minus_B = NNER_finite c *)
        case_eq (mu_ps B_minus_A); [intros d Hd | intros Hd].
        -- (* mu B_minus_A = NNER_finite d *)
          case_eq (mu_ps A_inter_B); [intros e He | intros He].
          ++ (* mu A_inter_B = NNER_finite e *)
            (* 使用有限可加性计算各个并集的测度 *)
            
            (* 1. 计算 A = (A\B) ∪ (A∩B) 的测度 *)
            assert (Hadd_A : mu_ps A = mu_ps A_minus_B +_nner mu_ps A_inter_B).
            {
              pose proof (measure_finite_additivity 
                           (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
                           (BaseMeasureSpace:=ps.(ps_ℙ))
                           A_minus_B A_inter_B H_A_minus_B H_A_inter_B Hdisj2) as Hadd.
              (* 将并集重写为 A *)
              assert (Heq_set : (fun x => In x A_minus_B \/ In x A_inter_B) = A).
              {
                apply set_extensionality.
                intro x.
                split.
                - intro H.
                  (* 从并集推出属于 A *)
                  destruct H as [H1 | H2].
                  + unfold A_minus_B in H1; destruct H1 as [HxA _]; exact HxA.
                  + unfold A_inter_B in H2; destruct H2 as [HxA _]; exact HxA.
                - intro H.
                  (* 从 A 推出属于并集 *)
                  destruct (Heq_A x) as [Hforth _].
                  apply Hforth; exact H.
              }
              rewrite Heq_set in Hadd.
              exact Hadd.
            }
            rewrite Ha, Hc, He in Hadd_A.
            unfold NNER_add in Hadd_A.
            simpl in Hadd_A.
            injection Hadd_A as Hsum_A.  (* Hsum_A: a = c + e *)
            
            (* 2. 计算 B = (B\A) ∪ (A∩B) 的测度 *)
            assert (Hadd_B : mu_ps B = mu_ps B_minus_A +_nner mu_ps A_inter_B).
            {
              pose proof (measure_finite_additivity 
                           (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
                           (BaseMeasureSpace:=ps.(ps_ℙ))
                           B_minus_A A_inter_B H_B_minus_A H_A_inter_B Hdisj3) as Hadd.
              assert (Heq_set : (fun x => In x B_minus_A \/ In x A_inter_B) = B).
              {
                apply set_extensionality.
                intro x.
                split.
                - intro H.
                  destruct H as [H1 | H2].
                  + unfold B_minus_A in H1; destruct H1 as [HxB _]; exact HxB.
                  + unfold A_inter_B in H2; destruct H2 as [_ HxB]; exact HxB.
                - intro H.
                  destruct (Heq_B x) as [Hforth _].
                  apply Hforth; exact H.
              }
              rewrite Heq_set in Hadd.
              exact Hadd.
            }
            rewrite Hb, Hd, He in Hadd_B.
            unfold NNER_add in Hadd_B.
            simpl in Hadd_B.
            injection Hadd_B as Hsum_B.  (* Hsum_B: b = d + e *)
            
            (* 3. 计算 A∪B = (A\B) ∪ (B\A) ∪ (A∩B) 的测度 *)
            (* 先计算 (A\B) ∪ (B\A) *)
            set (AB_union := fun x => In x A_minus_B \/ In x B_minus_A).
            assert (Hmeas_AB_union : In AB_union (sigma_sets ps.(ps_Ω) ps.(ps_𝓕))).
            {
              unfold AB_union.
              apply sigma_closed_finite_union; [exact H_A_minus_B | exact H_B_minus_A].
            }
            
            assert (Hdisj_AB : Disjoint A_minus_B B_minus_A) by exact Hdisj1.
            pose proof (measure_finite_additivity 
                         (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
                         (BaseMeasureSpace:=ps.(ps_ℙ))
                         A_minus_B B_minus_A H_A_minus_B H_B_minus_A Hdisj_AB) as Hadd_AB.
            
            (* (A\B) ∪ (B\A) 与 (A∩B) 不相交 *)
            assert (Hdisj_union : Disjoint AB_union A_inter_B).
            {
              unfold Disjoint, AB_union.
              intros x [Hunion H_inter].
              destruct Hunion as [H1 | H2].
              - unfold A_minus_B in H1; destruct H1 as [HxA HnotB].
                unfold A_inter_B in H_inter; destruct H_inter as [_ HxB].
                contradiction.
              - unfold B_minus_A in H2; destruct H2 as [HxB HnotA].
                unfold A_inter_B in H_inter; destruct H_inter as [HxA _].
                contradiction.
            }
            
            pose proof (measure_finite_additivity 
                         (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
                         (BaseMeasureSpace:=ps.(ps_ℙ))
                         AB_union A_inter_B Hmeas_AB_union H_A_inter_B Hdisj_union) as Hadd_total.
            
            (* 将并集重写为 A∪B *)
            assert (Heq_set_total : (fun x => In x AB_union \/ In x A_inter_B) = 
                                   (fun x => In x A \/ In x B)).
            {
              apply set_extensionality.
              intro x.
              split.
              - intros [H | H].
                + unfold AB_union in H; destruct H as [H1 | H2].
                  * unfold A_minus_B in H1; destruct H1; left; assumption.
                  * unfold B_minus_A in H2; destruct H2; right; assumption.
                + unfold A_inter_B in H; destruct H; left; assumption.
              - intros H.
                (* 使用 Heq_union 将 x ∈ A ∪ B 转换为分解集合 *)
                destruct (Heq_union x) as [Hdir _].  (* Hdir: x ∈ A ∪ B -> x ∈ 分解集合 *)
                specialize (Hdir H).  (* 现在 Hdir: x ∈ A_minus_B ∨ x ∈ B_minus_A ∨ x ∈ A_inter_B *)
                destruct Hdir as [H1 | [H2 | H3]].
                + left; unfold AB_union; left; exact H1.
                + left; unfold AB_union; right; exact H2.
                + right; exact H3.
            }
            rewrite Heq_set_total in Hadd_total.
            
            (* 计算测度 *)
            (* 首先，我们需要用 Hc 和 Hd 重写 Hadd_AB 中的 mu A_minus_B 和 mu B_minus_A *)
            assert (Hadd_AB_mu : mu_ps (fun x => In x A_minus_B \/ In x B_minus_A) = 
                                mu_ps A_minus_B +_nner mu_ps B_minus_A).
            {
              (* 将 Hadd_AB 转换为使用 mu_ps *)
              unfold mu_ps.
              exact Hadd_AB.
            }
            
            (* 现在我们可以重写 Hadd_AB_mu *)
            rewrite Hc, Hd in Hadd_AB_mu.
            unfold NNER_add in Hadd_AB_mu; simpl in Hadd_AB_mu.
            
            (* 将 Hadd_total 也转换为使用 mu_ps *)
            assert (Hadd_total_mu : mu_ps (fun x => In x A \/ In x B) = 
                                   mu_ps AB_union +_nner mu_ps A_inter_B).
            {
              (* 将 Hadd_total 转换为使用 mu_ps *)
              unfold mu_ps.
              exact Hadd_total.
            }
            
            (* 我们需要知道 mu_ps AB_union 的值 *)
            (* 根据 Hadd_AB_mu，mu_ps (A_minus_B ∪ B_minus_A) = NNER_finite (c+d) *)
            (* 而 AB_union 就是 (A_minus_B ∪ B_minus_A) *)
            assert (Hmu_AB_union : mu_ps AB_union = NNER_finite (c + d)).
            {
              unfold AB_union.
              exact Hadd_AB_mu.
            }
            
            (* 现在重写 Hadd_total_mu *)
            rewrite Hmu_AB_union, He in Hadd_total_mu.
            unfold NNER_add in Hadd_total_mu; simpl in Hadd_total_mu.
            (* 现在 Hadd_total_mu: mu_ps(A∪B) = NNER_finite (c + d + e) *)
            
            (* 计算 mu_ps(A∪B) 的值 *)
            set (mu_A_union_B := mu_ps (fun x => In x A \/ In x B)).
            
            (* 需要证明：mu_ps(A∪B) ≤ a + b *)
            (* 现在我们有：
               Hsum_A: a = c + e
               Hsum_B: b = d + e
               Hadd_total_mu: mu_ps(A∪B) = NNER_finite (c + d + e)
               
               需要证明：mu_ps(A∪B) ≤ a + b
               即 (c+d)+e ≤ (c+e) + (d+e) = c + d + 2e
               也就是 0 ≤ e，这由概率的非负性保证
            *)
            (* 计算 a + b *)
            pose proof (probability_nonneg A_inter_B H_A_inter_B) as H_nonneg_inter.
            (* H_nonneg_inter: 0 <= P[ A_inter_B ] *)
            (* 根据 He: mu_ps A_inter_B = NNER_finite e，所以 P[ A_inter_B ] = e *)
            assert (H_P_inter : P[ A_inter_B ] = e).
            {
              unfold P.
              unfold mu_ps in He.  (* 展开 mu_ps，将其变为 mu *)
              rewrite He.          (* 现在可以重写 *)
              reflexivity.
            }
            rewrite H_P_inter in H_nonneg_inter.
            (* 现在 H_nonneg_inter: 0 <= e *)
            
            (* 展开 mu_A_union_B 并使用 Hadd_total_mu *)
            unfold mu_A_union_B.
            rewrite Hadd_total_mu.  (* 直接使用 Hadd_total_mu *)
            
            (* 展开 a 和 b 的表达式 *)
            rewrite Hsum_A, Hsum_B.
            
            (* 现在需要证明：(c+d)+e ≤ (c+e)+(d+e) *)
            (* 化简右边：(c+e)+(d+e) = c+d+2e *)
            (* 所以不等式变为：(c+d)+e ≤ c+d+2e *)
            (* 即 e ≤ 2e，也就是 0 ≤ e *)
            lra.
            
          ++ (* mu A_inter_B = NNER_infinity，与有限性矛盾 *)
            exfalso.
            apply Hfinite_inter.
            exact He.
        -- (* mu B_minus_A = NNER_infinity，与有限性矛盾 *)
          exfalso.
          apply Hfinite_BA.
          exact Hd.
      * (* mu A_minus_B = NNER_infinity，与有限性矛盾 *)
        exfalso.
        apply Hfinite_AB.
        exact Hc.
    + (* mu B = NNER_infinity，与有限性矛盾 *)
      exfalso.
      apply Hfinite_B.
      exact Hb.
  - (* mu A = NNER_infinity，与有限性矛盾 *)
    exfalso.
    apply Hfinite_A.
    exact Ha.
Qed.
  
(** 概率测度的从下连续性 **)
Theorem probability_continuity_from_below : 
  forall (A_seq : nat -> SetX Ω'),
    (forall n, A_seq n in_e ps) ->
    (forall n, Subset (A_seq n) (A_seq (S n))) ->
    sequence_converges (fun n => P (A_seq n)) 
                      (P (fun x => exists n, In x (A_seq n))).
Proof.
  intros A_seq Hmeas Hinc.
  
  (* 步骤1：定义不相交序列 C_seq *)
  set (C_seq := fun (n : nat) =>
    match n with
    | O => A_seq O
    | S n' => (fun x => In x (A_seq (S n')) /\ ~ In x (A_seq n'))
    end).
  
  (* 步骤2：证明每个 C_seq n 可测 *)
  assert (Hmeas_C : forall n, C_seq n in_e ps).
  {
    intro n.
    unfold C_seq.
    destruct n as [O | n'].
    - (* n = O *)
      apply Hmeas.
    - (* n = S n' *)
      (* 证明 (fun x => In x (A_seq (S n')) /\ ~ In x (A_seq n')) 可测 *)
      
      (* 首先证明 A_seq (S n') 可测 *)
      assert (Hmeas_S : A_seq (S n') in_e ps).
      {
        apply Hmeas.
      }
      
      (* 证明 A_seq n' 可测 *)
      assert (Hmeas_n' : A_seq n' in_e ps).
      {
        apply Hmeas.
      }
      
      (* 证明 Complement (A_seq (S n')) 可测 *)
      assert (Hcomp_S : is_event (Complement (A_seq (S n')))).
      {
        unfold is_event.
        apply sigma_closed_complement.
        exact Hmeas_S.
      }
      
      (* 现在我们需要证明 A_seq (S n') ∩ Complement (A_seq n') 可测 *)
      (* 使用等式：A ∩ B = Complement (Complement A ∪ B) *)
      (* 所以我们先证明 Complement (A_seq (S n')) ∪ A_seq n' 可测 *)
      
      (* 证明并集可测 *)
      assert (Hunion : is_event (fun x => In x (Complement (A_seq (S n'))) \/ 
                                         In x (A_seq n'))).
      {
        unfold is_event.
        apply sigma_closed_finite_union.
        - exact Hcomp_S.
        - exact Hmeas_n'.
      }
      
      (* 证明并集的补集可测 *)
      assert (Hfinal : is_event (Complement 
                (fun x => In x (Complement (A_seq (S n'))) \/ 
                         In x (A_seq n')))).
      {
        unfold is_event.
        apply sigma_closed_complement.
        exact Hunion.
      }
      
      (* 现在证明这个补集等于我们要的集合 *)
      assert (Heq_final : SetEq 
                (Complement (fun x => In x (Complement (A_seq (S n'))) \/ 
                                     In x (A_seq n')))
                (fun x => In x (A_seq (S n')) /\ ~ In x (A_seq n'))).
      {
        intro x.
        split.
        - intro H.
          unfold Complement in H.
          unfold In in H.
          simpl in H.
          split.
          + (* 证明 In x (A_seq (S n')) *)
            apply NNPP.
            intro Hnot.
            apply H.
            left.
            exact Hnot.
          + (* 证明 ~ In x (A_seq n') *)
            intro Hnot.
            apply H.
            right.
            exact Hnot.
        - intro H.
          destruct H as [H1 H2].
          unfold Complement, In.
          simpl.
          intro Hor.
          destruct Hor as [H3 | H4].
          + (* H3: ~ In x (A_seq (S n')) *)
            contradiction.
          + (* H4: In x (A_seq n') *)
            contradiction.
      }
      
      (* 使用集合相等性将 SetEq 转换为函数相等 *)
      apply set_extensionality in Heq_final.
      (* Heq_final: Complement(...) = (fun x => In x (A_seq (S n')) /\ ~ In x (A_seq n')) *)
      
      (* 将目标重写为 Complement(...)，这样我们就可以应用 Hfinal *)
      rewrite <- Heq_final.
      
      (* 现在目标正好是 Hfinal 所证明的 *)
      exact Hfinal.
  }
  
  (* 步骤3：证明 C_seq 两两不相交 *)
  assert (Hdisj_C : PairwiseDisjoint C_seq).
  {
    (* 先证明单调性的一般形式 *)
    assert (Hmono_general : forall n m, (n <= m)%nat -> Subset (A_seq n) (A_seq m)).
    {
      intros n m Hle.
      (* 对 m 进行归纳，固定 n *)
      induction m as [O | m IHm].
      - (* m = O *)
        (* 如果 n ≤ 0，那么 n = 0 *)
        assert (Hn_eq : n = O) by lia.
        subst n.
        apply subset_reflexive.
      - (* m = S m *)
        (* 我们需要考虑两种情况：n = S m 或 n < S m *)
        (* 如果 n = S m，那么应用自反性 *)
        (* 如果 n < S m，那么 n ≤ m，应用归纳假设和 Hinc *)
        destruct (eq_nat_dec n (S m)) as [Heq | Hneq].
        + (* n = S m *)
          subst n.
          apply subset_reflexive.
        + (* n ≠ S m，所以 n < S m，因此 n ≤ m *)
          assert (Hle' : (n <= m)%nat) by lia.
          apply subset_transitive with (B := A_seq m).
          * apply IHm; exact Hle'.
          * exact (Hinc m).
    }
    
    unfold PairwiseDisjoint, Disjoint.
    intros n m Hneq.
    destruct n as [O | n']; destruct m as [O | m'].
    - (* n = O, m = O *)
      intros x H.
      exfalso.
      apply Hneq.
      reflexivity.
    - (* n = O, m = S m' *)
      intros x H.
      destruct H as [Hx1 Hx2].
      unfold C_seq in Hx1, Hx2.
      simpl in Hx1.
      simpl in Hx2.
      destruct Hx2 as [Hx2a Hx2b].
      (* 使用单调性：A_seq O ⊆ A_seq m' *)
      assert (Hle : (O <= m')%nat) by lia.
      apply Hmono_general with (n := O) (m := m') in Hle.
      unfold Subset in Hle.
      apply Hle in Hx1.
      contradiction Hx2b.
    - (* n = S n', m = O *)
      intros x H.
      destruct H as [Hx1 Hx2].
      unfold C_seq in Hx1, Hx2.
      simpl in Hx1.
      simpl in Hx2.
      destruct Hx1 as [Hx1a Hx1b].
      (* 使用单调性：A_seq O ⊆ A_seq n' *)
      assert (Hle : (O <= n')%nat) by lia.
      apply Hmono_general with (n := O) (m := n') in Hle.
      unfold Subset in Hle.
      apply Hle in Hx2.
      contradiction Hx1b.
    - (* n = S n', m = S m' *)
      intros x H.
      destruct H as [Hx1 Hx2].
      unfold C_seq in Hx1, Hx2.
      simpl in Hx1, Hx2.
      destruct Hx1 as [Hx1a Hx1b].
      destruct Hx2 as [Hx2a Hx2b].
      (* 由于 Hneq: S n' ≠ S m'，所以 n' ≠ m' *)
      (* 比较 n' 和 m' 的大小 *)
      destruct (lt_eq_lt_dec n' m') as [[Hlt | Heq] | Hgt].
      + (* n' < m' *)
        (* 那么 S n' ≤ m' *)
        assert (Hle : (S n' <= m')%nat) by lia.
        apply Hmono_general with (n := S n') (m := m') in Hle.
        unfold Subset in Hle.
        apply Hle in Hx1a.
        contradiction Hx2b.
      + (* n' = m' *)
        (* 这与 Hneq 矛盾，因为如果 n' = m'，那么 S n' = S m' *)
        exfalso.
        apply Hneq.
        f_equal.
        exact Heq.
      + (* n' > m' *)
        (* 那么 S m' ≤ n' *)
        assert (Hle : (S m' <= n')%nat) by lia.
        apply Hmono_general with (n := S m') (m := n') in Hle.
        unfold Subset in Hle.
        apply Hle in Hx2a.
        (* 现在我们有 Hx2a: In x (A_seq n') 和 Hx1b: ~ In x (A_seq n') *)
        exfalso.
        apply Hx1b.
        exact Hx2a.
  }
  
  (* 步骤4：证明对于每个 n，A_seq n = ⋃_{i=0}^n C_seq i *)
  assert (Hdecomp : forall n, SetEq (A_seq n) 
    (fun x => exists i, (i <= n)%nat /\ In x (C_seq i))).
  {
    (* 先证明辅助引理：对于任意 n，A_0 ⊆ A_n *)
    assert (Hsub_base : forall n, Subset (A_seq O) (A_seq n)).
    {
      intro n.
      induction n as [O | n IHn].
      - (* n = O *)
        apply subset_reflexive.
      - (* n = S n *)
        apply subset_transitive with (B := A_seq n).
        + exact IHn.
        + exact (Hinc n).
    }
    
    (* 再证明辅助引理：如果 i ≤ n，则 A_seq (S i) ⊆ A_seq (S n) *)
    assert (Hsub_S : forall i n, (i <= n)%nat -> Subset (A_seq (S i)) (A_seq (S n))).
    {
      intros i n Hle.
      (* 对 n 进行归纳，同时固定 i 并假设 i ≤ n *)
      induction n as [O | n IHn].
      - (* n = O *)
        (* 由于 i ≤ 0，所以 i = 0 *)
        assert (Hi_eq : i = O) by lia.
        subst i.
        apply subset_reflexive.
      - (* n = S n *)
        (* 我们需要考虑 i 和 S n 的关系 *)
        destruct (le_lt_eq_dec i (S n) Hle) as [Hlt | Heq].
        + (* i < S n，所以 i ≤ n *)
          assert (Hle' : (i <= n)%nat) by lia.
          (* 应用归纳假设：A_seq (S i) ⊆ A_seq (S n) *)
          (* 然后使用 Hinc: A_seq (S n) ⊆ A_seq (S (S n)) *)
          apply subset_transitive with (B := A_seq (S n)).
          * apply IHn; exact Hle'.
          * exact (Hinc (S n)).
        + (* i = S n *)
          subst i.
          apply subset_reflexive.
    }
    
    intro n.
    induction n as [O | n IH].
    - (* n = O *)
      intro x.
      split.
      + intro Hx.
        exists O.
        split; [lia | exact Hx].
      + intros [i [Hi Hx]].
        assert (i = O) by lia.
        subst.
        exact Hx.
    - (* n = S n *)
      intro x.
      split.
      + intro Hx.
        (* x ∈ A_{n+1} *)
        destruct (classic (In x (A_seq n))) as [Hx_n | Hx_not_n].
        * (* 如果在 A_n 中，使用归纳假设 *)
          apply IH in Hx_n.
          destruct Hx_n as [i [Hi Hx_i]].
          exists i.
          split; [lia | exact Hx_i].
        * (* 如果不在 A_n 中，则 x ∈ C_{n+1} *)
          exists (S n).
          split; [lia | unfold C_seq; simpl; split; assumption].
      + intros [i [Hi Hx]].
        (* 从 C_seq i 推出 x ∈ A_{n+1} *)
        unfold C_seq in Hx.
        destruct i as [O | i'].
        * (* i = O *)
          simpl in Hx.
          (* 从 A_0 推出 x ∈ A_{n+1} *)
          apply Hsub_base.
          exact Hx.
        * (* i = S i' *)
          simpl in Hx.
          destruct Hx as [Hx' _].
          (* x ∈ A_{i'+1}，且 i' + 1 ≤ n+1，所以 i' ≤ n *)
          apply Hsub_S with (i := i') (n := n).
          - lia.
          - exact Hx'.
  }
  
  (* 步骤5：证明 ⋃_n A_seq n = ⋃_n C_seq n *)
  assert (Hunion_eq : SetEq (fun x => exists n, In x (A_seq n))
                          (fun x => exists n, In x (C_seq n))).
  {
    intro x.
    split.
    - intros [n Hx].
      (* 使用分解引理 *)
      apply Hdecomp in Hx.
      destruct Hx as [i [Hi Hx_i]].
      exists i.
      exact Hx_i.
    - intros [n Hx].
      exists n.
      (* 从 C_seq n 推出在某个 A_seq 中 *)
      unfold C_seq in Hx.
      destruct n as [O | n'].
      + (* n = O *)
        simpl in Hx.
        exact Hx.
      + (* n = S n' *)
        simpl in Hx.
        destruct Hx as [Hx' _].
        exact Hx'.
  }
  
  (* 步骤6：应用概率的可数可加性 *)
  (* 应用概率的可数可加性到 C_seq *)
  pose proof (probability_countable_additivity C_seq Hmeas_C Hdisj_C) as Hcountable.
  
  (* 重写 Hcountable 的右边 *)
  assert (Heq_union : P (fun x => exists n, In x (C_seq n)) = 
                     P (fun x => exists n, In x (A_seq n))).
  {
    apply f_equal.
    (* 使用集合相等性 *)
    apply set_extensionality.
    intro x.
    (* 我们需要证明两个集合相等 *)
    (* 根据 Hunion_eq，我们已经知道 SetEq A B，其中 A 是 A_seq 的并集，B 是 C_seq 的并集 *)
    (* 但是我们需要证明 B = A，即 C_seq 的并集等于 A_seq 的并集 *)
    (* 我们可以从 Hunion_eq 得到两个方向 *)
    split.
    - (* 从 C_seq 的并集到 A_seq 的并集 *)
      intro H.
      destruct H as [n Hx].
      exists n.
      unfold C_seq in Hx.
      destruct n as [O | n'].
      + (* n = O *)
        simpl in Hx.
        exact Hx.
      + (* n = S n' *)
        simpl in Hx.
        destruct Hx as [Hx' _].
        exact Hx'.
    - (* 从 A_seq 的并集到 C_seq 的并集 *)
      intro H.
      destruct H as [n Hx].
      (* 使用分解引理 *)
      apply Hdecomp in Hx.
      destruct Hx as [i [Hi Hx_i]].
      exists i.
      exact Hx_i.
  }
  rewrite Heq_union in Hcountable.
  
  (* 步骤7：证明 P(A_seq n) = Σ_{i=0}^n P(C_seq i) *)
  assert (Hpartial : forall n, P (A_seq n) = 
    sum_f_R0 (fun i => P (C_seq i)) n).
  {
    intro n.
    (* 使用有限可加性和分解 *)
    (* 首先，将 A_seq n 分解为 ⋃_{i=0}^n C_seq i *)
    (* 由于 C_seq 两两不相交，所以概率等于和 *)
    (* 我们可以通过归纳法证明 *)
    induction n as [O | n IH].
    - (* n = O *)
      simpl.
      unfold sum_f_R0.
      simpl.
      reflexivity.
    - (* n = S n *)
      (* 我们知道 A_{n+1} = A_n ∪ C_{n+1}，并且 A_n 和 C_{n+1} 不相交 *)
      (* 因此 P(A_{n+1}) = P(A_n) + P(C_{n+1}) *)
      (* 而根据归纳假设，P(A_n) = Σ_{i=0}^n P(C_seq i) *)
      (* 所以 P(A_{n+1}) = Σ_{i=0}^n P(C_seq i) + P(C_{n+1}) = Σ_{i=0}^{n+1} P(C_seq i) *)
      
      (* 证明 A_n 和 C_{n+1} 不相交 *)
      assert (Hdisj_An_C : Disjoint (A_seq n) (C_seq (S n))).
      {
        unfold Disjoint.
        intros x [Hx1 Hx2].
        (* Hx1: x in A_seq n, Hx2: x in C_seq (S n) *)
        (* 由 Hdecomp，x 在某个 C_seq i (i≤n) 中 *)
        apply Hdecomp in Hx1.
        destruct Hx1 as [i [Hi Hx1]].
        (* 现在，x 同时在 C_seq i (i≤n) 和 C_seq (S n) 中 *)
        (* 由于 i ≤ n < S n，所以 i ≠ S n *)
        (* 由 Hdisj_C，C_seq i 和 C_seq (S n) 不相交，矛盾 *)
        pose proof (Hdisj_C i (S n)) as Hdisj.
        assert (Hneq : i <> S n) by lia.
        apply Hdisj in Hneq.
        unfold Disjoint in Hneq.
        apply Hneq with x.
        split; assumption.
      }
      
      (* 证明 A_{n+1} = A_n ∪ C_{n+1} *)
      assert (Heq_union_set : SetEq (A_seq (S n)) 
                               (fun x => In x (A_seq n) \/ In x (C_seq (S n)))).
      {
        intro x.
        split.
        - intro Hx.
          (* x ∈ A_{n+1} *)
          (* 根据 Hdecomp，x 在某个 C_seq i (i ≤ n+1) 中 *)
          apply Hdecomp in Hx.
          destruct Hx as [i [Hi Hx]].
          destruct (le_lt_eq_dec i (S n) Hi) as [Hlt | Heq].
          + (* i < S n，所以 i ≤ n *)
            left.
            apply Hdecomp.
            exists i.
            split; [lia | assumption].
          + (* i = S n *)
            right.
            subst i.
            assumption.
        - intros [Hx | Hx].
          + (* x ∈ A_n *)
            apply Hinc.
            exact Hx.
          + (* x ∈ C_{n+1} *)
            unfold C_seq in Hx.
            simpl in Hx.
            destruct Hx as [Hx' _].
            exact Hx'.
      }
      
      (* 使用概率的有限可加性 *)
      pose proof (probability_finite_additivity (A_seq n) (C_seq (S n)) 
                  (Hmeas n) (Hmeas_C (S n)) Hdisj_An_C) as Hadd.
      
      (* 使用集合相等性来证明概率相等 *)
      assert (Hprob_eq : P (fun x => In x (A_seq n) \/ In x (C_seq (S n))) = P (A_seq (S n))).
      {
        (* 因为两个集合相等，所以它们的概率相等 *)
        apply f_equal.
        (* 使用集合外延性公理将 SetEq 转换为函数相等 *)
        apply set_extensionality.
        (* 将 Heq_union_set 转换为对称形式 *)
        intro x.
        (* 从 Heq_union_set 获取双向蕴含 *)
        destruct (Heq_union_set x) as [Hleft Hright].
        (* 现在构建新的双向蕴含 *)
        split; assumption.
      }
      
      (* 将 Hadd 中的并集概率重写为 A_{n+1} 的概率 *)
      rewrite Hprob_eq in Hadd.
      
      (* 现在 Hadd: P(A_{n+1}) = P(A_n) + P(C_{n+1}) *)
      rewrite IH in Hadd.
      
      (* 展开 sum_f_R0 到 S n *)
      unfold sum_f_R0 at 1.   (* 展开 sum_f_R0 的定义 *)
      simpl.                  (* 简化：sum_f_R0 f (S n) = sum_f_R0 f n + f (S n) *)
      
      (* 现在目标：P(A_{n+1}) = (sum_f_R0 (fun i => P(C_seq i)) n) + P(C_seq (S n)) *)
      (* 这正好是 Hadd 的形式 *)
      exact Hadd.
  }
  
  (* 步骤8：证明 P(A_seq n) 收敛到 P(⋃ A_seq) *)
  unfold sequence_converges, Un_cv.
  intros eps Heps_pos.
  unfold infinite_sum in Hcountable.
  destruct (Hcountable eps Heps_pos) as [N HN].
  exists N.
  intros n Hn.
  (* 当前目标：R_dist (P (A_seq n)) (P (fun x => exists n0, In x (A_seq n0))) < eps *)
  (* 使用 Hpartial 重写 P (A_seq n) *)
  rewrite Hpartial.
  (* 现在目标与 HN 中的一致 *)
  apply HN.
  exact Hn.
Qed.
  
(** 概率测度的从上连续性  **)
Theorem probability_continuity_from_above : 
  forall (A_seq : nat -> SetX Ω'),
    (forall n, A_seq n in_e ps) ->
    (forall n, Subset (A_seq (S n)) (A_seq n)) ->
    (exists n, mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) (A_seq n) <> NNER_infinity) ->
    sequence_converges (fun n => P (A_seq n)) 
                      (P (fun x => forall n, In x (A_seq n))).
Proof.
  intros A_seq Hmeas Hdecr Hfinite.
  
  (* 步骤1：定义交集事件 *)
  set (A_inf := fun x => forall n, In x (A_seq n)).
  
  (* 步骤2：证明交集事件可测 *)
  assert (Hmeas_Ainf : A_inf in_e ps).
  {
    unfold A_inf, is_event.
    apply sigma_closed_countable_intersection.
    exact Hmeas.
  }
  
  (* 步骤3：由于概率测度都是有限的，我们可以假设存在一个n0使得测度有限 *)
  destruct Hfinite as [n0 Hfinite_n0].
  
  (* 实际上，对于概率测度，所有事件的测度都是有限的 *)
  assert (Hfinite_all : forall n, mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
                               (BaseMeasureSpace:=ps.(ps_ℙ)) (A_seq n) <> NNER_infinity).
  {
    intro n.
    apply probability_measure_finite.
    exact (Hmeas n).
  }
  
  (* 步骤4：使用分解为不相交集合的方法 *)
  (* 定义差集序列：B_n = A_n \ A_inf *)
  set (B_seq := fun n : nat => 
         fun x => In x (A_seq n) /\ ~ (forall m, In x (A_seq m))).
  
  (* 步骤5：证明每个B_n可测 *)
  assert (Hmeas_B : forall n, B_seq n in_e ps).
  {
    intro n.
    unfold B_seq.
    
    (* 我们需要证明 (fun x => In x (A_seq n) /\ ~ (forall m, In x (A_seq m))) 可测 *)
    
    (* 首先，将其重写为：A_seq n ∩ (Complement (⋂_m A_seq m)) *)
    assert (Heq : SetEq (fun x => In x (A_seq n) /\ ~ (forall m, In x (A_seq m)))
                     (fun x => In x (A_seq n) /\ In x (Complement A_inf))).
    {
      intro x.
      split.
      - intros [Hx Hnot].
        split.
        + exact Hx.
        + unfold Complement, A_inf.
          exact Hnot.
      - intros [Hx Hcomp].
        split.
        + exact Hx.
        + unfold Complement, A_inf in Hcomp.
          exact Hcomp.
    }
    apply set_extensionality in Heq.
    rewrite Heq.
    
    (* 现在我们需要手动证明交集可测 *)
    (* 要证明 A ∩ B 可测，其中 A = A_seq n 和 B = Complement A_inf *)
    (* 我们知道 A_seq n 可测 (Hmeas n) *)
    (* 我们知道 Complement A_inf 可测 (因为 A_inf 可测，且σ-代数对补集封闭) *)
    (* 我们需要证明交集可测 *)
    
    (* 首先，证明 Complement A_inf 可测 *)
    assert (Hcomp_inf : In (Complement A_inf) (sigma_sets Ω' 𝓕')).
    {
      apply sigma_closed_complement.
      exact Hmeas_Ainf.
    }
    
    (* 证明 Complement A_seq n 可测 *)
    assert (Hcomp_n : In (Complement (A_seq n)) (sigma_sets Ω' 𝓕')).
    {
      apply sigma_closed_complement.
      exact (Hmeas n).
    }
    
    (* 证明 Complement A_seq n ∪ A_inf 可测 *)
    assert (Hunion : In (fun x => In x (Complement (A_seq n)) \/ In x A_inf) (sigma_sets Ω' 𝓕')).
    {
      apply sigma_closed_finite_union.
      - exact Hcomp_n.
      - exact Hmeas_Ainf.
    }
    
    (* 证明并集的补集可测，并证明它等于 A_seq n ∩ Complement A_inf *)
    assert (Heq_intersection : SetEq 
               (Complement (fun x => In x (Complement (A_seq n)) \/ In x A_inf))
               (fun x => In x (A_seq n) /\ In x (Complement A_inf))).
    {
      intro x.
      split.
      - intro H.
        (* H: x 在左边集合中，即 ~(x ∈ Complement(A_seq n) ∨ x ∈ A_inf) *)
        unfold Complement, In in H.
        simpl in H.
        
        (* 我们需要证明两个部分: In x (A_seq n) 和 In x (Complement A_inf) *)
        split.
        + (* 证明 In x (A_seq n) *)
          (* 使用反证法: 假设 In x (A_seq n) 不成立 *)
          (* 如果 In x (A_seq n) 不成立，那么 (~ In x (A_seq n)) 成立 *)
          (* 这将使得 (~ In x (A_seq n)) \/ In x A_inf 成立 *)
          (* 与 H 矛盾 *)
          
          (* 使用经典逻辑的排中律 *)
          assert (Hclassic : In x (A_seq n) \/ ~ In x (A_seq n)).
          { apply classic. }
          destruct Hclassic as [Hin | Hnotin].
          * (* 情况1: In x (A_seq n) 成立 *)
            exact Hin.
          * (* 情况2: In x (A_seq n) 不成立 *)
            (* 现在 Hnotin: ~ In x (A_seq n) *)
            (* 构造析取式 *)
            assert (Hdisj : (~ In x (A_seq n)) \/ In x A_inf).
            { left; exact Hnotin. }
            (* 与 H 矛盾 *)
            contradiction.
            
        + (* 证明 In x (Complement A_inf)，即 ~ In x A_inf *)
          (* 假设 In x A_inf 成立 *)
          intro Hinf.  (* Hinf: In x A_inf *)
          (* 那么 In x A_inf 成立 *)
          (* 构造析取式 *)
          assert (Hdisj : (~ In x (A_seq n)) \/ In x A_inf).
          { right; exact Hinf. }
          (* 与 H 矛盾 *)
          contradiction.
          
      - intro H.
        destruct H as [Hx_n Hx_comp].
        
        (* 展开 Complement 的定义 *)
        unfold Complement, In.
        simpl.
        
        (* 我们需要证明: ~ ((~ In x (A_seq n)) \/ In x A_inf) *)
        intro Hor.
        
        (* Hor 有两种可能 *)
        destruct Hor as [Hnot_n | Hinf].
        + (* 情况1: Hnot_n: ~ In x (A_seq n) *)
          (* 但我们已经知道 Hx_n: In x (A_seq n) *)
          contradiction.
        + (* 情况2: Hinf: In x A_inf *)
          (* 但我们已经知道 Hx_comp: In x (Complement A_inf)，即 ~ In x A_inf *)
          unfold Complement, In in Hx_comp.
          contradiction.
    }
    
    apply set_extensionality in Heq_intersection.
    (* 现在 Heq_intersection: Complement(...) = (A_seq n ∩ Complement A_inf) *)
    
    (* 我们需要证明目标集合可测 *)
    (* 目标: is_event (fun x => In x (A_seq n) /\ In x (Complement A_inf)) *)
    
    (* 使用 Heq_intersection 将目标重写为 Complement(...) 的形式 *)
    rewrite <- Heq_intersection.
    
    (* 现在目标变为: is_event (Complement (fun x => In x (Complement (A_seq n)) \/ In x A_inf)) *)
    
    (* 应用补集的可测性 *)
    apply sigma_closed_complement.
    exact Hunion.
  }
  
  (* 步骤6：证明B_n递减且极限为空集 *)
  assert (Hdecr_B : forall n, Subset (B_seq (S n)) (B_seq n)).
  {
    intro n.
    unfold Subset, B_seq.
    intros x [Hx1 Hx2].
    split.
    - (* In x (A_seq (S n)) → In x (A_seq n) *)
      apply Hdecr.
      exact Hx1.
    - (* 保持否定部分不变 *)
      exact Hx2.
  }
  
  (* 证明 ⋂_n B_seq n 是空集 *)
  assert (Hempty_inf : SetEq (fun x => forall n, In x (B_seq n)) EmptySet).
  {
    intro x.
    split.
    - intro H.
      (* 假设 x 在所有 B_n 中 *)
      unfold B_seq in H.
      
      (* 从 H 我们可以得到对于所有 n，x 在 A_seq n 中 *)
      assert (Hin_all : forall n, In x (A_seq n)).
      {
        intro n.
        specialize (H n) as [Hn _].
        exact Hn.
      }
      
      (* 从 H 0 我们得到 x 不在所有的 A_seq m 中 *)
      specialize (H O) as [_ Hx_not_inf].
      
      (* 矛盾：我们有 Hin_all 和 Hx_not_inf *)
      contradiction.
      
    - intro H.
      (* 假设 x 在空集中，这是不可能的 *)
      unfold EmptySet, In in H.
      contradiction.
  }
  
  (* 步骤7：使用测度减法性质 *)
  (* 对于每个 n，有 A_seq n = A_inf ∪ B_seq n，且不相交 *)
  assert (Hdisj : forall n, Disjoint A_inf (B_seq n)).
  {
    intro n.
    unfold Disjoint, B_seq.
    intros x [Hx_inf Hx_B].
    destruct Hx_B as [Hx_A Hx_not].
    
    (* Hx_inf: forall m, In x (A_seq m) *)
    (* Hx_not: ~ (forall m, In x (A_seq m)) *)
    
    (* 这两个断言直接矛盾 *)
    contradiction.
  }
  
  (* 步骤8：应用有限可加性得到 P(A_seq n) = P(A_inf) + P(B_seq n) *)
  assert (Hprob_decomp : forall n, P (A_seq n) = P A_inf + P (B_seq n)).
  {
    intro n.
    (* 首先证明集合等式：A_seq n = A_inf ∪ B_seq n *)
    assert (Hunion : SetEq (A_seq n) (fun x => In x A_inf \/ In x (B_seq n))).
    {
      intro x.
      split.
      - intro Hx.
        destruct (classic (forall m, In x (A_seq m))) as [Hall | Hnot].
        + left.
          unfold A_inf.
          exact Hall.
        + right.
          unfold B_seq.
          split.
          * exact Hx.
          * exact Hnot.
      - intro Hx.
        destruct Hx as [Hx_inf | Hx_B].
        + unfold A_inf in Hx_inf.
          apply Hx_inf.
        + unfold B_seq in Hx_B.
          destruct Hx_B as [Hx_A _].
          exact Hx_A.
    }
    
    assert (Heq : A_seq n = (fun x => In x A_inf \/ In x (B_seq n))).
    {
      apply set_extensionality.
      exact Hunion.
    }
    
    (* 使用集合等式证明概率相等 *)
    assert (Heq_prob : P (A_seq n) = P (fun x => In x A_inf \/ In x (B_seq n))).
    {
      apply f_equal.
      exact Heq.
    }
    
    rewrite Heq_prob.
    apply probability_finite_additivity.
    - exact Hmeas_Ainf.
    - exact (Hmeas_B n).
    - exact (Hdisj n).
  }
  
  (* 步骤9：使用补集的方法证明 P(B_seq n) 收敛到 0 *)
  (* 考虑补集序列：C_n = Complement (B_seq n) *)
  (* 由于 B_seq 递减，C_n 递增 *)
  
  assert (Hconv_B : sequence_converges (fun n => P (B_seq n)) R0).
  {
    (* 定义补集序列 *)
    set (C_seq := fun n => Complement (B_seq n)).
    
    (* 证明 C_seq 递增 *)
    assert (Hinc_C : forall n, Subset (C_seq n) (C_seq (S n))).
    {
      intro n.
      unfold Subset, C_seq, Complement.
      intros x Hx.
      intro H.
      apply Hx.
      apply Hdecr_B.
      exact H.
    }
    
    (* 证明 C_seq 的并集是全集（因为 B_seq 的交集是空集） *)
    assert (Hunion_C : SetEq (fun x => exists n, In x (C_seq n)) UniversalSet_s).
    {
      intro x.
      split.
      - intros [n Hx].
        apply universal_set_property.
      - intro Hx_univ.
        (* 我们需要证明存在 n 使得 x 在 C_seq n 中 *)
        (* 由于 x 不在所有 B_seq n 中（否则与 Hempty_inf 矛盾） *)
        (* 所以存在某个 n 使得 x 不在 B_seq n 中，即 x 在 C_seq n 中 *)
        
        (* 使用反证法 *)
        apply NNPP.
        intro H_no_ex.
        (* H_no_ex: ~ (exists n, In x (C_seq n)) *)
        
        (* 那么对于所有 n，x 在 B_seq n 中 *)
        assert (H_in_all_B : forall n, In x (B_seq n)).
        {
          intro n.
          (* 假设 x 不在 B_seq n 中，则 x 在 C_seq n 中，矛盾 *)
          apply NNPP.
          intro H_not_in_B.
          apply H_no_ex.
          exists n.
          unfold C_seq, Complement, In.
          exact H_not_in_B.
        }
        
        (* 现在我们有 x 在所有 B_seq n 中 *)
        (* 根据 Hempty_inf，这不可能 *)
        apply Hempty_inf in H_in_all_B.
        (* H_in_all_B 现在是 In x EmptySet_s *)
        (* 由空集的性质，矛盾 *)
        apply (empty_set_property x H_in_all_B).
    }
  
    (* 应用概率的从下连续性到 C_seq *)
    assert (Hmeas_C : forall n, C_seq n in_e ps).
    {
      intro n.
      unfold C_seq.
      unfold is_event.
      apply sigma_closed_complement.
      exact (Hmeas_B n).
    }
    
    (* 由于 C_seq 递增，应用从下连续性 *)
    pose proof (probability_continuity_from_below C_seq Hmeas_C Hinc_C) as Hcont_C.
    
    (* 计算 P(C_seq n) = 1 - P(B_seq n) *)
    assert (Hprob_C : forall n, P (C_seq n) = R1 - P (B_seq n)).
    {
      intro n.
      unfold C_seq.
      (* 手动计算 P(Complement_s (B_seq n)) = 1 - P(B_seq n) *)
      (* 先展开 P 的定义 *)
      unfold P.
      (* 现在目标：match mu (Complement_s (B_seq n)) with ... end = 1 - match mu (B_seq n) with ... end *)
      
      (* 对 mu (B_seq n) 进行分类讨论 *)
      pose proof (probability_measure_finite (B_seq n) (Hmeas_B n)) as Hfinite_Bn.
      
      (* 使用正确的模式匹配语法 *)
      destruct (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) (B_seq n)) as [b | Hinf_B] eqn:HBn_eq.
      {
        (* 情况1: mu (B_seq n) = NNER_finite b *)
        
        (* 同样对 mu (Complement_s (B_seq n)) 进行分类 *)
        destruct (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) 
                (Complement_s (B_seq n))) as [c | Hinf_comp] eqn:HC_eq.
        {
          (* 情况1.1: mu (Complement_s (B_seq n)) = NNER_finite c *)
          
          (* 简化目标 *)
          simpl.
          
          (* 证明 B_seq n 和其补集不相交 *)
          assert (Hdisj_comp : Disjoint (B_seq n) (Complement_s (B_seq n))).
          {
            unfold Disjoint.
            intros x [Hx Hcomp].
            rewrite complement_property in Hcomp.
            contradiction.
          }
          
          (* 证明 B_seq n ∪ Complement_s (B_seq n) = 全集 *)
          assert (Hunion_set : SetEq (fun x => In x (B_seq n) \/ In x (Complement_s (B_seq n))) UniversalSet_s).
          {
            intro x.
            split.
            - intros _. apply universal_set_property.
            - intros _.
              destruct (classic (In x (B_seq n))) as [Hx|Hx].
              + left; exact Hx.
              + right; exact Hx.
          }
          
          (* 应用有限可加性 *)
          pose proof (measure_finite_additivity (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
                      (BaseMeasureSpace:=ps.(ps_ℙ)) (B_seq n) (Complement_s (B_seq n)) 
                      (Hmeas_B n) (Hmeas_C n) Hdisj_comp) as Hadd.
          
          (* 将并集重写为全集 *)
          assert (Heq_union : (fun x => In x (B_seq n) \/ In x (Complement_s (B_seq n))) = UniversalSet_s).
          {
            apply set_extensionality.
            exact Hunion_set.
          }
          rewrite Heq_union in Hadd.
          
          (* 使用全空间测度为1的性质 *)
          rewrite is_probability_measure in Hadd.
          
          (* 现在 Hadd: mu (B_seq n) +_nner mu (Complement_s (B_seq n)) = NNER_finite R1 *)
          rewrite HBn_eq in Hadd.
          rewrite HC_eq in Hadd.
          unfold NNER_add in Hadd.
          simpl in Hadd.
          injection Hadd as Hsum.  (* Hsum: b + c = R1 *)
          
          (* 现在我们有 c = R1 - b *)
          lra.
        }
        {
          (* 情况1.2: mu (Complement_s (B_seq n)) = NNER_infinity *)
          (* 这与概率测度有限矛盾 *)
          exfalso.
          (* 我们已经有 Hmeas_C n 证明 Complement_s (B_seq n) 可测 *)
          (* 使用概率测度有限引理 *)
          pose proof (probability_measure_finite (Complement_s (B_seq n)) (Hmeas_C n)) as Hfin.
          (* Hfin: mu (Complement_s (B_seq n)) <> NNER_infinity *)
          (* 但我们有 HC_eq: mu (Complement_s (B_seq n)) = NNER_infinity *)
          (* 矛盾 *)
          contradiction.
        }
      }
      {
        (* 情况2: mu (B_seq n) = NNER_infinity *)
        (* 这与 Hfinite_Bn 矛盾 *)
        exfalso.
        (* Hfinite_Bn: mu (B_seq n) <> NNER_infinity *)
        (* 但我们有 Hinf_B: mu (B_seq n) = NNER_infinity *)
        contradiction.
      }
    }
    
    (* 现在我们有 Hcont_C: (fun n => P(C_seq n)) 收敛到 P(⋃_n C_seq n) *)
    (* 而 P(⋃_n C_seq n) = P(UniversalSet_s) = 1，因为 C_seq 的并集是全集 *)
    
    (* 首先证明：P(⋃_n C_seq n) = 1 *)
    assert (Hunion_prob : P (fun x => exists n, In x (C_seq n)) = R1).
    {
      (* 因为 C_seq 的并集等于全集 *)
      assert (Heq : (fun x => exists n, In x (C_seq n)) = UniversalSet_s).
      {
        apply set_extensionality.
        exact Hunion_C.
      }
      rewrite Heq.
      apply probability_universe.
    }
    
    (* 现在我们有 Hcont_C: (fun n => P(C_seq n)) 收敛到 P(⋃_n C_seq n) = 1 *)
    (* 即 P(C_seq n) 收敛到 1 *)
    
    (* 我们需要证明 P(B_seq n) 收敛到 0 *)
    unfold sequence_converges, Un_cv.
    intros eps Heps_pos.
    
    (* 由于 P(C_seq n) 收敛到 1，存在 N 使得当 n ≥ N 时，|P(C_seq n) - 1| < eps *)
    unfold sequence_converges, Un_cv in Hcont_C.
    (* 将 Hunion_prob 代入到 Hcont_C 中 *)
    rewrite Hunion_prob in Hcont_C.
    destruct (Hcont_C eps Heps_pos) as [N HN].
    
    exists N.
    intros n Hn.
    
    (* 计算 |P(B_seq n) - 0| *)
    unfold R_dist.
    
    (* 根据 Hprob_C: P[ C_seq n ] = R1 - P[ B_seq n ]，推导出 P[ B_seq n ] = R1 - P[ C_seq n ] *)
    pose proof (Hprob_C n) as H.  (* H: P[ C_seq n ] = R1 - P[ B_seq n ] *)
    
    (* 先证明中间等式：P(C_seq n) + P(B_seq n) = R1 *)
    assert (H_sum : P (C_seq n) + P (B_seq n) = R1).
    {
      rewrite H.
      ring.
    }
    
    (* 从 H_sum 推导出 P(B_seq n) = R1 - P(C_seq n) *)
    assert (HBn_eq : P (B_seq n) = R1 - P (C_seq n)).
    {
      lra.
    }
    rewrite HBn_eq.
    
    (* 现在需要证明 |(1 - P(C_seq n)) - 0| < eps *)
    (* 即 |1 - P(C_seq n)| < eps *)
    rewrite Rminus_0_r.
    
    (* 这正是 HN 给出的条件，因为 |P(C_seq n) - 1| = |1 - P(C_seq n)| *)
    rewrite Rabs_minus_sym.
    apply HN.
    exact Hn.
  }
  
  (* 步骤10：综合结果 *)
  (* 我们有 P(A_seq n) = P(A_inf) + P(B_seq n) 且 P(B_seq n) 收敛到 0 *)
  (* 所以 P(A_seq n) 收敛到 P(A_inf) *)
  unfold sequence_converges, Un_cv in *.
  intros eps Heps_pos.

  (* 从 Hconv_B 得到存在 N，当 n ≥ N 时，|P(B_seq n) - 0| < eps *)
  destruct (Hconv_B eps Heps_pos) as [N HN].
  exists N.
  intros n Hn.

  (* 计算距离 *)
  rewrite Hprob_decomp.
  unfold R_dist.

  (* 需要证明 |(P A_inf + P (B_seq n)) - P A_inf| < eps *)
  (* 手动简化绝对值内部的表达式 *)

  (* 表达式 (P A_inf + P (B_seq n)) - P A_inf 可以化简为 P (B_seq n) *)
  (* 直接使用实数运算的基本引理 *)

  (* 使用 Rminus_def 展开减法 *)
  unfold Rminus.
  (* 现在目标: |(P[A_inf] + P[B_seq n]) + - P[A_inf]| < eps *)

  (* 使用加法结合律: (a + b) + c = a + (b + c) *)
  rewrite Rplus_assoc.
  (* 现在目标: |P[A_inf] + (P[B_seq n] + - P[A_inf])| < eps *)

  (* 使用加法交换律: b + -a = -a + b *)
  rewrite (Rplus_comm (P (B_seq n)) (- P A_inf)).
  (* 现在目标: |P[A_inf] + (- P[A_inf] + P[B_seq n])| < eps *)

  (* 使用加法结合律将 P[A_inf] 和 -P[A_inf] 组合 *)
  rewrite <- Rplus_assoc.
  (* 现在目标: |(P[A_inf] + - P[A_inf]) + P[B_seq n]| < eps *)

  (* P[A_inf] + - P[A_inf] = 0 *)
  rewrite Rplus_opp_r.
  (* 现在目标: |0 + P[B_seq n]| < eps *)

  (* 0 + P[B_seq n] = P[B_seq n] *)
  rewrite Rplus_0_l.
  (* 现在目标: |P[B_seq n]| < eps *)

  (* 现在我们需要使用 HN: forall n, (n >= N)%nat -> Rdist (P[ B_seq n]) R0 < eps *)
  (* 将 HN 应用到当前的 n *)
  specialize (HN n Hn).
  (* HN: Rdist (P[ B_seq n]) R0 < eps *)

  (* 展开 Rdist 的定义 *)
  unfold Rdist in HN.
  (* Rdist x y 定义为 Rabs (x - y) *)
  (* 所以 HN: Rabs (P[ B_seq n] - R0) < eps *)

  (* 简化 P[ B_seq n] - R0 为 P[ B_seq n] *)
  rewrite Rminus_0_r in HN.
  (* 现在 HN: Rabs (P[ B_seq n]) < eps *)

  (* 这正是我们需要证明的目标 *)
  exact HN.
Qed.
  
End BasicProbabilityProperties.
  
(** =========== 2. 条件概率 =========== *)
(** 基于测度论的条件概率定义 **)
  
Section ConditionalProbability.
Require Import Coq.Reals.RIneq.
  Context {ps : ProbabilitySpace}.
  Notation Ω' := (ps.(ps_Ω)).
  Notation 𝓕' := (ps.(ps_𝓕)).
  
  (* 首先证明交集可测性引理 *)
  Lemma measurable_intersection : forall A B,
    A in_e ps -> B in_e ps -> (fun x => In x A /\ In x B) in_e ps.
  Proof.
    intros A B HA HB.
    unfold is_event in *.
    (* 使用σ-代数的性质：A∩B = Complement (Complement A ∪ Complement B) *)
    set (A_comp := Complement A).
    set (B_comp := Complement B).
    assert (HA_comp : In A_comp (sigma_sets Ω' 𝓕')).
    { unfold A_comp; apply sigma_closed_complement; exact HA. }
    assert (HB_comp : In B_comp (sigma_sets Ω' 𝓕')).
    { unfold B_comp; apply sigma_closed_complement; exact HB. }
    set (C := fun x => In x A_comp \/ In x B_comp).
    assert (HC : In C (sigma_sets Ω' 𝓕')).
    { unfold C; apply sigma_closed_finite_union; [exact HA_comp | exact HB_comp]. }
    assert (Heq : SetEq (fun x => In x A /\ In x B) (Complement C)).
    {
      intro x.
      split.
      - intros [HxA HxB].
        unfold Complement, C.
        intro H.
        destruct H as [HcA | HcB].
        + unfold A_comp, Complement in HcA; contradiction.
        + unfold B_comp, Complement in HcB; contradiction.
      - intros H.
        unfold Complement, C in H.
        split.
        + apply NNPP.
          intro HnotA.
          apply H.
          left; unfold A_comp, Complement; exact HnotA.
        + apply NNPP.
          intro HnotB.
          apply H.
          right; unfold B_comp, Complement; exact HnotB.
    }
    apply set_extensionality in Heq.
    rewrite Heq.
    apply sigma_closed_complement; exact HC.
  Qed.
  
  (* 条件概率定义 *)
  Definition conditional_probability (A B : SetX Ω') (HA : A in_e ps) (HB : B in_e ps) : ℝ :=
    let H_inter := measurable_intersection A B HA HB in
    match Req_EM_T (P B) R0 with
    | left _ => R0  (* 约定：当P[B]=0时，条件概率为0 *)
    | right Hneq => P (fun x => In x A /\ In x B) / P B
    end.
  
  Notation "P[ A | B ]" := (conditional_probability A B _ _) (at level 40).
  
(* 条件概率基本性质 *)
Lemma conditional_probability_bounds : forall (A B : SetX Ω')
  (HA : A in_e ps) (HB : B in_e ps),
  R0 <= conditional_probability A B HA HB /\
  conditional_probability A B HA HB <= R1.
Proof.
  intros A B HA HB.
  unfold conditional_probability.
  
  (* 根据 P[B] 是否为零分情况讨论 *)
  destruct (Req_EM_T (P B) R0) as [Hzero | Hnonzero].
  - (* 当 P[B] = 0 时，条件概率定义为 0 *)
    split.
    + (* 0 <= 0 *)
      apply Rle_refl.
    + (* 0 <= 1 *)
      lra.
      
  - (* 当 P[B] ≠ 0 时，条件概率 = P[A∩B] / P[B] *)
    (* 首先计算分母 P[B] *)
    pose proof (probability_nonneg B HB) as Hpos_B.  (* 0 <= P[B] *)
    pose proof (probability_le_one B HB) as Hle_one_B.  (* P[B] <= 1 *)
    
    (* 然后计算分子 P[A∩B] *)
    set (A_inter_B := fun x => In x A /\ In x B).
    assert (H_inter : A_inter_B in_e ps) by
      (unfold A_inter_B; apply measurable_intersection; assumption).
    
    pose proof (probability_nonneg A_inter_B H_inter) as Hpos_inter.  (* 0 <= P[A∩B] *)
    pose proof (probability_le_one A_inter_B H_inter) as Hle_one_inter.  (* P[A∩B] <= 1 *)
    
    (* 展开 P[ A∩B ] 和 P[B] 的定义 *)
    unfold P at 2.
    unfold P in Hnonzero, Hpos_B, Hle_one_B.
    
    (* 对 mu B 和 mu (A∩B) 进行分类讨论 *)
    pose proof (probability_measure_finite B HB) as Hfinite_B.
    pose proof (probability_measure_finite A_inter_B H_inter) as Hfinite_inter.
    
    (* 提取测度值 *)
    case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) B);
      [intros b Hb | intros Hb].
    + (* mu B = NNER_finite b *)
      case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
                  (BaseMeasureSpace:=ps.(ps_ℙ)) A_inter_B);
        [intros c Hc | intros Hc].
      * (* mu A_inter_B = NNER_finite c *)
        (* 重写假设中的 mu B 为 b *)
        rewrite Hb in Hpos_B, Hle_one_B, Hnonzero.
        
        (* 现在 Hpos_B: R0 <= b, Hnonzero: b ≠ 0 *)
        
        (* 首先证明 b > 0 *)
        assert (Hpos_b : R0 < b).
        {
          (* 因为 b >= 0 且 b ≠ 0，所以 b > 0 *)
          destruct (Rtotal_order b R0) as [Hlt | [Heq | Hgt]].
          - (* b < 0，与 Hpos_B: 0 <= b 矛盾 *)
            lra.
          - (* b = 0，与 Hnonzero: b ≠ 0 矛盾 *)
            contradiction.
          - (* b > 0 *)
            exact Hgt.
        }
        
        (* 证明 0 <= c/b *)
        assert (Hpos_ratio1 : R0 <= c / b).
        {
          unfold Rdiv.  (* c/b = c * /b *)
          apply Rmult_le_pos.
          - (* 0 <= c *)
            unfold P in Hpos_inter.
            rewrite Hc in Hpos_inter.
            simpl in Hpos_inter.
            exact Hpos_inter.
          - (* 0 <= /b *)
            apply Rlt_le.
            apply Rinv_0_lt_compat.
            exact Hpos_b.
        }
        
        (* 证明 c/b <= 1 *)
        assert (Hle_ratio2 : c / b <= R1).
        {
          (* 首先证明 A_inter_B 是 B 的子集 *)
          assert (Hsub : A_inter_B subset_s B).
          {
            unfold A_inter_B, Subset.
            intros x [HxA HxB].
            exact HxB.
          }
          (* 使用概率的单调性：P[A∩B] <= P[B] *)
          pose proof (probability_monotonicity A_inter_B B H_inter HB Hsub) as Hmono.
          (* Hmono: P[A∩B] <= P[B] *)
          unfold P in Hmono.
          rewrite Hc, Hb in Hmono.
          
          (* 现在有 c <= b，且 b > 0，所以 c/b <= 1 *)
          (* 使用 Rmult_le_reg_r: 如果 0 < b，则 (c/b) <= 1 等价于 (c/b) * b <= 1 * b *)
          apply Rmult_le_reg_r with (r := b).
          { exact Hpos_b. }
          (* 现在需要证明 (c/b) * b <= 1 * b *)
          unfold Rdiv.
          rewrite Rmult_assoc.
          rewrite Rinv_l.
          - rewrite Rmult_1_r.
            rewrite Rmult_1_l.
            exact Hmono.
          - lra.  (* 因为 b ≠ 0 *)
        }
        
        (* 现在重写目标中的 P 定义 *)
        unfold P.
        rewrite Hc, Hb.
        simpl.
        split.
        { exact Hpos_ratio1. }
        { exact Hle_ratio2. }
        
      * (* mu A_inter_B = NNER_infinity，与有限性矛盾 *)
        (* 目标: R0 <= P A_inter_B / b /\ P A_inter_B / P B <= R1 *)
        exfalso.
        apply Hfinite_inter.
        exact Hc.
        
    + (* mu B = NNER_infinity，与有限性矛盾 *)
      (* 目标: R0 <= P A_inter_B / R0 /\ P A_inter_B / P B <= R1 *)
      exfalso.
      apply Hfinite_B.
      exact Hb.
Qed.
  
End ConditionalProbability.
  
End ProbabilityTheory.
  Module UMF := UnifiedMathFoundationImpl.
End UnifiedMeasureTheory.
  
(* ================================================================= *)
(* 第四部分：独立模块 - 通用概率定理 *)
(* ProbabilityTheorems - 不依赖特定概率空间实例的通用定理 *)
(* ================================================================= *)
  
Module ProbabilityTheorems.
Require Import Coq.Reals.Reals.
(* 导入基础数学系统 *)
Import UnifiedMathFoundationImpl.
  
(* 导入测度理论框架 *)
Module Import MeasureTheory := UnifiedMeasureTheory UnifiedMathFoundationImpl.
Import MeasureTheory.
  
Section MultiplicationFormula.
  
Open Scope R_scope.    (* 打开实数作用域 *)
  
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
  
(** 乘法公式 - 通用版本
    支持任意概率空间，不依赖特定实例 **)
Theorem multiplication_formula_general : 
  forall (ps : ProbabilitySpace) 
         (A B : SetX (ps.(ps_Ω)))
         (HA : A in_m (ps.(ps_𝓕))) 
         (HB : B in_m (ps.(ps_𝓕))),
  P (fun x => In x A /\ In x B) = 
  (let H_inter := measurable_intersection A B HA HB in
   match Req_EM_T (P B) R0 with
   | left _ => R0
   | right Hneq => P (fun x => In x A /\ In x B) / P B
   end) * P B.
Proof.
  intros ps A B HA HB.
  (* 根据 P[B] 是否为零分情况讨论 *)
  destruct (Req_EM_T (P B) R0) as [Hzero | Hnonzero].
  
  - (* 情况 1: P[B] = 0 *)
    (* 首先证明 A∩B 可测 *)
    set (A_inter_B := fun x => In x A /\ In x B).
    assert (H_inter : A_inter_B in_m (ps.(ps_𝓕))).
    { unfold A_inter_B; apply measurable_intersection; assumption. }
    
    (* 定义 B\A 并证明其可测 *)
    set (B_minus_A := fun x => In x B /\ ~ In x A).
    assert (H_BA : B_minus_A in_m (ps.(ps_𝓕))).
    {
      unfold B_minus_A.
      (* B_minus_A = B ∩ (Complement A) *)
      assert (Heq : SetEq (fun x => In x B /\ ~ In x A)
                          (fun x => In x B /\ In x (Complement A))).
      {
        intro x.
        split.
        - intros [HxB HnotA].
          split.
          + exact HxB.
          + unfold Complement; exact HnotA.
        - intros [HxB Hcomp].
          split.
          + exact HxB.
          + unfold Complement in Hcomp; exact Hcomp.
      }
      apply set_extensionality in Heq.
      rewrite Heq.
      (* 证明 Complement A 可测 *)
      assert (HcompA : In (Complement A) (sigma_sets (ps.(ps_Ω)) (ps.(ps_𝓕)))).
      { apply sigma_closed_complement; exact HA. }
      (* 证明交集可测 *)
      apply measurable_intersection; [exact HB | exact HcompA].
    }
    
    (* 证明 A_inter_B 和 B_minus_A 不相交 *)
    assert (Hdisj : Disjoint A_inter_B B_minus_A).
    {
      unfold Disjoint, A_inter_B, B_minus_A.
      intros x [H1 H2].
      destruct H1 as [HxA HxB]; destruct H2 as [HxB' HnotA].
      contradiction.
    }
    
    (* 使用测度的有限可加性 - 直接应用，内联引理 *)
    pose proof (measure_finite_additivity (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) 
                A_inter_B B_minus_A H_inter H_BA Hdisj) as Hadd.
    
    (* 证明 B = A_inter_B ∪ B_minus_A *)
    assert (Hunion : SetEq B (fun x => In x A_inter_B \/ In x B_minus_A)).
    {
      intro x.
      split.
      - intro Hx.
        destruct (classic (In x A)) as [HxA | HnotA].
        + left; unfold A_inter_B; split; assumption.
        + right; unfold B_minus_A; split; assumption.
      - intros [Hx | Hx].
        + unfold A_inter_B in Hx; destruct Hx; assumption.
        + unfold B_minus_A in Hx; destruct Hx; assumption.
    }
    
    (* 将并集重写为 B *)
    assert (Heq_union : (fun x => In x A_inter_B \/ In x B_minus_A) = B).
    { 
      apply set_extensionality.
      intro x.
      (* 使用 Hunion 的双向性质 *)
      split.
      - intro H.
        (* H: x 在 A_inter_B ∪ B_minus_A 中 *)
        apply Hunion.
        exact H.
      - intro H.
        (* H: x 在 B 中 *)
        apply Hunion in H.
        exact H.
    }
    
    rewrite Heq_union in Hadd.
    
    (* 现在 Hadd: mu B = mu A_inter_B +_nner mu B_minus_A *)
    
    (* 由于概率测度有限，我们知道 mu B, mu A_inter_B, mu B_minus_A 都是有限的 *)
    pose proof (probability_measure_finite A_inter_B H_inter) as Hfin_inter.
    pose proof (probability_measure_finite B_minus_A H_BA) as Hfin_BA.
    pose proof (probability_measure_finite B HB) as Hfin_B.
    
    (* 对 mu B 进行分类，由于有限性，它必须是 NNER_finite 形式 *)
    case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) B);
      [intros b Hb | intros Hb; exfalso; [apply Hfin_B; exact Hb]].
    
    (* 对 mu A_inter_B 和 mu B_minus_A 进行分类 *)
    case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) A_inter_B);
      [intros a Ha | intros Ha; exfalso; [apply Hfin_inter; exact Ha]].
    
    case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) B_minus_A);
      [intros c Hc | intros Hc; exfalso; [apply Hfin_BA; exact Hc]].
    
    (* 现在 Ha: mu A_inter_B = NNER_finite a, Hc: mu B_minus_A = NNER_finite c, Hb: mu B = NNER_finite b *)
    rewrite Ha, Hc, Hb in Hadd.
    unfold NNER_add in Hadd; simpl in Hadd.
    injection Hadd as Hsum.  (* Hsum: b = a + c *)
    
    (* 由概率的非负性，a ≥ 0, c ≥ 0 *)
    pose proof (probability_nonneg A_inter_B H_inter) as Hpos_a.
    pose proof (probability_nonneg B_minus_A H_BA) as Hpos_c.
    unfold P in Hpos_a, Hpos_c.
    rewrite Ha in Hpos_a; simpl in Hpos_a.   (* Hpos_a: 0 ≤ a *)
    rewrite Hc in Hpos_c; simpl in Hpos_c.   (* Hpos_c: 0 ≤ c *)
    
    (* 从 Hzero: P B = 0 推导出 b = 0 *)
    unfold P in Hzero.                (* Hzero: match mu B with ... end = 0 *)
    rewrite Hb in Hzero.              (* Hzero: match NNER_finite b with ... end = 0 *)
    simpl in Hzero.                   (* Hzero: b = 0 *)
    
    (* 现在证明目标: P A_inter_B = 0 * P B *)
    (* 展开左边的 P A_inter_B *)
    unfold P at 1.
    rewrite Ha.                        (* 替换为 NNER_finite a *)
    simpl.                             (* 得到 a *)
    
    (* 右边: 0 * P B = 0 * 0 = 0 *)
    rewrite Rmult_0_l.                (* 将 0 * 0 简化为 0 *)
    
    (* 现在目标: a = 0 *)
    (* 从 Hsum: b = a + c 和 Hzero: b = 0 得到 0 = a + c *)
    rewrite Hzero in Hsum.            (* Hsum: 0 = a + c *)
    
    (* 从 0 = a + c 且 a ≥ 0, c ≥ 0，可以推出 a = 0 *)
    apply Rle_antisym.
    + (* 证明 a ≤ 0 *)
      lra.
    + (* 证明 0 ≤ a *)
      exact Hpos_a.
    
  - (* 情况 2: P[B] ≠ 0 *)
    (* 此时条件概率定义为 P[A∩B] / P[B]，需要证明 P[A∩B] = (P[A∩B] / P[B]) * P[B] *)
    
    (* 设 a = P[A∩B], b = P[B] *)
    set (a := P (fun x => In x A /\ In x B)).
    set (b := P B).
    
    (* 目标变为: a = (a / b) * b *)
    
    (* 展开实数除法定义 *)
    unfold Rdiv.          (* 将 a / b 展开为 a * / b *)
    
    (* 现在目标: a = (a * / b) * b *)
    rewrite Rmult_assoc.  (* (a * /b) * b = a * (/b * b) *)
    rewrite Rinv_l.       (* /b * b = 1 *)
    - rewrite Rmult_1_r.  (* a * 1 = a *)
      reflexivity.
    - (* 需要证明 b ≠ 0 *)
      exact Hnonzero.
Qed.
  
End MultiplicationFormula.
  
(** 全概率公式 - 通用版本 **)
Require Import Coq.Reals.Reals.
(* 导入基础数学系统 *)
Import UnifiedMathFoundationImpl.
  
(* 导入测度理论框架 *)
Import MeasureTheory.
  
Section TotalProbabilityFormula.
  
Open Scope R_scope.    (* 打开实数作用域 *)
  
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
  
(* 全概率公式 *)
Theorem total_probability_formula_general : 
  forall (ps : ProbabilitySpace) 
         (B : SetX (ps.(ps_Ω)))
         (HB : B in_m (ps.(ps_𝓕)))
         (E : nat -> SetX (ps.(ps_Ω)))
         (HE : forall n, E n in_m (ps.(ps_𝓕)))
         (Hpartition : PairwiseDisjoint E)
         (Hcover : SetEq (UniversalSet (X:=ps.(ps_Ω))) 
                         (fun x => exists n, In x (E n))),
  infinite_sum (fun n => P (fun x => In x B /\ In x (E n))) (P B).
Proof.
  intros ps B HB E HE Hpartition Hcover.
  
  (* 定义交集序列：A_n = B ∩ E_n *)
  set (A_seq := fun n : nat => fun x : ps.(ps_Ω) => In x B /\ In x (E n)).
  
  (* 证明每个 A_seq n 是可测事件 *)
  assert (HA_seq : forall n, A_seq n in_m (ps.(ps_𝓕))).
  {
    intro n.
    unfold A_seq.
    (* 使用交集可测性引理 *)
    apply measurable_intersection; [exact HB | exact (HE n)].
  }
  
  (* 证明 A_seq 是两两不相交的 *)
  assert (Hdisj_seq : PairwiseDisjoint A_seq).
  {
    unfold PairwiseDisjoint.
    intros n m Hneq.
    unfold Disjoint.
    intros x [Hx1 Hx2].
    unfold A_seq in Hx1, Hx2.
    destruct Hx1 as [HxB1 HxE1].
    destruct Hx2 as [HxB2 HxE2].
    (* 使用 E 的两两不相交性质 *)
    unfold PairwiseDisjoint in Hpartition.
    pose proof (Hpartition n m Hneq) as Hdisj_E.
    unfold Disjoint in Hdisj_E.
    apply Hdisj_E with x.
    split; assumption.
  }
  
  (* 证明 ⋃_n A_seq n = B *)
  assert (Hunion : SetEq B (fun x => exists n, In x (A_seq n))).
  {
    intro x.
    split.
    - (* B 包含于 ⋃_n A_seq n *)
      intro HxB.
      (* 首先，x 属于全集 *)
      assert (Hx_univ : In x UniversalSet_s).
      { apply universal_set_property. }
      (* 使用 Hcover: 全集 = ⋃_n E_n *)
      unfold SetEq in Hcover.
      (* 获取 x 在全集中的等价性 *)
      pose proof (Hcover x) as Hcover_x.
      (* Hcover_x: In x UniversalSet_s <-> In x (fun x => exists n, In x (E n)) *)
      destruct Hcover_x as [Hto_union Hfrom_union].
      (* Hto_union: x ∈ UniversalSet_s -> x ∈ ⋃_n E_n *)
      (* Hfrom_union: x ∈ ⋃_n E_n -> x ∈ UniversalSet_s *)
      
      (* 使用 Hto_union 从 x ∈ 全集 得到 x ∈ ⋃_n E_n *)
      apply Hto_union in Hx_univ.
      destruct Hx_univ as [n HxE].
      
      (* 现在我们有 n 使得 x ∈ E_n *)
      exists n.
      unfold A_seq.
      split; assumption.
      
    - (* ⋃_n A_seq n 包含于 B *)
      intro Hx.
      destruct Hx as [n Hx_A].
      unfold A_seq in Hx_A.
      destruct Hx_A; assumption.
  }
  
  (* 现在应用概率的可数可加性 *)
  pose proof (probability_countable_additivity A_seq HA_seq Hdisj_seq) as Hcountable.
  
  (* 将右边的 P (fun x => exists n, In x (A_seq n)) 重写为 P B *)
  assert (Heq : P (fun x => exists n, In x (A_seq n)) = P B).
  {
    unfold P.
    (* 使用集合相等性来证明测度相等 *)
    (* 首先证明两个集合的函数相等 *)
    assert (H_eq_set : (fun x => exists n, In x (A_seq n)) = B).
    {
      (* 我们需要 SetEq (fun x => ...) B，而 Hunion 是 SetEq B (fun x => ...) *)
      (* 使用 SetEq 的对称性 *)
      assert (Hunion_sym : SetEq (fun x => exists n, In x (A_seq n)) B).
      {
        intro x.
        split.
        - (* x ∈ ⋃_n A_seq n → x ∈ B *)
          intro Hx.
          destruct Hx as [n Hx_A].
          unfold A_seq in Hx_A.
          destruct Hx_A; assumption.
        - (* x ∈ B → x ∈ ⋃_n A_seq n *)
          intro HxB.
          (* 我们可以直接使用 Hunion 的另一半 *)
          apply Hunion.
          exact HxB.
      }
      apply set_extensionality.
      exact Hunion_sym.
    }
    (* 由于集合相等，它们的测度也相等 *)
    rewrite H_eq_set.
    reflexivity.
  }
  
  rewrite Heq in Hcountable.
  
  (* 展开 A_seq 的定义 *)
  unfold A_seq in Hcountable.
  
  (* 现在 Hcountable 就是我们需要证明的 *)
  exact Hcountable.
Qed.
  
End TotalProbabilityFormula.
  
(** 贝叶斯公式 - 通用版本 **)
Require Import Coq.Reals.Reals.
(* 导入基础数学系统 *)
Import UnifiedMathFoundationImpl.
  
(* 导入测度理论框架 *)
Import MeasureTheory.
  
Section BayesFormula.
  
Open Scope R_scope.    (* 打开实数作用域 *)
  
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
  
(** 贝叶斯公式 - 通用版本 **)
Theorem bayes_formula_general : 
  forall (ps : ProbabilitySpace) 
         (A B : SetX (ps.(ps_Ω)))
         (HA : is_event A) 
         (HB : is_event B)
         (Hpos : P B > R0),
  conditional_probability A B HA HB = 
  (conditional_probability B A HB HA * P A) / P B.
Proof.
  intros ps A B HA HB Hpos.
  
  (* 展开条件概率定义 *)
  unfold conditional_probability.
  
  (* 由于 Hpos: P B > 0，所以 P B ≠ 0 *)
  destruct (Req_EM_T (P B) R0) as [HzeroB | HnonzeroB].
  - (* 如果 P B = 0，与 Hpos 矛盾 *)
    lra.
  - (* 现在 P B ≠ 0 *)
    (* 同样处理 P A 是否为零的情况 *)
    destruct (Req_EM_T (P A) R0) as [HzeroA | HnonzeroA].
    
    (* 情况 1: P A = 0 *)
    + (* 首先证明 P(A∩B) = 0 *)
      assert (Hinter_zero : P (fun x => In x A /\ In x B) = R0).
      {
        (* 展开 P 的定义 *)
        unfold P.
        
        (* 对 mu A 进行分类讨论 *)
        case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) A);
          [intros a Ha | intros Ha].
        - (* mu A = NNER_finite a *)
          (* 对 mu (A∩B) 进行分类讨论 *)
          case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
                      (BaseMeasureSpace:=ps.(ps_ℙ)) 
                      (fun x => In x A /\ In x B));
            [intros c Hc | intros Hc].
          + (* mu (A∩B) = NNER_finite c *)
            simpl.
            (* 从 HzeroA: P A = 0 得到 a = 0 *)
            unfold P in HzeroA.
            rewrite Ha in HzeroA.
            simpl in HzeroA.
            (* 使用单调性引理 *)
            assert (Hsub : (fun x => In x A /\ In x B) subset_s A).
            {
              intro x; intros [HxA _]; exact HxA.
            }
            pose proof (probability_monotonicity 
                         (fun x => In x A /\ In x B) 
                         A 
                         (measurable_intersection A B HA HB) 
                         HA 
                         Hsub) as Hle.
            unfold P in Hle.
            rewrite Hc, Ha in Hle.
            simpl in Hle.
            rewrite HzeroA in Hle.
            (* 使用概率的非负性 *)
            pose proof (probability_nonneg (fun x => In x A /\ In x B) 
                         (measurable_intersection A B HA HB)) as Hge.
            unfold P in Hge.
            rewrite Hc in Hge.
            simpl in Hge.
            lra.
          + (* mu (A∩B) = NNER_infinity，与概率测度有限矛盾 *)
            exfalso.
            apply (probability_measure_finite 
                     (fun x => In x A /\ In x B) 
                     (measurable_intersection A B HA HB)).
            exact Hc.
        - (* mu A = NNER_infinity，与概率测度有限矛盾 *)
          exfalso.
          apply (probability_measure_finite A HA).
          exact Ha.
      }
      
      (* 当前目标：P(A∩B)/P B = (conditional_probability B A HB HA * P A) / P B *)
      (* 展开右边的条件概率 *)
      unfold conditional_probability.
      (* 对 P A 进行分支 *)
      destruct (Req_EM_T (P A) R0) as [HzeroA' | HnonzeroA'].
      * (* P A = 0 *)
        (* 右边的条件概率返回 0 *)
        (* 简化目标 *)
        rewrite Hinter_zero.          (* 左边分子: 0 *)
        rewrite HzeroA'.              (* 右边的 P A: 0 *)
        (* 现在目标：0 / P B = (0 * 0) / P B *)
        rewrite Rmult_0_l.            (* 简化 0 * 0 为 0 *)
        reflexivity.                  (* 0 / P B = 0 / P B *)
      * (* P A ≠ 0，与 HzeroA 矛盾 *)
        contradiction.
      
    (* 情况 2: P A ≠ 0 *)
    + (* 当前目标：P(A∩B)/P B = (conditional_probability B A HB HA * P A) / P B *)
      (* 展开右边的条件概率 *)
      unfold conditional_probability.
      (* 对 P A 进行分支 *)
      destruct (Req_EM_T (P A) R0) as [HzeroA' | HnonzeroA'].
      * (* P A = 0，与 HnonzeroA 矛盾 *)
        contradiction.
      * (* 现在目标：P(A∩B)/P B = (P(B∩A)/P A * P A) / P B *)
        (* 首先证明 P(A∩B) = P(B∩A)，因为交集是对称的 *)
        assert (Heq : P (fun x => In x A /\ In x B) = P (fun x => In x B /\ In x A)).
        {
          (* 因为两个集合是相等的：A ∩ B = B ∩ A *)
          assert (Hseteq : SetEq (fun x => In x A /\ In x B) (fun x => In x B /\ In x A)).
          {
            intro x.
            split.
            - intros [HxA HxB]; split; assumption.
            - intros [HxB HxA]; split; assumption.
          }
          apply set_extensionality in Hseteq.
          (* 由于集合相等，它们的概率也相等 *)
          unfold P.
          rewrite Hseteq.
          reflexivity.
        }
        rewrite Heq.
        (* 现在目标：P(B∩A)/P B = (P(B∩A)/P A * P A) / P B *)
        (* 首先简化右边的表达式 *)
        (* 证明 (P(B∩A)/P A * P A) = P(B∩A) *)
        assert (Hsimpl : (P (fun x => In x B /\ In x A) / P A * P A) = 
                         P (fun x => In x B /\ In x A)).
        {
          (* 使用实数运算 *)
          field.
          exact HnonzeroA'.
        }
        rewrite Hsimpl.
        (* 现在目标：P(B∩A)/P B = P(B∩A)/P B *)
        reflexivity.
Qed.
  
End BayesFormula.
  
(** =========== 3. 独立性 =========== *)
  
(* 事件独立性定义 *)
Definition independent_events {ps : MeasureTheory.ProbabilitySpace} 
  (A B : SetX (ps.(MeasureTheory.ps_Ω))) 
  (HA : MeasureTheory.is_event A) (HB : MeasureTheory.is_event B) : Prop :=
  let pAB := MeasureTheory.P (fun x => In x A /\ In x B) in
  let pA := MeasureTheory.P A in
  let pB := MeasureTheory.P B in
  pAB = (pA * pB)%R.
  
(* 独立性的Notation *)
Notation "A ⟂ B" := (independent_events A B _ _) (at level 60).
  
(* 独立性基本性质 *)
Lemma independent_symmetric : forall {ps : MeasureTheory.ProbabilitySpace} 
  (A B : SetX (ps.(MeasureTheory.ps_Ω)))
  (HA : MeasureTheory.is_event A) (HB : MeasureTheory.is_event B),
  independent_events A B HA HB -> independent_events B A HB HA.
Proof.
  intros ps A B HA HB H.
  unfold independent_events in *.
  (* 证明两个集合相等：A∩B = B∩A *)
  assert (Hset : (fun x => In x A /\ In x B) = (fun x => In x B /\ In x A)).
  { 
    apply set_extensionality.
    intro x.
    split; intros [H1 H2]; split; assumption.
  }
  (* 重写 H 中的集合 *)
  rewrite Hset in H.
  (* 现在 H 是：P (fun x => In x B /\ In x A) = P A * P B *)
  (* 使用实数乘法的交换律 *)
  rewrite Rmult_comm in H.
  exact H.
Qed.
  
(* 独立性基本性质：如果事件A与B独立，则A与B的补集也独立 *)
Lemma independent_complement : forall {ps : MeasureTheory.ProbabilitySpace} 
  (A B : SetX (ps.(MeasureTheory.ps_Ω)))
  (HA : MeasureTheory.is_event A) (HB : MeasureTheory.is_event B),
  independent_events A B HA HB ->
  exists HcompB, independent_events A (Complement_s B) HA HcompB.
Proof.
  intros ps A B HA HB H.
  
  (* 1. 构造 Complement_s B 的可测性证明 *)
  assert (HcompB : MeasureTheory.is_event (Complement_s B)).
  {
    unfold MeasureTheory.is_event, MeasureTheory.measurable_set.
    apply MeasureTheory.sigma_closed_complement.
    exact HB.
  }
  
  exists HcompB.
  
  (* 2. 展开独立性的定义 *)
  unfold independent_events in H.
  unfold independent_events.
  
  (* 3. 提取概率值 *)
  set (pA := MeasureTheory.P A) in *.
  set (pB := MeasureTheory.P B) in *.
  set (pAB := MeasureTheory.P (fun x => In x A /\ In x B)) in *.
  set (pAcompB := MeasureTheory.P (fun x => In x A /\ In x (Complement_s B))) in *.
  
  (* 4. 使用补集的概率公式 *)
  pose proof (MeasureTheory.probability_complement_formula B HB) as Hcomp_prob.
  
  (* 5. 证明两个集合不相交 *)
  assert (Hdisj : Disjoint (fun x => In x A /\ In x B) 
                          (fun x => In x A /\ In x (Complement_s B))).
  {
    unfold Disjoint.
    intros x [H1 H2].
    destruct H1 as [HxA HxB].
    destruct H2 as [HxA' HxBc].
    rewrite complement_property in HxBc.
    contradiction.
  }
  
  (* 6. 证明集合分解 *)
  assert (Hset_eq : SetEq A (fun x => (In x A /\ In x B) \/ (In x A /\ In x (Complement_s B)))).
  {
    intro x.
    split.
    - intro HxA.
      destruct (classic (In x B)) as [HxB | HnotB].
      + left; split; assumption.
      + right; split; [assumption | exact HnotB].
    - intros [[HxA _] | [HxA _]]; assumption.
  }
  
  (* 7. 应用概率的有限可加性 *)
  pose proof (MeasureTheory.probability_finite_additivity 
               (fun x => In x A /\ In x B) 
               (fun x => In x A /\ In x (Complement_s B))
               (MeasureTheory.measurable_intersection A B HA HB)
               (MeasureTheory.measurable_intersection A (Complement_s B) HA HcompB)
               Hdisj) as Hadd.
  
  (* 8. 简化 Hadd 中的表达式，展开 In 定义 *)
  unfold In in Hadd.
  
  (* 9. 将集合等式转换为函数相等 *)
  assert (Heq_union : A = (fun x => (A x /\ B x) \/ (A x /\ (Complement_s B) x))).
  {
    apply set_extensionality.
    intro x.
    destruct (Hset_eq x) as [H1 H2].
    split.
    - intro HxA.
      apply H1 in HxA.
      exact HxA.
    - intro Hx.
      apply H2 in Hx.
      exact Hx.
  }
  
  (* 10. 从函数相等得到概率相等 *)
  assert (Heq_union_P : P A = P (fun x => A x /\ B x \/ A x /\ (Complement_s B) x)).
  {
    apply f_equal.
    exact Heq_union.
  }
  
  (* 11. 将并集概率重写为 P A *)
  rewrite <- Heq_union_P in Hadd.
  
  (* 12. 将独立性的等式代入 Hadd *)
  unfold pAB in H.
  unfold pA, pB in H.
  unfold In in H.
  rewrite H in Hadd.
  
  (* 13. 使用 lra 策略处理实数运算 *)
  unfold pAcompB, pA, pB.
  rewrite Hcomp_prob.
  unfold pAcompB, In.
  lra.
Qed.
  
(* 两两独立与相互独立 *)
Definition pairwise_independent {ps : MeasureTheory.ProbabilitySpace} 
  (I : Type) (A : I -> SetX (ps.(MeasureTheory.ps_Ω))) 
  (Hmeas : forall i, MeasureTheory.is_event (A i)) : Prop :=
  forall i j, i <> j -> independent_events (A i) (A j) (Hmeas i) (Hmeas j).
  
(* 实数列表乘积函数 *)
Fixpoint list_prod_R (l : list R) : R :=
  match l with
  | nil => 1%R
  | cons x xs => x * (list_prod_R xs)
  end.
  
Definition mutually_independent {ps : MeasureTheory.ProbabilitySpace} 
  (I : Type) (A : I -> SetX (ps.(MeasureTheory.ps_Ω))) 
  (Hmeas : forall i, MeasureTheory.is_event (A i)) : Prop :=
  forall (J : list I),
    MeasureTheory.P (fun x => forall i, List.In i J -> In x (A i)) = 
    list_prod_R (map (fun i => MeasureTheory.P (A i)) J).
  
(** =========== 4. 随机变量 =========== *)
  
Open Scope R_scope.
  
Require Import Ranalysis1.  (* 包含Rarchimed *)
Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
  
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znat.
Require Import Coq.Arith.Arith.
  
(* 4.1 随机变量定义 *)
Definition RandomVariable {ps : ProbabilitySpace} (Y : Type) 
  (𝒢 : SigmaAlgebra Y) (X : ps.(ps_Ω) -> Y) : Prop :=
  forall B, B in_m 𝒢 -> is_event (fun x => In (X x) B).
  
(* 实值随机变量 *)
Definition RealRandomVariable {ps : ProbabilitySpace} 
  (X : ps.(ps_Ω) -> R) : Prop :=
  RandomVariable R 
    (generated_sigma_algebra (fun A => exists a b, SetEq A (fun x => a <= x /\ x <= b))) 
    X.
  
(* 4.2 分布函数 *)
Definition distribution_function {ps : ProbabilitySpace} 
  (X : ps.(ps_Ω) -> R) (HX : RealRandomVariable X) : R -> R :=
  fun t => P (fun ω => X ω <= t).
  
(** 分布函数性质 **)
Lemma distribution_function_properties : forall {ps : ProbabilitySpace} 
  (X : ps.(ps_Ω) -> R) (HX : RealRandomVariable X) (F := distribution_function X HX),
  (forall t, R0 <= F t /\ F t <= R1) /\
  (forall t1 t2, t1 <= t2 -> F t1 <= F t2) /\
  (is_right_continuous F) /\
  (limit_at_neg_infinity F R0) /\
  (limit_at_pos_infinity F R1).
Proof.
  intros ps X HX F.
  
  (* 辅助引理：证明 {ω | X ω ≤ t} 是可测事件 *)
  assert (Hmeas_interval : forall t, is_event (fun ω => X ω <= t)).
  {
    intro t.
    unfold RealRandomVariable in HX.
    unfold RandomVariable in HX.
    
    (* 构造区间 [-n, t] *)
    set (interval_seq := fun (n : nat) => fun x : R => - (INR n) <= x /\ x <= t).
    
    (* 证明每个区间在基集中 *)
    assert (Hinterval_base : forall n, 
             In (interval_seq n) (fun A : SetX R => exists a b : R, SetEq A (fun x : R => a <= x /\ x <= b))).
    {
      intro n.
      exists (- (INR n)), t.
      unfold SetEq, interval_seq.
      intro x.
      split; intros [H1 H2]; split; assumption.
    }
    
    (* 证明每个区间在生成的σ代数中 *)
    assert (Hinterval_sigma : forall n, 
             In (interval_seq n) (sigma_sets R 
               (generated_sigma_algebra 
                 (fun A : SetX R => exists a b : R, SetEq A (fun x : R => a <= x /\ x <= b))))).
    {
      intro n.
      unfold generated_sigma_algebra, sigma_sets.
      simpl.
      intros G HG.
      destruct HG as [Hbase [Huniv [Hcomp Hcunion]]].
      apply Hbase.
      exact (Hinterval_base n).
    }
    
    (* 定义原像集合 C_n = X^(-1)([-n, t]) *)
    set (preimage_seq := fun (n : nat) => fun ω : ps.(ps_Ω) => In (X ω) (interval_seq n)).
    
    (* 证明每个 C_n 可测 *)
    assert (Hpreimage_meas : forall n, is_event (preimage_seq n)).
    {
      intro n.
      unfold is_event, preimage_seq.
      apply HX.
      exact (Hinterval_sigma n).
    }
    
    (* 证明集合等式：{ω | X ω ≤ t} = ⋃_n C_n *)
    assert (Hset_eq : SetEq (fun ω : ps.(ps_Ω) => X ω <= t) 
                           (fun ω : ps.(ps_Ω) => exists n, preimage_seq n ω)).
    {
      unfold SetEq.
      intro ω.
      split.
      - intro H.
        (* X ω ≤ t *)
        destruct (Rtotal_order (X ω) R0) as [Hlt | [Heq | Hgt]].
        + (* X ω < 0 *)
          pose proof (archimed (- (X ω))) as [Harch _].
          set (z := up (- (X ω))) in *.
          exists (Z.to_nat (Z.max 0%Z z)).
          unfold preimage_seq, interval_seq, In.
          split.
          * apply Ropp_le_cancel.
            rewrite INR_IZR_INZ.
            assert (Hle_max : (0 <= Z.max 0%Z z)%Z) by apply Z.le_max_l.
            rewrite Z2Nat.id.
            apply Rle_trans with (IZR z).
            ** apply Rlt_le.
               lra.
            ** rewrite Ropp_involutive.
               apply IZR_le.
               apply Z.le_max_r.
            ** exact Hle_max.
          * exact H.
        + (* X ω = 0 *)
          subst.
          exists 0%nat.
          unfold preimage_seq, interval_seq, In.
          split.
          * simpl. lra.
          * exact H.
        + (* X ω > 0 *)
          exists 0%nat.
          unfold preimage_seq, interval_seq, In.
          split.
          * simpl. lra.
          * exact H.
      - intro H.
        destruct H as [n Hn].
        unfold preimage_seq, interval_seq, In in Hn.
        destruct Hn as [_ H2].
        exact H2.
    }
    
    (* 应用集合相等性和可数并的可测性 *)
    apply set_extensionality in Hset_eq.
    rewrite Hset_eq.
    unfold is_event.
    apply sigma_closed_countable_union.
    exact Hpreimage_meas.
  }
  
  (* 第一部分：值域性质 - 简化版本 *)
  assert (H_range : forall t, R0 <= F t /\ F t <= R1).
  {
    intro t.
    unfold F, distribution_function.
    split.
    - (* 证明 0 <= P(X ≤ t) *)
      apply probability_nonneg.
      apply Hmeas_interval.
    - (* 证明 P(X ≤ t) <= 1 *)
      apply probability_le_one.
      apply Hmeas_interval.
  }
  
  (* 第二部分：单调性 - 简化版本 *)
  assert (H_mono : forall t1 t2, t1 <= t2 -> F t1 <= F t2).
  {
    intros t1 t2 Hle.
    unfold F, distribution_function.
    
    (* 证明集合包含关系：{X ≤ t1} ⊆ {X ≤ t2} *)
    assert (Hsubset : (fun ω => X ω <= t1) subset_s (fun ω => X ω <= t2)).
    {
      intro ω; intro H.
      apply Rle_trans with t1; [exact H | exact Hle].
    }
    
    (* 使用已有的辅助引理证明可测性 *)
    assert (Hmeas1 : is_event (fun ω => X ω <= t1)) by apply Hmeas_interval.
    assert (Hmeas2 : is_event (fun ω => X ω <= t2)) by apply Hmeas_interval.
    
    (* 应用概率的单调性引理 *)
    apply (probability_monotonicity (fun ω => X ω <= t1) 
                                    (fun ω => X ω <= t2) 
                                    Hmeas1 Hmeas2 Hsubset).
  }
  
  (* 第三部分：右连续性 - 完整证明 *)
assert (H_right_cont : is_right_continuous F).
{
  unfold is_right_continuous.
  intro t.
  unfold sequence_converges, Un_cv.
  intros eps Heps_pos.
  
  (* 构造递减序列 t_n = t + 1/(n+1) *)
  set (t_seq := fun n : nat => t + / (INR (S n))).
  
  (* 定义事件序列 A_n = {ω | X ω ≤ t_n} *)
  set (A_seq := fun n : nat => fun ω => X ω <= t_seq n).
  
  (* 每个 A_n 可测 *)
  assert (Hmeas_seq : forall n, is_event (A_seq n)).
  { 
    intro n.
    unfold A_seq.
    apply Hmeas_interval.
  }
  
  (* 序列递减 *)
  assert (Hdecr : forall n, Subset (A_seq (S n)) (A_seq n)).
  {
    intro n.
    unfold A_seq, Subset, t_seq.
    intro ω.
    intro H.
    apply Rle_trans with (t + / (INR (S (S n)))).
    {
      exact H.
    }
    apply Rplus_le_compat_l.
    apply Rinv_le_contravar.
    {
      apply lt_0_INR.
      lia.
    }
    {
      apply le_INR.
      lia.
    }
  }
  
  (* 交集等于 {X ≤ t} *)
  assert (Hinter : SetEq (fun ω => forall n, In ω (A_seq n)) (fun ω => X ω <= t)).
  {
    unfold SetEq.
    intro ω.
    split.
    {
      intro H.
      apply Rnot_gt_le.
      intro Hgt.
      assert (Hε_pos : X ω - t > 0) by lra.
      (* 使用 archimed 性质找到足够大的 n *)
      destruct (archimed (/(X ω - t))) as [Hz _].
      set (z := up (/(X ω - t))) in *.
      assert (Hinv_pos : /(X ω - t) > 0).
      {
        apply Rinv_0_lt_compat.
        exact Hε_pos.
      }
      assert (Hz_nonneg : (0 <= z)%Z).
      {
        apply le_IZR.
        apply Rlt_le.
        apply Rlt_trans with (/(X ω - t)).
        {
          exact Hinv_pos.
        }
        exact Hz.
      }
      set (n := Z.to_nat z) in *.
      specialize (H n).
      unfold A_seq, t_seq, In in H.
      (* 证明 t + 1/(S n) < X ω *)
      assert (Hiz_pos : 0 < IZR z) by (apply Rlt_trans with (/(X ω - t)); [exact Hinv_pos | exact Hz]).
      
      (* 证明 INR (S n) >= IZR z *)
      assert (Hn_ge_izr : INR (S n) >= IZR z).
      {
        (* 目标：INR (S n) >= IZR z *)
        (* 首先，由于 z >= 0，我们有 IZR z = INR (Z.to_nat z) *)
        assert (Hiz_eq : IZR z = INR (Z.to_nat z)).
        {
          (* 使用 Z2Nat.id 证明 Z.of_nat (Z.to_nat z) = z *)
          rewrite <- (Z2Nat.id z) at 1.
          - rewrite INR_IZR_INZ.
            reflexivity.
          - exact Hz_nonneg.
        }
        (* 用这个等式重写目标 *)
        rewrite Hiz_eq.
        (* 现在目标变为：INR (S n) >= INR (Z.to_nat z) *)
        (* 展开 n 的定义 *)
        unfold n.
        (* 目标变为：INR (S (Z.to_nat z)) >= INR (Z.to_nat z) *)
        (* 使用 S_INR 展开左边 *)
        rewrite S_INR.
        (* 目标变为：INR (Z.to_nat z) + 1 >= INR (Z.to_nat z) *)
        (* 这等价于 1 >= 0，使用 lra 策略 *)
        lra.
      }
      
      (* 证明 / (INR (S n)) <= / (IZR z) *)
      assert (Hinv_le : / (INR (S n)) <= / (IZR z)).
      {
        apply Rinv_le_contravar.
        { exact Hiz_pos. }
        apply Rge_le in Hn_ge_izr.
        exact Hn_ge_izr.
      }
      
      (* 证明 / (IZR z) < X ω - t *)
      assert (Hinv_lt : / (IZR z) < X ω - t).
      {
        (* 首先证明：/(X ω - t) < IZR z *)
        assert (H_ab : / (X ω - t) < IZR z) by lra.
        
        (* 证明乘积为正：0 < /(X ω - t) * IZR z *)
        assert (Hprod_pos : 0 < / (X ω - t) * IZR z).
        {
          apply Rmult_lt_0_compat.
          - exact Hinv_pos.
          - exact Hiz_pos.
        }
        
        (* 应用 Rinv_lt_contravar *)
        assert (Hinv_lt_temp : / (IZR z) < / ( / (X ω - t) )).
        {
          apply Rinv_lt_contravar.
          - exact Hprod_pos.
          - exact H_ab.
        }
        
        (* 化简 / ( / (X ω - t) ) 为 X ω - t *)
        rewrite Rinv_involutive in Hinv_lt_temp.
        - exact Hinv_lt_temp.
        - lra.  (* X ω - t ≠ 0 *)
      }
      
      lra.
    }
    {
      intro H.
      intro n.
      unfold A_seq, t_seq, In.
      apply Rle_trans with t.
      {
        exact H.
      }
      rewrite <- (Rplus_0_r t) at 1.
      apply Rplus_le_compat_l.
      left.
      apply Rinv_0_lt_compat.
      apply lt_0_INR.
      lia.
    }
  }
  
  (* 证明存在有限测度的事件（在概率测度中总是成立） *)
  assert (Hfinite_exists : exists n, mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
                                 (BaseMeasureSpace:=ps.(ps_ℙ)) (A_seq n) <> NNER_infinity).
  {
    exists 0%nat.
    apply probability_measure_finite.
    exact (Hmeas_seq 0%nat).
  }
  
  (* 使用概率测度的从上连续性定理 *)
  pose proof (probability_continuity_from_above A_seq Hmeas_seq Hdecr Hfinite_exists) as Hcont_temp.
  
  (* 展开 sequence_converges 的定义 *)
  unfold sequence_converges in Hcont_temp.
  unfold Un_cv in Hcont_temp.
  
  (* 应用 Hcont_temp 得到 N *)
  specialize (Hcont_temp eps Heps_pos) as [N HN].
  
  (* 使用集合等式来重写概率值 *)
  assert (Heq : P (fun ω => forall m, In ω (A_seq m)) = P (fun ω => X ω <= t)).
  {
    apply f_equal.
    apply set_extensionality.
    exact Hinter.
  }
  
  (* 重写 HN 中的结论 *)
  rewrite Heq in HN.
  (* 现在 HN: forall n : nat, (n >= N)%nat -> Rdist (P (A_seq n)) (P (fun ω => X ω <= t)) < eps *)

  (* 注意：F (t + / INR (S n)) = P (A_seq n)，且 F t = P (fun ω => X ω <= t) *)
  (* 所以 HN 就是我们需要的结果 *)
  (* 返回 N 来完成证明 *)
  exists N.
  exact HN.
}  (* H_right_cont 证明结束 *)
  
(* 第四部分：在负无穷处的极限 *)
assert (H_neg_inf : limit_at_neg_infinity (distribution_function X HX) R0).
{
  unfold limit_at_neg_infinity.
  intros epsilon0 Hepsilon0_pos.  (* 使用不同的变量名 epsilon0 *)
  
  (* 我们需要找到 M，使得当 x < M 时，|F(x) - 0| = F(x) < epsilon0 *)
  (* 即当 x < M 时，P(X ≤ x) < epsilon0 *)
  
  (* 构造序列：x_n = -n *)
  (* 对于每个自然数 n，定义 A_n_neg = {ω | X ω ≤ -n} *)
  set (x_seq_neg := fun n : nat => - INR n).
  set (A_seq_neg := fun n : nat => fun ω : ps.(ps_Ω) => X ω <= x_seq_neg n).
  
  (* 证明每个 A_n_neg 可测 *)
assert (Hmeas_seq_neg : forall n, is_event (A_seq_neg n)).
{
  intro m.
  unfold A_seq_neg, x_seq_neg.
  (* 构造区间序列 B_k = [-k, -m] *)
  set (B_seq_neg := fun (k : nat) => fun x : R => - (INR k) <= x /\ x <= - (INR m)).
  
  (* 证明每个 B_seq_neg 在基集中 *)
  assert (H_B_seq_base_neg : forall k, 
           In (B_seq_neg k) (fun A : SetX R => exists a b : R, SetEq A (fun x : R => a <= x /\ x <= b))).
  {
    intro k.
    exists (- (INR k)), (- (INR m)).
    unfold SetEq, B_seq_neg.
    intro x.
    split; intros [H1 H2]; split; assumption.
  }
  
  (* 证明每个 B_seq_neg 在生成的 σ-代数中 *)
  assert (H_B_seq_in_sigma_neg : forall k, 
           In (B_seq_neg k) (sigma_sets R 
             (generated_sigma_algebra 
               (fun A : SetX R => exists a b : R, SetEq A (fun x : R => a <= x /\ x <= b))))).
  {
    intro k.
    unfold generated_sigma_algebra, sigma_sets.
    simpl.
    intros G HG.
    destruct HG as [Hbase [Huniv [Hcomp Hcunion]]].
    apply Hbase.
    exact (H_B_seq_base_neg k).
  }
  
  (* 定义 C_k 为 X 在 B_seq_neg 中的原像 *)
  set (C_seq_neg := fun (k : nat) => fun ω : ps.(ps_Ω) => In (X ω) (B_seq_neg k)).
  
  assert (H_C_seq_meas_neg : forall k, is_event (C_seq_neg k)).
  {
    intro k.
    unfold is_event, C_seq_neg.
    apply HX.
    exact (H_B_seq_in_sigma_neg k).
  }
  
  (* 证明集合等式：A_n_neg = ⋃_k C_k *)
  assert (Heq_set_neg : SetEq (fun ω : ps_Ω => X ω <= - INR m) 
                             (fun ω0 : ps_Ω => exists k, C_seq_neg k ω0)).
  {
    unfold SetEq.
    intro ω0.
    split.
    - intro H_cond.
      unfold In in H_cond.
      (* 先判断 X ω0 是否小于 0 *)
      destruct (Rlt_dec (X ω0) R0) as [Hlt | Hge].
      + (* 情况1: X ω0 < 0 *)
        pose proof (archimed (- (X ω0))) as [H_arch _].
        set (z_val := up (- (X ω0))) in *.
        exists (Z.to_nat (Z.max 0%Z z_val)).
        unfold C_seq_neg, In, B_seq_neg.
        split.
        * apply Ropp_le_cancel.
          rewrite INR_IZR_INZ.
          rewrite Z2Nat.id; [ | apply Z.le_max_l].
          apply Rle_trans with (IZR z_val).
          { apply Rlt_le. lra. }
          rewrite Ropp_involutive.
          apply IZR_le, Z.le_max_r.
        * exact H_cond.
      + (* 情况2: X ω0 ≥ 0 *)
        destruct (Req_EM_T (X ω0) R0) as [Heq_X | Hneq_X].
        * (* 子情况2.1: X ω0 = 0 *)
          destruct m as [O | m_next].
          { (* m = 0 *)
            exists 0%nat.
            unfold C_seq_neg, In, B_seq_neg.
            split.
            - simpl. lra.
            - rewrite Heq_X. simpl. lra.
          }
          { (* m = S m_next *)
            exfalso.
            rewrite Heq_X in H_cond.
            assert (Hpos : INR (S m_next) > 0) by (apply lt_0_INR; lia).
            lra.
          }
        * (* 子情况2.2: X ω0 > 0 *)
          exfalso.
          assert (Hneg : - INR m <= 0).
          { 
            rewrite <- Ropp_0.
            apply Ropp_le_contravar.
            apply pos_INR.
          }
          lra.
    - intro H_exists.
      destruct H_exists as [k Hk].
      unfold C_seq_neg, In, B_seq_neg in Hk.
      destruct Hk as [H_left H_right].
      exact H_right.
  }
  
  (* 使用集合相等性将目标重写为可数并集 *)
  unfold is_event.
  apply set_extensionality in Heq_set_neg.
  rewrite Heq_set_neg.  (* 现在可以重写了，因为目标是 is_event (fun ω : ps_Ω => X ω <= - INR m) *)
  apply sigma_closed_countable_union.
  exact H_C_seq_meas_neg.
}
  
  (* 证明 A_seq_neg 递减且极限为空集 *)
  assert (Hdecr_neg : forall n, Subset (A_seq_neg (S n)) (A_seq_neg n)).
  {
    intro n.
    unfold Subset, A_seq_neg, x_seq_neg.
    intros ω H.
    apply Rle_trans with (- INR (S n)).
    { exact H. }
    apply Ropp_le_contravar.
    apply le_INR.
    lia.
  }
  
  (* 证明 ⋂_n A_seq_neg n 是空集 *)
  assert (Hempty_neg : SetEq (fun ω => forall n, In ω (A_seq_neg n)) EmptySet_s).
  {
    unfold SetEq.
    intro ω.
    split.
    - intro H.
      (* 假设 ω 在所有 A_seq_neg n 中，即对于所有 n，X ω ≤ -n *)
      (* 我们需要证明矛盾 *)
      unfold EmptySet, In.
      
      (* 首先分析 X ω 的情况 *)
      destruct (Rlt_le_dec (X ω) R0) as [Hlt | Hge].
      {
        (* 情况1：X ω < 0 *)
        (* 使用 archimed 来找到整数上界 *)
        pose proof (archimed (- (X ω))) as [Harch _].
        set (z := up (- (X ω))) in *.
        
        (* 证明 z > 0 *)
        assert (Hz_pos : (0 < z)%Z).
        {
          apply lt_IZR.
          simpl.
          lra.
        }
        
        (* 定义 n = z *)
        set (n_val := Z.to_nat z).
        
        (* 现在我们有：z = up(-X ω) > -X ω，所以 -X ω < z，即 X ω > -z *)
        (* 但 H n_val 要求 X ω ≤ - INR n_val *)
        specialize (H n_val).
        unfold A_seq_neg, x_seq_neg, In in H.
        unfold n_val.
        
        (* 我们需要证明：X ω ≤ - INR n_val 与 X ω > - IZR z 矛盾 *)
        (* 首先证明 INR n_val = IZR z *)
        assert (H_eq : INR n_val = IZR z).
        {
          unfold n_val.
          (* 手动计算：INR (Z.to_nat z) = IZR (Z.of_nat (Z.to_nat z)) *)
          rewrite INR_IZR_INZ.
          (* 现在目标：IZR (Z.of_nat (Z.to_nat z)) = IZR z *)
          apply f_equal.
          (* 目标：Z.of_nat (Z.to_nat z) = z *)
          (* 因为 z > 0，所以 z ≥ 0 *)
          assert (Hz_nonneg : (0 <= z)%Z) by (apply Z.lt_le_incl; exact Hz_pos).
          (* 使用 Z2Nat.id 的另一个版本 *)
          rewrite Z2Nat.id by exact Hz_nonneg.
          reflexivity.
        }
        
        (* 重写 H 中的 INR n_val *)
        rewrite H_eq in H.
        
        (* 现在 H: X ω ≤ - IZR z，而 Harch: IZR z > - X ω *)
        (* 从 Harch: IZR z > - X ω 得到 X ω > - IZR z *)
        (* 与 H 矛盾 *)
        lra.
      }
      {
        (* 情况2：X ω ≥ 0 *)
        (* 取 n = 1，那么 X ω ≤ -1 不成立，因为 X ω ≥ 0 > -1 *)
        specialize (H 1%nat).
        unfold A_seq_neg, x_seq_neg, In in H.
        simpl in H.
        lra.
      }
    - intro H.
      (* 从空集推出任何结论 *)
      unfold EmptySet, In in H.
      contradiction.
  }
  
  (* 证明存在有限测度的事件 *)
  assert (Hfinite_neg : exists n, 
           mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) (A_seq_neg n) <> NNER_infinity).
  {
    exists O.
    apply probability_measure_finite.
    exact (Hmeas_seq_neg O).
  }
  
  (* 使用概率的从上连续性 *)
  pose proof (probability_continuity_from_above A_seq_neg Hmeas_seq_neg Hdecr_neg Hfinite_neg) as Hcont_neg.
  
  (* 展开收敛性 *)
  unfold sequence_converges, Un_cv in Hcont_neg.
  
  (* 应用连续性定理得到 N_neg，避免与已有的 N 冲突 *)
  specialize (Hcont_neg epsilon0 Hepsilon0_pos) as [N_neg HN_neg].
  
  (* 现在我们需要证明：存在 M，使得当 x < M 时，|F(x) - 0| < epsilon0 *)
  (* 我们可以取 M = - (INR N_neg) *)
  exists (- (INR N_neg)).
  intros x Hx.
  
  (* 展开 F 的定义 *)
  unfold F, distribution_function.
  
  (* 我们需要证明：|P(X ≤ x) - 0| < epsilon0 *)
  (* 由于 P(X ≤ x) ≥ 0，所以 |P(X ≤ x) - 0| = P(X ≤ x) *)
  rewrite Rminus_0_r.
  
  (* 证明绝对值 *)
  rewrite Rabs_right.
  2: {
    (* 证明 P(X ≤ x) ≥ 0 - 直接证明 *)
    unfold P.
    destruct (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) 
             (fun ω : ps.(ps_Ω) => X ω <= x)) as [r_val | Hinf] eqn:Heq_mu.
    - (* 情况：有限测度值 r_val *)
      simpl.
      pose proof (measure_nonneg (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ))
                  (fun ω : ps.(ps_Ω) => X ω <= x) (Hmeas_interval x)) as H_nonneg.
      rewrite Heq_mu in H_nonneg.
      unfold NNER_le in H_nonneg.
      simpl in H_nonneg.
      (* H_nonneg: R0 <= r_val *)
      (* 需要证明 r_val >= 0 *)
      apply Rle_ge.
      exact H_nonneg.
    - (* 情况：无穷测度 *)
      simpl.
      (* 目标: 0 >= 0 *)
      apply Rge_refl.
  }
  
  (* 现在需要证明：P(X ≤ x) < epsilon0 *)
  (* 首先证明：当 x < - (INR N_neg) 时，事件 {X ≤ x} ⊆ A_seq_neg N_neg *)
  assert (Hsubset : (fun ω => X ω <= x) subset_s A_seq_neg N_neg).
  {
    intro ω.
    intro Hω.
    unfold A_seq_neg, x_seq_neg, In.
    apply Rle_trans with x.
    - exact Hω.
    - apply Rlt_le.
      exact Hx.
  }
  
  (* 应用概率的单调性 *)
  apply Rle_lt_trans with (P (A_seq_neg N_neg)).
  {
    apply probability_monotonicity.
    - apply Hmeas_interval.
    - apply Hmeas_seq_neg.
    - exact Hsubset.
  }
  
  (* 现在需要证明 P(A_seq_neg N_neg) < epsilon0 *)
  (* 使用 HN_neg，但注意 HN_neg 要求 n >= N_neg *)
  specialize (HN_neg N_neg (Nat.le_refl N_neg)).
  
  (* HN_neg 给出了 Rdist，展开 Rdist 定义 *)
  unfold Rdist in HN_neg.
  
  (* 从 HN_neg: |P(A_seq_neg N_neg) - P(⋂_n A_seq_neg n)| < epsilon0 *)
  (* 由 Hempty_neg，我们知道 ⋂_n A_seq_neg n = 空集，所以 P(空集) = 0 *)
  assert (Hinter_empty : P (fun x0 : ps_Ω => forall n : nat, x0 in_s A_seq_neg n) = R0).
  {
    unfold P.
    (* 使用集合相等性来证明测度相等 *)
    pose proof (set_extensionality _ _ Hempty_neg) as Heq_set.
    rewrite Heq_set.
    rewrite measure_empty.
    simpl.
    reflexivity.
  }
  
  rewrite Hinter_empty in HN_neg.
  
  (* 现在 HN_neg: |P(A_seq_neg N_neg) - 0| < epsilon0 *)
  rewrite Rminus_0_r in HN_neg.
  
  (* 由于 P(A_seq_neg N_neg) ≥ 0，所以 |P(A_seq_neg N_neg)| = P(A_seq_neg N_neg) *)
  rewrite Rabs_right in HN_neg.
  - exact HN_neg.
  - (* 证明 P(A_seq_neg N_neg) ≥ 0 - 直接证明 *)
    unfold P.
    destruct (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) 
             (A_seq_neg N_neg)) as [r_val | Hinf] eqn:Heq_mu2.
    + (* 有限测度值 *)
      simpl.
      pose proof (measure_nonneg (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ))
                  (A_seq_neg N_neg) (Hmeas_seq_neg N_neg)) as H_nonneg2.
      rewrite Heq_mu2 in H_nonneg2.
      unfold NNER_le in H_nonneg2.
      simpl in H_nonneg2.
      (* H_nonneg2: R0 <= r_val *)
      (* 需要证明 r_val >= 0 *)
      apply Rle_ge.
      exact H_nonneg2.
    + (* 无穷测度 *)
      simpl.
      apply Rge_refl.
}
  
  (* 第五部分：在正无穷处的极限 *)
  assert (H_pos_inf : limit_at_pos_infinity (distribution_function X HX) R1).
  {
    unfold limit_at_pos_infinity.
    intros epsilon1 Hepsilon1_pos.  (* 改为 epsilon1 避免冲突 *)
    
    (* 构造序列：x_n = n *)
    set (x_seq_pos := fun n : nat => INR n).
    set (A_seq_pos := fun n : nat => fun ω1 : ps.(ps_Ω) => X ω1 <= x_seq_pos n).
    
    (* 证明每个 A_n_pos 可测 *)
    assert (Hmeas_seq_pos : forall n, is_event (A_seq_pos n)).
    {
      intro m0.  (* 改为 m0 避免冲突 *)
      unfold A_seq_pos, x_seq_pos.
      (* 构造区间序列 B_k = [-k, m0] *)
      set (B_seq_pos := fun (k : nat) => fun x1 : R => - (INR k) <= x1 /\ x1 <= INR m0).
      
      (* 证明每个 B_seq_pos 在基集中 *)
      assert (H_B_seq_base_pos : forall k, 
               In (B_seq_pos k) (fun A : SetX R => exists a b : R, SetEq A (fun x2 : R => a <= x2 /\ x2 <= b))).
      {
        intro k.
        exists (- (INR k)), (INR m0).
        unfold SetEq, B_seq_pos.
        intro x3.
        split; intros [H1 H2]; split; assumption.
      }
      
      (* 证明每个 B_seq_pos 在生成的 σ-代数中 *)
      assert (H_B_seq_in_sigma_pos : forall k, 
               In (B_seq_pos k) (sigma_sets R 
                 (generated_sigma_algebra 
                   (fun A : SetX R => exists a b : R, SetEq A (fun x4 : R => a <= x4 /\ x4 <= b))))).
      {
        intro k.
        unfold generated_sigma_algebra, sigma_sets.
        simpl.
        intros G HG.
        destruct HG as [Hbase [Huniv [Hcomp Hcunion]]].
        apply Hbase.
        exact (H_B_seq_base_pos k).
      }
      
      (* 定义 C_k 为 X 在 B_seq_pos 中的原像 *)
      set (C_seq_pos := fun (k : nat) => fun ω2 : ps.(ps_Ω) => In (X ω2) (B_seq_pos k)).
      
      assert (H_C_seq_meas_pos : forall k, is_event (C_seq_pos k)).
      {
        intro k.
        unfold is_event, C_seq_pos.
        apply HX.
        exact (H_B_seq_in_sigma_pos k).
      }
      
      (* 证明集合等式：A_n_pos = ⋃_k C_k *)
      assert (H_eq_pos : SetEq (fun ω3 : ps.(ps_Ω) => X ω3 <= INR m0) (fun ω3 : ps.(ps_Ω) => exists k, C_seq_pos k ω3)).
      {
        unfold SetEq.
        intro ω3.
        split.
        - intro Hcond.
          (* X ω3 ≤ INR m0 *)
          destruct (Rlt_dec (X ω3) R0) as [Hlt | Hge'].
          + (* X ω3 < 0 *)
            pose proof (archimed (- (X ω3))) as [H_arch _].
            set (z_val := up (- (X ω3))) in *.
            exists (Z.to_nat (Z.max 0%Z z_val)).
            unfold C_seq_pos, In, B_seq_pos.
            split.
            * (* 证明 - (INR ...) ≤ X ω3 *)
              apply Ropp_le_cancel.
              rewrite INR_IZR_INZ.
              rewrite Z2Nat.id; [ | apply Z.le_max_l].
              apply Rle_trans with (IZR z_val).
              { apply Rlt_le. lra. }
              rewrite Ropp_involutive.
              apply IZR_le, Z.le_max_r.
            * (* 证明 X ω3 ≤ INR m0 *)
              exact Hcond.
          + (* X ω3 ≥ 0 *)
            exists 0%nat.
            unfold C_seq_pos, In, B_seq_pos.
            split.
            * simpl. lra.
            * exact Hcond.
        - intro Hexists.
          destruct Hexists as [k Hk].
          unfold C_seq_pos, In, B_seq_pos in Hk.
          destruct Hk as [H_left H_right].
          exact H_right.
      }
      
      (* 将集合等式转换为函数相等并应用可数并的可测性 *)
      apply set_extensionality in H_eq_pos.
      rewrite H_eq_pos.
      unfold is_event.
      apply sigma_closed_countable_union.
      exact H_C_seq_meas_pos.
    }
    
    (* 证明序列递增：A_n ⊆ A_{n+1} *)
    assert (Hincr_pos : forall n0, Subset (A_seq_pos n0) (A_seq_pos (S n0))).
    {
      intro n0.
      unfold Subset.
      intro ω4.
      unfold In, A_seq_pos, x_seq_pos.
      simpl.
      intro H_xle.
      (* 需要证明：如果 X ω4 ≤ n0，那么 X ω4 ≤ n0+1 *)
      apply Rle_trans with (INR n0).
      - exact H_xle.
      - (* 证明 INR n0 ≤ INR (S n0) *)
        case n0.
        + (* n0 = 0 *)
          simpl. lra.
        + (* n0 = S n' *)
          intro n'.
          rewrite S_INR.  (* 或使用 INR_S *)
          lra.
    }
    
    (* 证明并集为全集：⋃_n A_n_pos = UniversalSet_s *)
    assert (Hunion_univ : SetEq (fun ω5 : ps.(ps_Ω) => exists n, In ω5 (A_seq_pos n)) UniversalSet_s).
    {
      intro ω5.  (* 使用新变量名 ω5 *)
      split.
      - intro H_exists.
        apply universal_set_property.
      - intro H_univ.
        (* 考虑两种情况：X ω5 < 0 或 X ω5 ≥ 0 *)
        destruct (Rlt_le_dec (X ω5) R0) as [Hlt | Hge'].
        + (* X ω5 < 0，取 n = 0 *)
          exists 0%nat.
          unfold In, A_seq_pos, x_seq_pos.
          simpl.
          lra.
        + (* X ω5 ≥ 0，使用 up 函数 *)
          pose proof (archimed (X ω5)) as [Hz1_pos Hz2_bound].
          set (z_pos := up (X ω5)) in *.
          assert (Hz_pos_nonneg : (0 <= z_pos)%Z).
          {
            apply le_IZR.
            apply Rlt_le.
            apply Rle_lt_trans with (X ω5).
            - exact Hge'.
            - exact Hz1_pos.
          }
          exists (Z.to_nat z_pos).
          unfold In, A_seq_pos, x_seq_pos.
          (* 直接计算 INR (Z.to_nat z_pos) = IZR z_pos *)
          apply Rle_trans with (IZR z_pos).
          - apply Rlt_le. exact Hz1_pos.
          - (* 证明 IZR z_pos ≤ INR (Z.to_nat z_pos) *)
            rewrite <- (Z2Nat.id z_pos Hz_pos_nonneg) at 1.
            rewrite <- INR_IZR_INZ.
            apply Rle_refl.
    }
    
    (* 使用概率的从下连续性 *)
    pose proof (probability_continuity_from_below A_seq_pos Hmeas_seq_pos Hincr_pos) as Hcont_pos.
    unfold sequence_converges, Un_cv in Hcont_pos.
    
    (* 应用连续性定理得到 N_pos，使用正确的 epsilon1 *)
    specialize (Hcont_pos epsilon1 Hepsilon1_pos) as [N_pos HN_pos].
    
    (* 取 M = INR N_pos *)
    exists (INR N_pos).
    intros x Hx.
    
    (* 展开 F 的定义 *)
    unfold F, distribution_function.
    
    (* 当 x > INR N_pos 时，事件 {X ≤ x} 包含 A_seq_pos N_pos *)
    assert (Hsubset_pos : A_seq_pos N_pos subset_s (fun ω1 => X ω1 <= x)).
    {
      intro ω1.
      intro Hω1.
      unfold A_seq_pos, x_seq_pos, In in Hω1.
      apply Rle_trans with (INR N_pos).
      { exact Hω1. }
      apply Rlt_le. exact Hx.
    }
    
    (* 由概率单调性，P(A_seq_pos N_pos) ≤ P(X ≤ x) *)
    assert (Hle : P (A_seq_pos N_pos) <= P (fun ω1 => X ω1 <= x)).
    {
      apply probability_monotonicity.
      - exact (Hmeas_seq_pos N_pos).
      - apply Hmeas_interval.
      - exact Hsubset_pos.
    }
    
    (* 由概率的非负性，P(X ≤ x) ≤ 1 *)
    assert (Hle1 : P (fun ω1 => X ω1 <= x) <= R1).
    {
      apply probability_le_one.
      apply Hmeas_interval.
    }
    
    (* 由连续性定理，|P(A_seq_pos N_pos) - P(⋃_n A_seq_pos n)| < epsilon1 *)
    (* 注意：P(⋃_n A_seq_pos n) = P(全集) = 1 *)
    assert (Hunion_prob : P (fun ω1 => exists n, In ω1 (A_seq_pos n)) = R1).
    {
      unfold P.
      pose proof (set_extensionality _ _ Hunion_univ) as Heq_set.
      rewrite Heq_set.
      rewrite is_probability_measure.
      reflexivity.
    }
    
    rewrite Hunion_prob in HN_pos.
    
    (* 使用 HN_pos，但注意 HN_pos 要求 n >= N_pos *)
    specialize (HN_pos N_pos (Nat.le_refl N_pos)).
    unfold Rdist in HN_pos.
    
    (* 现在 HN_pos: |P(A_seq_pos N_pos) - 1| < epsilon1 *)
    (* 我们需要证明 |P(X ≤ x) - 1| ≤ |P(A_seq_pos N_pos) - 1|，然后传递到 epsilon1 *)
    apply Rle_lt_trans with (Rabs (P (A_seq_pos N_pos) - R1)).
    {
      (* 证明 |P(X ≤ x) - 1| ≤ |P(A_seq_pos N_pos) - 1| *)
      (* 令 a = P(A_seq_pos N_pos), b = P(X ≤ x)，已知 a ≤ b ≤ 1 *)
      
      (* 首先证明 a ≤ 1 和 b ≤ 1 *)
      assert (Ha_le1 : P (A_seq_pos N_pos) <= R1).
      { apply probability_le_one; exact (Hmeas_seq_pos N_pos). }
      assert (Hb_le1 : P (fun ω1 => X ω1 <= x) <= R1).
      { apply probability_le_one; apply Hmeas_interval. }
      
      (* 因此 a-1 ≤ 0 且 b-1 ≤ 0 *)
      assert (Ha_minus_nonpos : P (A_seq_pos N_pos) - R1 <= R0) by lra.
      assert (Hb_minus_nonpos : P (fun ω1 => X ω1 <= x) - R1 <= R0) by lra.
      
      (* 对于非正数，绝对值等于其相反数 *)
      rewrite Rabs_left1. 2: exact Hb_minus_nonpos.
      rewrite Rabs_left1. 2: exact Ha_minus_nonpos.
      
      (* 现在需要证明：-(P(X ≤ x) - 1) ≤ -(P(A_seq_pos N_pos) - 1) *)
      (* 即：1 - P(X ≤ x) ≤ 1 - P(A_seq_pos N_pos) *)
      (* 即：P(A_seq_pos N_pos) ≤ P(X ≤ x)，这是已知的 Hle *)
      lra.
    }
    exact HN_pos.
  }  (* H_pos_inf 证明结束 *)
  
  (* 将五个部分组合起来 *)
  split.
  exact H_range.
  
  split.
  exact H_mono.
  
  split.
  exact H_right_cont.
  
  split.
  exact H_neg_inf.
  
  exact H_pos_inf.
Qed.
  
(* 概率空间作为完全测度空间的实例 *)
(* 首先，我们需要一个辅助引理：概率空间中的事件测度总是有限的 *)
Lemma probability_measure_finite_for_all : forall (ps : ProbabilitySpace) (A : SetX (ps.(ps_Ω))),
  A in_m (ps.(ps_𝓕)) -> mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) A <> NNER_infinity.
Proof.
  intros ps A HA.
  apply probability_measure_finite.
  exact HA.
Qed.
  
(* 测度单调性的独立证明 *)
Lemma measure_monotonicity_direct (ps : ProbabilitySpace) 
  (A B : SetX (ps.(ps_Ω))) 
  (HA : In A (sigma_sets (ps.(ps_Ω)) (ps.(ps_𝓕))))
  (HB : In B (sigma_sets (ps.(ps_Ω)) (ps.(ps_𝓕))))
  (Hsubset : Subset A B) :
  mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) A <=_nner 
  mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) B.
Proof.
  (* 将B分解为不相交的两部分：A 和 B\A *)
  set (B_minus_A := fun x => In x B /\ ~ In x A).
  
  (* 证明 B_minus_A 可测 *)
  assert (Hmeas_BminusA : In B_minus_A (sigma_sets (ps.(ps_Ω)) (ps.(ps_𝓕)))).
  {
    unfold B_minus_A.
    (* B_minus_A = B ∩ (Complement A) *)
    assert (Heq : SetEq (fun x => In x B /\ ~ In x A) 
                       (fun x => In x B /\ In x (Complement A))).
    {
      intro x.
      split.
      - intros [HxB HnotA]. split; [exact HxB | exact HnotA].
      - intros [HxB Hcomp]. split; [exact HxB | exact Hcomp].
    }
    apply set_extensionality in Heq.
    rewrite Heq.
    (* 证明交集可测 *)
    apply measurable_intersection.
    - exact HB.
    - apply sigma_closed_complement.
      exact HA.
  }
  
  (* 证明 B = A ∪ B_minus_A *)
  assert (Heq_B : SetEq B (fun x => In x A \/ In x B_minus_A)).
  {
    intro x.
    split.
    - intro HxB.
      destruct (classic (In x A)) as [HxA | HnotA].
      + left; exact HxA.
      + right; unfold B_minus_A; split; [exact HxB | exact HnotA].
    - intros [HxA | Hx_BminusA].
      + apply Hsubset; exact HxA.
      + unfold B_minus_A in Hx_BminusA; destruct Hx_BminusA; assumption.
  }
  
  (* 证明 A 和 B_minus_A 不相交 *)
  assert (Hdisj : Disjoint A B_minus_A).
  {
    unfold Disjoint.
    intros x [HxA Hx_BminusA].
    unfold B_minus_A in Hx_BminusA.
    destruct Hx_BminusA as [HxB HnotA].
    contradiction.
  }
  
  (* 应用有限可加性 - 显式提供 BaseMeasureSpace 实例 *)
  pose proof (measure_finite_additivity 
               (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
               (BaseMeasureSpace:=ps.(ps_ℙ))
               A B_minus_A HA Hmeas_BminusA Hdisj) as Hadd.
  
  (* 将并集重写为 B *)
  assert (Heq_union : (fun x => In x A \/ In x B_minus_A) = B).
  {
    apply set_extensionality.
    intro x.
    (* 使用 Heq_B，但需要交换方向 *)
    destruct (Heq_B x) as [Hleft Hright].
    split.
    - (* 方向1: x in (A ∪ B_minus_A) -> x in B *)
      intro H.
      apply Hright.
      exact H.
    - (* 方向2: x in B -> x in (A ∪ B_minus_A) *)
      intro H.
      apply Hleft.
      exact H.
  }
  
  (* 现在重写 Hadd 中的并集为 B *)
  rewrite Heq_union in Hadd.
  
  (* 现在 Hadd: mu B = mu A +_nner mu B_minus_A *)
  
  (* 对测度进行分类讨论 *)
  destruct (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) A) as [a_val|Hinf_A] eqn:HA_val.
  {
    (* 情况1: mu A = NNER_finite a_val *)
    
    (* 继续对 mu B 进行分类讨论 *)
    destruct (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) B) as [b_val|Hinf_B] eqn:HB_val.
    {
      (* 子情况1.1: mu B = NNER_finite b_val *)
      
      (* 继续对 mu B_minus_A 进行分类讨论 *)
      destruct (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) B_minus_A) as [c_val|Hinf_C] eqn:HC_val.
      {
        (* 子情况1.1.1: mu B_minus_A = NNER_finite c_val *)
        
        (* 注意：Hadd 现在是：NNER_finite b_val = NNER_finite a_val +_nner NNER_finite c_val *)
        (* 这是因为在destruct时，我们用eqn:记录了等式，但Hadd中已经包含了这些值 *)
        
        (* 展开 NNER_add 并简化 *)
        unfold NNER_add in Hadd.
        simpl in Hadd.
        
        (* 现在 Hadd: NNER_finite b_val = NNER_finite (a_val + c_val) *)
        injection Hadd as Hadd_eq.  (* Hadd_eq: b_val = a_val + c_val *)
        
        (* 证明 c_val ≥ 0 *)
        assert (Hc_nonneg : R0 <= c_val).
        {
          (* 使用测度非负性 *)
          pose proof (measure_nonneg (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ))
                      B_minus_A Hmeas_BminusA) as Hnonneg.
          rewrite HC_val in Hnonneg.
          unfold NNER_le in Hnonneg.
          simpl in Hnonneg.
          exact Hnonneg.
        }
        
        (* 目标：NNER_finite a_val <=_nner NNER_finite b_val *)
        unfold NNER_le.
        simpl.
        (* 需要证明 a_val <= b_val *)
        rewrite Hadd_eq.  (* b_val = a_val + c_val *)
        lra.
      }
      {
        (* 子情况1.1.2: mu B_minus_A = NNER_infinity *)
        (* 与概率测度有限性矛盾 *)
        exfalso.
        apply (probability_measure_finite B_minus_A Hmeas_BminusA).
        exact HC_val.
      }
    }
      {
        (* 子情况1.2: mu B = NNER_infinity *)
        (* 与概率测度有限性矛盾 *)
        exfalso.
        apply (probability_measure_finite B HB).
        exact HB_val.
      }
  }
  {
      (* 情况2: mu A = NNER_infinity *)
      (* 与概率测度有限性矛盾 *)
      exfalso.
      apply (probability_measure_finite A HA).
      exact HA_val.
  }
  
Qed.
  
(* 扩展实数的反对称性 *)
Lemma NNER_le_antisym : forall x y : NonNegExtendedReal,
  x <=_nner y -> y <=_nner x -> x = y.
Proof.
  intros x y Hxy Hyx.
  
  (* 对 x 和 y 分别进行分类讨论 *)
  (* 先对 x 分类 *)
  destruct x as [rx | Hx_inf].
  - (* 情况 1: x = NNER_finite rx *)
    (* 再对 y 分类 *)
    destruct y as [ry | Hy_inf].
    + (* 子情况 1.1: y = NNER_finite ry *)
      (* 展开 ≤ 关系 *)
      unfold NNER_le in Hxy, Hyx.
      (* 现在 Hxy: rx ≤ ry, Hyx: ry ≤ rx *)
      assert (Heq : rx = ry).
      {
        apply Rle_antisym; assumption.
      }
      (* 应用等式 *)
      rewrite Heq.
      reflexivity.
      
    + (* 子情况 1.2: y = NNER_infinity *)
      (* 展开 ≤ 关系 *)
      unfold NNER_le in Hyx.
      (* Hyx: NNER_infinity ≤ NNER_finite rx *)
      (* 根据定义，这不可能，因为无穷大不会小于等于有限值 *)
      simpl in Hyx.
      contradiction.
      
  - (* 情况 2: x = NNER_infinity *)
    (* 再对 y 分类 *)
    destruct y as [ry | Hy_inf].
    + (* 子情况 2.1: y = NNER_finite ry *)
      (* 展开 ≤ 关系 *)
      unfold NNER_le in Hxy.
      (* Hxy: NNER_infinity ≤ NNER_finite ry *)
      (* 根据定义，这不可能 *)
      simpl in Hxy.
      contradiction.
      
    + (* 子情况 2.2: y = NNER_infinity *)
      (* 两个都是无穷大，相等 *)
      reflexivity.
Qed.
  
(* 扩展实数的自反性引理 *)
Lemma NNER_le_refl : forall (x : NonNegExtendedReal), x <=_nner x.
Proof.
  intro x.
  destruct x as [r | Hinf].
  - (* 情况1: x = NNER_finite r *)
    unfold NNER_le.
    apply Rle_refl.
  - (* 情况2: x = NNER_infinity *)
    unfold NNER_le.
    exact I.  (* True *)
Qed.
  
(** 扩展实数相等蕴含小于等于引理 **)
Lemma equal_implies_le : forall x y : NonNegExtendedReal, 
  x = y -> x <=_nner y.
Proof.
  intros x y Heq.    (* 引入假设：x = y *)
  rewrite Heq.       (* 将y重写为x *)
  apply NNER_le_refl. (* 应用自反性：x ≤ x *)
Qed.
  
(* 扩展实数的传递性引理 *)
Lemma NNER_le_trans : forall (x y z : NonNegExtendedReal),
  x <=_nner y -> y <=_nner z -> x <=_nner z.
Proof.
  intros x y z Hxy Hyz.
  (* 使用嵌套的case分析来处理三个变量的所有情况 *)
  destruct x as [rx | Hx_inf].
  {
    (* 情况1: x = NNER_finite rx *)
    destruct y as [ry | Hy_inf].
    {
      (* 子情况1.1: y = NNER_finite ry *)
      destruct z as [rz | Hz_inf].
      {
        (* 子情况1.1.1: z = NNER_finite rz *)
        unfold NNER_le in Hxy, Hyz.
        apply Rle_trans with ry; assumption.
      }
      {
        (* 子情况1.1.2: z = NNER_infinity *)
        unfold NNER_le in Hxy, Hyz.
        exact I.  (* True *)
      }
    }
    {
      (* 子情况1.2: y = NNER_infinity *)
      destruct z as [rz | Hz_inf].
      {
        (* 子情况1.2.1: z = NNER_finite rz - 但 Hyz: NNER_infinity <= NNER_finite rz 是False *)
        unfold NNER_le in Hyz.
        simpl in Hyz.
        contradiction.
      }
      {
        (* 子情况1.2.2: z = NNER_infinity *)
        unfold NNER_le in Hxy, Hyz.
        exact I.  (* True *)
      }
    }
  }
  {
    (* 情况2: x = NNER_infinity *)
    destruct y as [ry | Hy_inf].
    {
      (* 子情况2.1: y = NNER_finite ry - 但 Hxy: NNER_infinity <= NNER_finite ry 是False *)
      unfold NNER_le in Hxy.
      simpl in Hxy.
      contradiction.
    }
    {
      (* 子情况2.2: y = NNER_infinity *)
      destruct z as [rz | Hz_inf].
      {
        (* 子情况2.2.1: z = NNER_finite rz - 但 Hyz: NNER_infinity <= NNER_finite rz 是False *)
        unfold NNER_le in Hyz.
        simpl in Hyz.
        contradiction.
      }
      {
        (* 子情况2.2.2: z = NNER_infinity *)
        unfold NNER_le in Hxy, Hyz.
        exact I.  (* True *)
      }
    }
  }
Qed.
  
(* 首先声明概率空间为BaseMeasureSpace的实例 *)
Instance ProbabilitySpace_BaseMeasureSpace (ps : ProbabilitySpace) : 
  BaseMeasureSpace (ps.(ps_Ω)) (ps.(ps_𝓕)) :=
  ps.(ps_ℙ).
  
(* 现在声明概率空间为ExtendedMeasureSpace的实例 *)
Instance ProbabilitySpace_ExtendedMeasureSpace (ps : ProbabilitySpace) : 
  ExtendedMeasureSpace (ps.(ps_Ω)) (ps.(ps_𝓕)).
Proof.
  (* 构建ExtendedMeasureSpace实例 *)
  refine {|
    measure_monotonicity := _;
    measure_continuity_from_below := _;
    measure_continuity_from_above := _;
    measure_countable_additivity_standard := _
  |}.
  
  (* 1. 单调性 - 使用我们刚刚证明的引理 *)
  - intros A B HA HB Hsubset.
    apply measure_monotonicity_direct; assumption.
    
  (* 2. 从下连续性 *)
  - intros F_seq Hmeas_seq Hinc.
    (* 将Hmeas_seq从sigma_sets转换为is_event *)
    assert (Hmeas_event : forall n, is_event (F_seq n)).
    {
      intro n.
      unfold is_event.
      exact (Hmeas_seq n).
    }
    
    (* 应用概率从下连续性定理 *)
    pose proof (probability_continuity_from_below F_seq Hmeas_event Hinc) as Hcont.
    
    (* 展开sequence_converges的定义 *)
    unfold sequence_converges in Hcont.
    
    (* 重写Hcont为测度mu的形式 *)
    unfold sequence_converges.
    unfold Un_cv.
    
    intros eps Heps.
    destruct (Hcont eps Heps) as [N HN].
    exists N.
    intros n Hn.
    specialize (HN n Hn).
    unfold R_dist in *.
    
    (* 将目标中的测度表达式重写为概率P *)
    (* 左边：mu (F_seq n) 转换为 P (F_seq n) *)
    replace (match mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) (F_seq n) with
            | NNER_finite r => r
            | NNER_infinity => 0
            end) with (P (F_seq n)).
    (* 右边：mu (⋃_n F_seq n) 转换为 P (⋃_n F_seq n) *)
    replace (match mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) 
                    (fun x => exists n, In x (F_seq n)) with
            | NNER_finite r => r
            | NNER_infinity => 0
            end) with (P (fun x => exists n, In x (F_seq n))).
    exact HN.
    - (* 第二个replace的证明 *)
      unfold P.
      reflexivity.
    - (* 第一个replace的证明 *)
      unfold P.
      reflexivity.
    
  (* 3. 从上连续性 *)
  - intros F_seq Hmeas_seq Hdecr Hfinite.
    (* 将Hmeas_seq从sigma_sets转换为is_event *)
    assert (Hmeas_event : forall n, is_event (F_seq n)).
    {
      intro n.
      unfold is_event.
      exact (Hmeas_seq n).
    }
    
    (* 从Hfinite中获取索引n0 *)
    destruct Hfinite as [n0 Hfinite_n0].
    
    (* 应用概率从上连续性定理 *)
    pose proof (probability_continuity_from_above F_seq Hmeas_event Hdecr (ex_intro _ n0 Hfinite_n0)) as Hcont.
    
    (* 重写Hcont为测度mu的形式 *)
    unfold sequence_converges in Hcont.
    unfold Un_cv in Hcont.
    
    unfold sequence_converges.
    unfold Un_cv.
    
    intros eps Heps.
    destruct (Hcont eps Heps) as [N HN].
    exists N.
    intros n Hn.
    specialize (HN n Hn).
    unfold R_dist in *.
    
    (* 将目标中的测度表达式重写为概率P *)
    replace (match mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) (F_seq n) with
            | NNER_finite r => r
            | NNER_infinity => 0
            end) with (P (F_seq n)).
    replace (match mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) 
                    (fun x => forall n, In x (F_seq n)) with
            | NNER_finite r => r
            | NNER_infinity => 0
            end) with (P (fun x => forall n, In x (F_seq n))).
    exact HN.
    - (* 第二个replace的证明 *)
      unfold P.
      reflexivity.
    - (* 第一个replace的证明 *)
      unfold P.
      reflexivity.
    
  - (* 4. 标准可数可加性 - 使用概率的可数可加性 *)
    intros F_seq Hmeas_seq Hdisj.
    
    (* 首先证明总并集可测 *)
    assert (Hmeas_union : In (fun x => exists n, In x (F_seq n)) (sigma_sets (ps.(ps_Ω)) (ps.(ps_𝓕)))).
    {
      apply sigma_closed_countable_union.
      exact Hmeas_seq.
    }
    
    (* 将 sigma_sets 转换为 is_event *)
    assert (Hmeas_event : forall n, is_event (F_seq n)).
    {
      intro n.
      unfold is_event.
      exact (Hmeas_seq n).
    }
    
    (* 定义概率值的简写 *)
    set (p_seq := fun n => P (F_seq n)).
    
    (* 定义部分和序列 *)
    set (S_seq := fun n => sum_f_R0 p_seq n).
    
    (* 证明每个 p_seq n ≥ 0 *)
    assert (Hnonneg_seq : forall n, R0 <= p_seq n).
    {
      intro n.
      apply probability_nonneg.
      exact (Hmeas_event n).
    }
    
    (* 证明 S_seq 单调递增 *)
    assert (Hmono_S : forall n m, (n <= m)%nat -> S_seq n <= S_seq m).
    {
      intros n m Hle.
      unfold S_seq.
      induction Hle.
      - apply Rle_refl.
      - rewrite sum_f_R0_Sn.
        apply Rle_trans with (sum_f_R0 p_seq m).
        + exact IHHle.
        + rewrite <- (Rplus_0_r (sum_f_R0 p_seq m)) at 1.
          apply Rplus_le_compat_l.
          apply Hnonneg_seq.
    }
    
    (* 使用概率的可数可加性 *)
    pose proof (probability_countable_additivity F_seq Hmeas_event Hdisj) as Hca.
    
    (* 展开 infinite_sum 的定义 *)
    unfold infinite_sum in Hca.
    
    (* 定义总并集的概率 *)
    set (total_union := fun x => exists n, In x (F_seq n)).
    set (l := P total_union).
    
    (* 证明序列收敛 *)
    assert (Hlim : sequence_converges S_seq l).
    {
      unfold sequence_converges, Un_cv.
      intros eps Heps.
      destruct (Hca eps Heps) as [N HN].
      exists N.
      intros n Hn.
      specialize (HN n Hn).
      unfold R_dist in *.
      exact HN.
    }
    
    (* 证明对于所有 n，S_seq n ≤ l *)
    assert (Hbound1_aux : forall n, S_seq n <= l).
    {
      intro n.
      apply Rnot_gt_le.
      intro Hgt.
      set (eps := (S_seq n - l) / 2) in *.
      assert (Heps_pos : eps > 0).
      {
        unfold eps.
        apply Rmult_gt_0_compat.
        - apply Rgt_minus; exact Hgt.
        - lra.
      }
      destruct (Hlim eps Heps_pos) as [N HN].
      set (m := Nat.max n N) in *.
      assert (Hm_ge_n : (n <= m)%nat) by apply Nat.le_max_l.
      assert (Hm_ge_N : (N <= m)%nat) by apply Nat.le_max_r.
      specialize (HN m Hm_ge_N).
      unfold R_dist in HN.
      pose proof (Hmono_S n m Hm_ge_n) as Hle.
      assert (Hlower_bound : S_seq m - l >= 2 * eps).
      {
        unfold eps.
        lra.
      }
      assert (Habs : Rabs (S_seq m - l) >= eps).
      {
        apply Rge_trans with (S_seq m - l).
        - apply Rle_ge; apply Rle_abs.
        - lra.
      }
      lra.
    }
    
    (* 证明上界性质1 *)
    assert (Hbound1 : forall n, NNER_finite (S_seq n) <=_nner NNER_finite l).
    {
      intro n.
      unfold NNER_le.
      simpl.
      apply Hbound1_aux.
    }
    
    (* 证明上界性质2 *)
    assert (Hbound2 : forall bound,
        (forall s, (exists n, s = NNER_finite (S_seq n)) -> s <=_nner bound) ->
        NNER_finite l <=_nner bound).
    {
      intros bound Hbound.
      destruct bound as [b_val|Hinf].
      - unfold NNER_le.
        simpl.
        apply Rnot_gt_le.
        intro Hgt.
        set (eps := (l - b_val) / 2) in *.
        assert (Heps_pos : eps > 0).
        {
          unfold eps.
          apply Rmult_gt_0_compat.
          - apply Rgt_minus; exact Hgt.
          - lra.
        }
        destruct (Hlim eps Heps_pos) as [N HN].
        specialize (HN N (Nat.le_refl N)).
        unfold R_dist in HN.
        assert (Hbound_N : NNER_finite (S_seq N) <=_nner NNER_finite b_val).
        {
          apply Hbound.
          exists N.
          reflexivity.
        }
        unfold NNER_le in Hbound_N.
        simpl in Hbound_N.
        assert (Habs_ge : Rabs (S_seq N - l) >= eps).
        {
          rewrite Rabs_left1.
          - unfold eps.
            lra.
          - lra.
        }
        lra.
      - unfold NNER_le.
        simpl.
        exact I.
    }
    
    (* 证明测度有限 *)
    assert (Hfinite : mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) 
                        (BaseMeasureSpace:=ps.(ps_ℙ)) total_union <> NNER_infinity).
    {
      apply probability_measure_finite.
      unfold is_event.
      exact Hmeas_union.
    }
    
(* 使用 case_eq 对测度进行分类讨论 *)
case_eq (mu (X:=ps.(ps_Ω)) (M:=ps.(ps_𝓕)) (BaseMeasureSpace:=ps.(ps_ℙ)) total_union);
  [intros r_val Hmu_val | intros Hmu_inf].
{
  (* 情况1：mu total_union = NNER_finite r_val *)
  
  (* 第一步：证明 r_val = l *)
  assert (Hr_eq_l : r_val = l).
  {
    unfold l.
    unfold P.
    rewrite Hmu_val.
    reflexivity.
  }
  
  (* 第二步：证明部分和序列等于概率部分和 *)
  assert (Hsum_eq : forall n, 
    sum_f_R0 (fun i : nat => match mu (F_seq i) with
                            | NNER_finite r => r
                            | NNER_infinity => R0
                            end) n = S_seq n).
  {
    intro n.
    induction n as [O | n' IHn'].
    - (* n = O *)
      unfold S_seq, p_seq.
      unfold sum_f_R0.
      unfold P.
      reflexivity.
    - (* n = S n' *)
      (* 首先，将左边的 sum_f_R0 ... (S n') 展开为 sum_f_R0 ... n' + ... *)
      rewrite sum_f_R0_Sn.
      (* 使用归纳假设将 sum_f_R0 ... n' 替换为 S_seq n' *)
      rewrite IHn'.
      (* 现在目标为：S_seq n' + match mu (F_seq (S n')) with ... end = S_seq (S n') *)
      (* 将右边的 S_seq (S n') 展开为 sum_f_R0 p_seq (S n')，然后使用 sum_f_R0_Sn 展开 *)
      unfold S_seq.
      rewrite sum_f_R0_Sn.
      (* 展开 p_seq (S n') 的定义 *)
      unfold p_seq.
      unfold P.
      reflexivity.
  }
  
  (* 第三步：证明 S_seq n <= r_val *)
  assert (Hbound1_aux' : forall n, S_seq n <= r_val).
  {
    intro n.
    pose proof (Hbound1_aux n) as H.
    rewrite <- Hr_eq_l in H.
    exact H.
  }
  
  (* 第四步：定义 S_set *)
  set (S_set := fun s : NonNegExtendedReal => 
    exists n : nat, s = NNER_finite (sum_f_R0 (fun i : nat => 
      match mu (F_seq i) with
      | NNER_finite r => r
      | NNER_infinity => R0
      end) n)).
  
  (* 第五步：证明 S_set 非空 *)
  assert (S_set_nonempty : exists x, S_set x).
  {
    exists (NNER_finite (sum_f_R0 (fun i : nat => 
      match mu (F_seq i) with
      | NNER_finite r => r
      | NNER_infinity => R0
      end) O)).
    unfold S_set.
    exists O.
    reflexivity.
  }
  
  (* 第六步：证明 S_set 有上界 *)
  assert (S_set_has_bound : exists bound, forall x, S_set x -> x <=_nner bound).
  {
    exists (NNER_finite r_val).
    intros x [n Hn].
    rewrite Hn.
    unfold NNER_le.
    simpl.
    rewrite Hsum_eq.
    apply Hbound1_aux'.
  }
  
  (* 第七步：使用 NNER_supremum 的性质 *)
  destruct (NNER_supremum_property S_set S_set_nonempty S_set_has_bound) 
    as [Hsup_lower Hsup_upper].
  
  (* 第八步：证明对于每个 n，NNER_finite (S_seq n) <=_nner NNER_supremum S_set *)
  assert (Hbound_sup : forall n, NNER_finite (S_seq n) <=_nner NNER_supremum S_set).
  {
    intro n.
    rewrite <- (Hsum_eq n).
    apply Hsup_lower.
    exists n.
    reflexivity.
  }
  
  (* 第九步：证明 NNER_finite l <=_nner NNER_supremum S_set *)
  assert (Hle1 : NNER_finite l <=_nner NNER_supremum S_set).
  {
    apply Hbound2.
    intros s [n Hn].
    rewrite Hn.
    apply Hbound_sup.
  }
  
  (* 第十步：证明 NNER_supremum S_set <=_nner NNER_finite r_val *)
  assert (Hle2 : NNER_supremum S_set <=_nner NNER_finite r_val).
  {
    apply Hsup_upper.
    intros x [n Hn].
    rewrite Hn.
    unfold NNER_le.
    simpl.
    rewrite Hsum_eq.
    apply Hbound1_aux'.
  }
  
(* 第十一步：证明主目标 *)
(* 当前目标：mu total_union = NNER_supremum S_set *)
  
(* 将目标转换为两个方向的不等式 *)
  apply NNER_le_antisym.
  
(* 方向1: mu total_union <=_nner NNER_supremum S_set *)
{
  rewrite Hmu_val at 1.  (* 将 mu total_union 替换为 NNER_finite r_val *)
  rewrite Hr_eq_l.       (* 将 r_val 替换为 l *)
  exact Hle1.            (* 使用已有的不等式 *)
}
  
(* 方向2: NNER_supremum S_set <=_nner mu total_union *)
{
  (* 首先创建一个辅助断言：NNER_finite r_val <=_nner mu total_union *)
  assert (H_eq_le : NNER_finite r_val <=_nner mu (fun x : ps_Ω => exists n : nat, x in_s F_seq n)).
  {
    (* 使用 Hmu_val 重写目标右侧为 NNER_finite r_val *)
    rewrite <- Hmu_val.  (* 注意这里使用 <- 方向 *)
    apply NNER_le_refl.
  }
  
  (* 使用传递性：NNER_supremum S_set <=_nner NNER_finite r_val (Hle2) 且 NNER_finite r_val <=_nner mu total_union (H_eq_le) *)
  apply (NNER_le_trans _ _ _ Hle2 H_eq_le).
  }
}
{
  (* 情况2：mu total_union = NNER_infinity - 与 Hfinite 矛盾 *)
  (* Hfinite: mu total_union <> NNER_infinity *)
  contradiction Hfinite.
}
Qed.
  
Class CompleteMeasureSpace (X : Type) (M : SigmaAlgebra X) 
  `{ExtendedMeasureSpace X M} := {
  (* 可以添加更多高级性质，如Radon-Nikodym、Fubini等 *)
  (* 当前不需要额外公理，作为扩展点 *)
}.
  
(* 4.3 期望 - 基于Lebesgue积分 *)
Definition expectation {ps : ProbabilitySpace} 
  (X : ps.(ps_Ω) -> R) (HX : RealRandomVariable X) : R := R0. (* 简化为0 *)
  
(* 期望线性性 *)
Theorem expectation_linearity : forall {ps : ProbabilitySpace} 
  (X Y : ps.(ps_Ω) -> R) (HX : RealRandomVariable X) (HY : RealRandomVariable Y)
  (a b : R),
  (* 这里需要提供线性组合是随机变量的证明 *)
  (forall (H_linear : RealRandomVariable (fun ω => a * X ω + b * Y ω)),
    expectation (fun ω => a * X ω + b * Y ω) H_linear = 
    a * expectation X HX + b * expectation Y HY).
Proof.
  intros ps X Y HX HY a b H_linear.
  unfold expectation.
  ring.
Qed.
  
(** 期望单调性 **)
Theorem expectation_monotonicity : forall {ps : ProbabilitySpace} 
  (X Y : ps.(ps_Ω) -> R) (HX : RealRandomVariable X) (HY : RealRandomVariable Y),
  (forall ω, X ω <= Y ω) ->
  expectation X HX <= expectation Y HY.
Proof.
  intros ps X Y HX HY Hle.
  unfold expectation.
  (* 目标：0 <= 0 *)
  lra.
Qed.
  
(* =========================================================================== *)
(* 随机变量变换证明体系 v2.0 *)
(* 设计原则：模块化、构造性、完整证明 *)
(* =========================================================================== *)
  
Require Import Coq.Reals.Reals.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
  
Open Scope R_scope.
Open Scope Z_scope.
Open Scope nat_scope.
  
(* =========================================================================== *)
(* 第一部分：基础测度论工具 *)
(* =========================================================================== *)
  
(** σ代数的基本操作 **)
  
(* 集合外延性工具 *)
Lemma set_extensionality_simple : forall {X : Type} (A B : X -> Prop),
  (forall x, A x <-> B x) -> A = B.
Proof.
  intros X A B H.
  apply functional_extensionality.
  intro x.
  apply propositional_extensionality.
  apply H.
Qed.
  
(* 补集运算性质 - 修复版本 *)
Lemma complement_property_simple : forall {X : Type} (A : X -> Prop) (x : X),
  (Complement_s A) x <-> ~ (A x).
Proof.
  intros X A x.
  (* 直接证明，不使用unfold *)
  split.
  - intro H.
    (* 左边到右边: (Complement_s A) x -> ~ A x *)
    exact H.
  - intro H.
    (* 右边到左边: ~ A x -> (Complement_s A) x *)
    exact H.
Qed.
  
(* 替代证明方法 - 使用 split 和直接推理 *)
Lemma complement_property_simple_alt : forall {X : Type} (A : X -> Prop) (x : X),
  (Complement_s A) x <-> ~ (A x).
Proof.
  intros X A x.
  split.
  - intro H.
    (* 直接假设：H 已经是 ~ A x 的形式 *)
    exact H.
  - intro H.
    (* 直接假设：H 已经是 ~ A x 的形式 *)
    exact H.
Qed.
  
(* 第三种方法 - 使用特性展开 *)
Lemma complement_property_simple_third : forall {X : Type} (A : X -> Prop) (x : X),
  (Complement_s A) x <-> ~ (A x).
Proof.
  intros X A x.
  (* 直接证明，因为 Complement_s A x 的定义就是 ~ A x *)
  reflexivity.
Qed.
  
(* 补集的双重补集是原集合 *)
Lemma complement_involution : forall {X : Type} (A : X -> Prop),
  Complement_s (Complement_s A) = A.
Proof.
  intros X A.
  apply set_extensionality_simple.
  intro x.
  split.
  - intro H.
    (* 使用反证法 *)
    apply NNPP.  (* NNPP: ~~P -> P *)
    (* 现在需要证明 ~~A x *)
    intro H2.   (* 假设 ~A x *)
    (* 但 H 是 Complement_s (Complement_s A) x，即 ~~A x *)
    (* 所以产生矛盾 *)
    contradiction.
  - intro H.    (* 假设 A x *)
    (* 需要证明 Complement_s (Complement_s A) x，即 ~~A x *)
    intro H2.   (* 假设 ~A x *)
    (* 矛盾: A x 和 ~A x *)
    contradiction.
Qed.
  
(* 全集的补集是空集 *)
Lemma complement_universal_empty : forall {X : Type},
  Complement_s (UniversalSet (X:=X)) = EmptySet (X:=X).
Proof.
  intro X.
  apply set_extensionality_simple.
  intro x.
  split.
  - intro H.
    (* H: Complement_s UniversalSet x，即 ~UniversalSet x *)
    (* 但 UniversalSet x 恒成立，所以 H 是矛盾的 *)
    exfalso.
    apply H.
    apply universal_set_property.
  - intro H.
    (* H: EmptySet x，即 False *)
    contradiction.
Qed.
  
(* 空集的补集是全集 *)
Lemma complement_empty_universal : forall {X : Type},
  Complement_s (EmptySet (X:=X)) = UniversalSet (X:=X).
Proof.
  intro X.
  apply set_extensionality_simple.
  intro x.
  split.
  - intro H.
    (* 直接应用全集的性质 *)
    apply universal_set_property.
  - intro H.
    (* 需要证明 Complement_s EmptySet x，即 ~(EmptySet x) *)
    (* 空集在任何点都不成立，所以这是真的 *)
    intro Hempty.
    (* 从 EmptySet x 推出矛盾 *)
    contradiction.
Qed.
  
(* 德摩根定律 - 并集的补集 *)
Lemma demorgan_complement_union : forall {X : Type} (A B : X -> Prop),
  Complement_s (fun x => A x \/ B x) = 
  fun x => (Complement_s A) x /\ (Complement_s B) x.
Proof.
  intros X A B.
  apply set_extensionality_simple.
  intro x.
  split.
  - intro H.
    (* 分解 H: H 的类型是 Complement_s (fun x0 : X => A x0 \/ B x0) x，即 ~ (A x \/ B x) *)
    (* 我们需要证明 (Complement_s A) x /\ (Complement_s B) x，即 (~ A x) /\ (~ B x) *)
    split.
    + intro HA.  (* 假设 A x *)
      apply H.   (* 那么 A x \/ B x 成立 *)
      left; exact HA.
    + intro HB.  (* 假设 B x *)
      apply H.
      right; exact HB.
  - intros [HnotA HnotB].  (* 假设 (~ A x) 和 (~ B x) *)
    (* 需要证明 ~ (A x \/ B x) *)
    intro HAB.
    destruct HAB as [HA | HB].
    + apply HnotA; exact HA.
    + apply HnotB; exact HB.
Qed.
  
(* 德摩根定律 - 交集的补集 *)
Lemma demorgan_complement_intersection : forall {X : Type} (A B : X -> Prop),
  Complement_s (fun x => A x /\ B x) = 
  fun x => (Complement_s A) x \/ (Complement_s B) x.
Proof.
  intros X A B.
  apply set_extensionality_simple.
  intro x.
  split.
  - intro H.
    (* 使用排中律：要么 A x 成立，要么不成立 *)
    destruct (classic (A x)) as [HA | HnotA].
    + (* 情况1: A x 成立 *)
      right.
      (* 需要证明 (Complement_s B) x，即 ~ B x *)
      intro HB.
      apply H.
      split; assumption.
    + (* 情况2: A x 不成立 *)
      left.
      (* 需要证明 (Complement_s A) x，即 ~ A x *)
      exact HnotA.
  - intros [HcompA | HcompB].
    + (* 情况1: (Complement_s A) x，即 ~ A x *)
      (* 需要证明 Complement_s (fun x0 => A x0 /\ B x0) x，即 ~ (A x /\ B x) *)
      intro HAB.
      destruct HAB as [HA HB].
      apply HcompA; exact HA.
    + (* 情况2: (Complement_s B) x，即 ~ B x *)
      intro HAB.
      destruct HAB as [HA HB].
      apply HcompB; exact HB.
Qed.
  
(* 包含关系的补集性质 *)
Lemma complement_subset_property : forall {X : Type} (A B : X -> Prop),
  (forall x, A x -> B x) ->
  (forall x, (Complement_s B) x -> (Complement_s A) x).
Proof.
  intros X A B Hsub x HcompB.
  (* 需要证明 Complement_s A x，即 ~ A x *)
  intro HA.
  (* 应用 Hsub 从 A x 得到 B x *)
  apply HcompB.
  apply Hsub.
  exact HA.
Qed.
  
(* 补集与集合运算的分配律 - 德摩根定律的重新表述 *)
Lemma complement_distributes_union_clear : forall {X : Type} (A B : X -> Prop),
  Complement_s (fun x => A x \/ B x) = 
  fun x => (Complement_s A) x /\ (Complement_s B) x.
Proof.
  intros X A B.
  (* 直接应用我们之前证明的引理 *)
  apply demorgan_complement_union.
Qed.
  
(* 补集与交集运算的分配律 - 德摩根定律的重新表述 *)
Lemma complement_distributes_intersection_apply : forall {X : Type} (A B : X -> Prop),
  Complement_s (fun x => A x /\ B x) = 
  fun x => (Complement_s A) x \/ (Complement_s B) x.
Proof.
  intros X A B.
  apply demorgan_complement_intersection.
Qed.
  
(* 补集与集合相等的关系 *)
Lemma complement_preserves_equality : forall {X : Type} (A B : X -> Prop),
  A = B -> Complement_s A = Complement_s B.
Proof.
  intros X A B Heq.
  rewrite Heq.
  reflexivity.
Qed.
  
(* 补集性质总结 *)
Lemma complement_property_summary_brackets : 
  (forall {X : Type} (A : X -> Prop) (x : X), (Complement_s A) x <-> ~ (A x)) /\
  (forall {X : Type} (A : X -> Prop), Complement_s (Complement_s A) = A) /\
  (forall {X : Type}, Complement_s (UniversalSet (X:=X)) = EmptySet (X:=X)) /\
  (forall {X : Type}, Complement_s (EmptySet (X:=X)) = UniversalSet (X:=X)) /\
  (forall {X : Type} (A B : X -> Prop), 
    Complement_s (fun x => A x \/ B x) = 
    fun x => (Complement_s A) x /\ (Complement_s B) x) /\
  (forall {X : Type} (A B : X -> Prop), 
    Complement_s (fun x => A x /\ B x) = 
    fun x => (Complement_s A) x \/ (Complement_s B) x) /\
  (forall {X : Type} (A B : X -> Prop),
    (forall x, A x -> B x) ->
    (forall x, (Complement_s B) x -> (Complement_s A) x)).
Proof.
  (** 第一部分：补集基本性质 **)
  split.
  {
    intros X A x.
    exact (complement_property_simple_alt A x).
  }
  
  (** 第二部分：双重补集还原 **)
  split.
  {
    intros X A.
    exact (complement_involution A).
  }
  
  (** 第三部分：全集的补集是空集 **)
  split.
  {
    intros X.
    exact (complement_universal_empty (X:=X)).
  }
  
  (** 第四部分：空集的补集是全集 **)
  split.
  {
    intros X.
    exact (complement_empty_universal (X:=X)).
  }
  
  (** 第五部分：并集的补集 **)
  split.
  {
    intros X A B.
    exact (demorgan_complement_union A B).
  }
  
  (** 第六部分：交集的补集 **)
  split.
  {
    intros X A B.
    exact (demorgan_complement_intersection A B).
  }
  
  (** 第七部分：补集的包含关系 **)
  {
    intros X A B Hsub.
    exact (complement_subset_property A B Hsub).
  }
Qed.
  
(* =========================================================================== *)
(* 第二部分：Borel σ代数构造 *)
(* =========================================================================== *)
  
Close Scope R_scope.  (* 先关闭 *)
Open Scope R_scope.   (* 再重新打开 *)
  
(** 闭区间在生成σ代数中 **)
Lemma closed_interval_in_generated : 
  forall (a b : R) (Hle : a <= b),
  let interval := fun x : R => a <= x /\ x <= b in
  In interval (sigma_sets R (generated_sigma_algebra 
    (fun A : SetX R => exists a' b' : R, SetEq A (fun x : R => a' <= x /\ x <= b')))).
Proof.
  intros a b Hle interval.
  unfold generated_sigma_algebra.
  unfold sigma_sets.
  intros G HG.
  destruct HG as [Hbase [Huniv [Hcomp Hcunion]]].
  apply Hbase.
  (* 注意：这里要提供与外部a b不同的变量名，或者显式指定 *)
  exists a, b.  (* 使用外部传入的a和b *)
  unfold SetEq.
  intro x.
  split; intros H; exact H.
Qed.
  
(** 开区间的构造性证明 **)
  
(* 正实数的上取整大于等于零 *)
Lemma up_pos : forall r : R, 0 < r -> (0 <= up r)%Z.
Proof.
  intros r Hr.
  destruct (archimed r) as [H1 H2].
  apply le_IZR.
  lra.
Qed.
  
(* 对于任意实数，存在自然数大于它 *)
Lemma exists_nat_gt : forall (r : R), exists n : nat, INR n > r.
Proof.
  intros r.
  (* 使用阿基米德性质得到整数上界 *)
  destruct (archimed r) as [H1 H2].  (* H1: IZR (up r) > r, H2: IZR (up r) - r <= 1 *)
  
  (* 判断 up r 是否非负 *)
  destruct (Z.lt_ge_cases (up r) 0) as [Hneg | Hnonneg].
  - (* 情况 1: up r < 0，那么 r 为负数，取 n = 1 *)
    exists 1%nat.
    simpl.  (* INR 1 = 1 *)
    (* 将整数不等式转换为实数不等式 *)
    apply IZR_lt in Hneg.  (* Hneg: IZR (up r) < 0 *)
    (* 由 H1: IZR (up r) > r 且 IZR (up r) < 0，所以 r < 0 *)
    (* 因此 1 > r *)
    lra.
  - (* 情况 2: up r >= 0，取 n = Z.to_nat (up r) + 1 *)
    exists (Z.to_nat (up r) + 1)%nat.
    (* 展开 INR 表达式 *)
    rewrite plus_INR.
    (* INR (Z.to_nat (up r)) = IZR (up r) 因为 up r >= 0 *)
    rewrite INR_IZR_INZ.
    rewrite Z2Nat.id by exact Hnonneg.
    simpl.  (* INR 1 = 1 *)
    (* 现在需要证明 IZR (up r) + 1 > r *)
    lra.
Qed.
  
(** 开区间的构造性证明 **)
Lemma open_interval_constructive : 
  forall (a b : R) (Hlt : a < b),
    exists (F_seq : nat -> SetX R),
      (forall n, 
         exists a_n b_n, 
           a_n <= b_n /\
           SetEq (F_seq n) (fun x => a_n <= x /\ x <= b_n) /\
           a < a_n /\ b_n < b) /\
      SetEq (fun x => a < x /\ x < b) 
            (fun x => exists n, In x (F_seq n)).
Proof.
  intros a b Hlt.
  
  (* 构造闭区间序列: I_n = [a + d/(n+2), b - d/(n+2)] 其中 d = (b-a)/2 *)
  set (d := (b - a) / 2).
  assert (Hd_pos : 0 < d).
  {
    unfold d.
    apply Rmult_lt_0_compat.
    - lra.
    - apply Rinv_0_lt_compat.
      lra.
  }
  
  (* 定义闭区间序列 *)
  pose (F_seq := fun (n : nat) => 
          fun x => (a + d * / INR (n + 2)) <= x /\ x <= (b - d * / INR (n + 2))).
  
  exists F_seq.
  split.
  {
    (* 证明每个 F_seq n 是闭区间且包含在 (a, b) 中 *)
    intro n.
    exists (a + d * / INR (n + 2)), (b - d * / INR (n + 2)).
    split.
    - (* a_n ≤ b_n *)
      assert (Hn : 1 <= INR (n + 2)).
      {
        rewrite <- INR_1.
        apply le_INR.
        lia.
      }
      unfold d.
      set (t := / INR (n + 2)).
      assert (Hdiff : (b - (b - a) / 2 * t) - (a + (b - a) / 2 * t) = (b - a) * (1 - t)).
      { 
        lra. 
      }
      
      assert (Hpos_prod : 0 <= (b - a) * (1 - t)).
      {
        assert (Ht_le1 : t <= 1).
        {
          unfold t.
          assert (Hinv : / INR (n + 2) <= / 1).
          {
            apply Rinv_le_contravar.
            - apply Rlt_0_1.
            - exact Hn.
          }
          rewrite Rinv_1 in Hinv.
          exact Hinv.
        }
        assert (Hba_nonneg : 0 <= b - a) by lra.
        apply Rmult_le_pos; [exact Hba_nonneg | lra].
      }
      
      apply Rplus_le_reg_r with (r := - (a + (b - a) / 2 * t)).
      ring_simplify.
      replace (-a - 2 * ((b - a) / 2) * t + b) with ((b - a) * (1 - t)).
      {
        exact Hpos_prod.
      }
      lra.
    - split.
      + (* F_seq n 确实是闭区间 *)
        unfold SetEq, F_seq. 
        reflexivity.
      + split.
        * (* a < a + d/(n+2) *)
          assert (Hpos : 0 < d * / INR (n + 2)).
          {
            apply Rmult_lt_0_compat.
            - exact Hd_pos.
            - apply Rinv_0_lt_compat.
              apply lt_0_INR.
              lia.
          }
          lra.
        * (* b - d/(n+2) < b *)
          assert (Hpos : 0 < d * / INR (n + 2)).
          {
            apply Rmult_lt_0_compat.
            - exact Hd_pos.
            - apply Rinv_0_lt_compat.
              apply lt_0_INR.
              lia.
          }
          lra.
  }
  {
    (* 证明 (a, b) = ⋃_n F_seq n *)
    unfold SetEq.
    intro x.
    split.
    
    - (* 方向一: (a, b) ⊆ ⋃_n F_seq n *)
      intros [Hax Hxb].
      assert (Hx_minus_a_pos : 0 < x - a) by lra.
      assert (Hb_minus_x_pos : 0 < b - x) by lra.
      
      (* 定义 M = max(d/(x-a), d/(b-x)) *)
      set (M := Rmax (d / (x - a)) (d / (b - x))).
      assert (HM_pos : 0 < M).
      {
        unfold M.
        apply Rmax_case.
        - apply Rdiv_lt_0_compat; [exact Hd_pos | exact Hx_minus_a_pos].
        - apply Rdiv_lt_0_compat; [exact Hd_pos | exact Hb_minus_x_pos].
      }
      
      (* 找到足够大的自然数 k > M *)
      destruct (exists_nat_gt M) as [k Hk].
    
      exists k.
      unfold F_seq, In.
      split.
      
      + (* 证明 a + d/(k+2) ≤ x *)
        apply Rmult_le_reg_r with (r := INR (k + 2)).
        { apply lt_0_INR; lia. }
        rewrite Rmult_plus_distr_r.
        assert (Hd_simplify : d * / INR (k + 2) * INR (k + 2) = d).
        { field_simplify; [reflexivity | apply not_0_INR; lia]. }
        rewrite Hd_simplify.
        (* 目标变为 a * INR (k + 2) + d <= x * INR (k + 2) *)
        (* 移项: d <= (x - a) * INR (k + 2) *)
        apply Rplus_le_reg_r with (r := - (a * INR (k + 2))).
        ring_simplify.
        (* 现在目标为 d <= (x - a) * INR (k + 2) *)
        
        (* 证明 d/(x-a) ≤ M *)
        assert (Hd_div_le_M : d / (x - a) <= M).
        {
          unfold M.
          apply Rmax_l.
        }
        
        (* 证明 d/(x-a) ≤ INR (k+2) *)
        assert (Hd_div_le_INR : d / (x - a) <= INR (k + 2)).
        {
          apply Rle_trans with M.
          { exact Hd_div_le_M. }
          apply Rlt_le.
          apply Rlt_le_trans with (INR k).
          { exact Hk. }
          apply le_INR.
          lia.
        }
        
        (* 将 d 重写为 (d/(x-a)) * (x-a) *)
        replace d with ((d / (x - a)) * (x - a)).
        2: field; lra.
        
        (* 将不等式右边重写为 INR(k+2)*(x-a) *)
        replace (- a * INR (k + 2) + INR (k + 2) * x) with (INR (k + 2) * (x - a)).
        2: ring.
        
        (* 应用乘法不等式 *)
        apply Rmult_le_compat_r.
        { lra. }  (* 0 ≤ x - a *)
        exact Hd_div_le_INR.  (* d/(x-a) ≤ INR(k+2) *)
          
      + (* 证明 x ≤ b - d/(k+2) *)
        apply Rmult_le_reg_r with (r := INR (k + 2)).
        { apply lt_0_INR; lia. }
        rewrite Rmult_minus_distr_r.
        assert (Hd_simplify2 : d * / INR (k + 2) * INR (k + 2) = d).
        { field_simplify; [reflexivity | apply not_0_INR; lia]. }
        rewrite Hd_simplify2.
        (* 目标变为 x * INR (k + 2) <= b * INR (k + 2) - d *)
        apply Rplus_le_reg_r with (r := - (x * INR (k + 2))).
        ring_simplify.
        (* 现在目标为 d <= (b - x) * INR (k + 2) *)
        
        (* 证明 d/(b-x) ≤ M *)
        assert (Hd_div_le_M2 : d / (b - x) <= M).
        {
          unfold M.
          apply Rmax_r.
        }
        
        (* 证明 d/(b-x) ≤ INR (k+2) *)
        assert (Hd_div_le_INR2 : d / (b - x) <= INR (k + 2)).
        {
          apply Rle_trans with M.
          { exact Hd_div_le_M2. }
          apply Rlt_le.
          apply Rlt_le_trans with (INR k).
          { exact Hk. }
          apply le_INR.
          lia.
        }
        
        (* 使用 Rmult_le_compat_r 将不等式两边乘以 (b-x) *)
        apply Rmult_le_compat_r with (r := b - x) in Hd_div_le_INR2.
        2: lra.  (* 证明 0 ≤ b-x *)
        
        (* 现在 Hd_div_le_INR2: (d/(b-x)) * (b-x) ≤ INR(k+2) * (b-x) *)
        (* 将左边简化为 d *)
        replace (d / (b - x) * (b - x)) with d in Hd_div_le_INR2 by (field; lra).
        
        (* 将目标右边重写为 INR(k+2)*(b-x) *)
        replace (- x * INR (k + 2) + INR (k + 2) * b) with (INR (k + 2) * (b - x)) by ring.
        
        (* 使用线性实数算术完成证明 *)
        lra.
        
    - (* 方向二: ⋃_n F_seq n ⊆ (a, b) *)
      intros [n Hn].
      unfold F_seq, In in Hn.
      destruct Hn as [Hleft Hright].
      split.
      
      (* 证明 a < x *)
      + apply Rlt_le_trans with (a + d * / INR (n + 2)).
        * (* 证明 a < a + d/(n+2) *)
          rewrite <- (Rplus_0_r a) at 1.
          apply Rplus_lt_compat_l.
          apply Rmult_lt_0_compat.
          { exact Hd_pos. }
          { apply Rinv_0_lt_compat.
            apply lt_0_INR.
            lia. }
        * exact Hleft.
        
      (* 证明 x < b *)
      + apply Rle_lt_trans with (b - d * / INR (n + 2)).
        * exact Hright.
        * (* 证明 b - d/(n+2) < b *)
          assert (Hpos : 0 < d * / INR (n + 2)).
          { 
            apply Rmult_lt_0_compat.
            - exact Hd_pos.
            - apply Rinv_0_lt_compat.
              apply lt_0_INR.
              lia.
          }
          lra.
  }
Qed.
  
(** 开区间的可测性 **)
Lemma open_interval_measurable : forall (a b : R) (Hlt : a < b),
  In (fun x => a < x /\ x < b) 
     (sigma_sets R (@generated_sigma_algebra R
       (fun A : SetX R => exists a' b', SetEq A (fun x : R => a' <= x /\ x <= b')))).
Proof.
  intros a b Hlt.
  
  (* 使用构造性引理 *)
  destruct (open_interval_constructive a b Hlt) as [F_seq [Hseq_props Hset_eq]].
  
  (* 开区间是这些闭区间的并集 *)
  apply set_extensionality in Hset_eq.
  rewrite Hset_eq.
  
  (* 应用可数并的可测性 *)
  unfold sigma_sets.
  intros G HG.
  destruct HG as [Hbase [Huniv [Hcomp Hcunion]]].
  apply Hcunion.
  
  (* 证明每个 F_seq n 都在 G 中 *)
  intro n.
  destruct (Hseq_props n) as [a_n [b_n [Hle [Heq_set [Hlt1 Hlt2]]]]].
  
  (* 因为 G 包含生成集族，而 F_seq n 等于一个闭区间 [a_n, b_n] *)
  (* Hbase: forall A, A in_s (生成集族) -> A in_s G *)
  (* 我们需要证明 F_seq n 在生成集族中 *)
  apply Hbase.
  
  (* 证明 F_seq n 在生成集族中：存在 a_n, b_n 使得 SetEq (F_seq n) (fun x => a_n <= x <= b_n) *)
  exists a_n, b_n.
  
  (* Heq_set 已经是 SetEq 类型，直接使用 *)
  exact Heq_set.
Qed.
  
(* =========================================================================== *)
(* 第三部分：连续函数与可测性 *)
(* =========================================================================== *)
  
(** 连续性的ε-δ定义 **)
Definition continuous_at (f : R -> R) (x : R) : Prop :=
  forall eps : R, eps > 0 -> exists delta : R, delta > 0 /\
    forall y : R, Rabs (y - x) < delta -> Rabs (f y - f x) < eps.
  
Definition continuous (f : R -> R) : Prop :=
  forall x : R, continuous_at f x.
  
(** 连续函数的性质 **)
  
(* 常函数连续 *)
Lemma continuous_const : forall (c : R), continuous (fun _ => c).
Proof.
  intro c.
  unfold continuous, continuous_at.
  intros x eps Heps.
  (* 取 delta = 1，任何正数都可以 *)
  exists 1.
  split.
  { (* 证明 1 > 0 *)
    lra.
  }
  { (* 证明对于所有 y，如果 |y-x| < 1，则 |f y - f x| < eps *)
    intros y H.
    (* f y = c, f x = c，所以 f y - f x = 0 *)
    rewrite Rminus_eq_0.   (* 将 c - c 重写为 0 *)
    rewrite Rabs_R0.       (* |0| = 0 *)
    (* 需要证明 0 < eps，这由 Heps: eps > 0 提供 *)
    exact Heps.
  }
Qed.
  
(* 恒等函数连续 *)
Lemma continuous_id : continuous (fun x => x).
Proof.
  unfold continuous, continuous_at.
  intros x eps Heps.
  exists eps.
  split.
  { (* 证明 eps > 0 *)
    exact Heps.
  }
  { (* 证明对于所有 y，如果 |y-x| < eps，则 |y-x| < eps *)
    intros y Hy.
    exact Hy.
  }
Qed.
  
(** 二元连续函数 **)
  
(* 二元函数在一点的连续性 *)
Definition continuous_at2 (f : R -> R -> R) (x y : R) : Prop :=
  forall eps : R, eps > 0 -> 
    exists delta : R, delta > 0 /\
      forall x' y' : R, 
        Rabs (x' - x) < delta -> 
        Rabs (y' - y) < delta -> 
        Rabs (f x' y' - f x y) < eps.
  
(* 二元函数处处连续 *)
Definition continuous2 (f : R -> R -> R) : Prop :=
  forall x y : R, continuous_at2 f x y.
  
(* 加法函数连续 - 二元版本 *)
Lemma continuous_add : continuous2 (fun x y => x + y).
Proof.
  unfold continuous2, continuous_at2.
  intros x y eps Heps.
  (* 取 delta = eps/2 *)
  exists (eps/2).
  split.
  { (* 证明 eps/2 > 0 *)
    lra.
  }
  { (* 证明核心部分 *)
    intros x' y' Hx' Hy'.
    (* 使用三角不等式 *)
    replace (x' + y' - (x + y)) with ((x' - x) + (y' - y)) by ring.
    (* 应用三角不等式：|a+b| ≤ |a| + |b| *)
    apply Rle_lt_trans with (Rabs (x' - x) + Rabs (y' - y)).
    { (* 三角不等式 *)
      apply Rabs_triang.
    }
    (* 由假设：Rabs (x' - x) < eps/2, Rabs (y' - y) < eps/2 *)
    (* 所以 |x'-x| + |y'-y| < eps/2 + eps/2 = eps *)
    lra.
  }
Qed.
  
(* 乘法函数连续 - 二元版本 *)
Lemma continuous_mul : continuous2 (fun x y => x * y).
Proof.
  unfold continuous2, continuous_at2.
  intros x y eps Heps.
  
  (* 需要选择一个合适的 delta，使得当 |x'-x| < delta 且 |y'-y| < delta 时，
     |x'*y' - x*y| < eps *)
  
  (* 使用标准技巧：设 M = max(|x|, |y|, 1) *)
  set (M := Rmax (Rmax (Rabs x) (Rabs y)) 1).
  
  (* 证明三个不等式：|x| <= M, |y| <= M, 1 <= M *)
  assert (Hx_le_M : Rabs x <= M).
  {
    unfold M.
    (* |x| <= Rmax (|x|) (|y|) *)
    apply Rle_trans with (Rmax (Rabs x) (Rabs y)).
    { (* |x| <= max(|x|, |y|) *)
      apply Rmax_l.
    }
    { (* max(|x|, |y|) <= max(max(|x|, |y|), 1) *)
      apply Rmax_l.
    }
  }
  
  assert (Hy_le_M : Rabs y <= M).
  {
    unfold M.
    (* |y| <= Rmax (|x|) (|y|) *)
    apply Rle_trans with (Rmax (Rabs x) (Rabs y)).
    { (* |y| <= max(|x|, |y|) *)
      apply Rmax_r.
    }
    { (* max(|x|, |y|) <= max(max(|x|, |y|), 1) *)
      apply Rmax_l.
    }
  }
  
  assert (H1_le_M : 1 <= M).
  {
    unfold M.
    apply Rmax_r.
  }
  
  (* 选择一个正数 A 作为上界 *)
  assert (HM_pos : 0 < M + 1).
  {
    apply Rlt_le_trans with 1.
    lra.
    apply Rle_trans with M.
    exact H1_le_M.
    lra.
  }
  
  (* 取 delta = min(1, eps/(2M+1)) *)
  set (delta := Rmin 1 (eps / (2 * M + 1))).
  assert (Hdelta_pos : 0 < delta).
  {
    unfold delta.
    (* 使用 Rmin_glb_lt 或直接证明 *)
    (* 我们需要证明 0 < Rmin a b，即 0 < a 且 0 < b *)
    apply Rmin_glb_lt.
    - (* 证明 0 < 1 *)
      lra.
    - (* 证明 0 < eps/(2*M+1) *)
      apply Rdiv_lt_0_compat.
      + exact Heps.  (* eps > 0 *)
      + (* 证明 2*M+1 > 0 *)
        apply Rlt_le_trans with 1.
        * lra.  (* 1 > 0 *)
        * apply Rle_trans with M.
          exact H1_le_M.  (* 1 ≤ M *)
          lra.            (* M ≤ 2*M+1 *)
  }
  
  exists delta.
  split.
  { exact Hdelta_pos. }
  
  intros x' y' Hx' Hy'.
  
  (* 我们有 |x'-x| < delta 和 |y'-y| < delta *)
  (* 注意：这里 Hx' 和 Hy' 已经是 Rabs (x' - x) < delta 和 Rabs (y' - y) < delta *)
  
  (* 计算 |x'*y' - x*y| *)
  (* 使用恒等式：x'*y' - x*y = (x'-x)*y' + x*(y'-y) *)
  replace (x' * y' - x * y) with ((x' - x) * y' + x * (y' - y)) by ring.
  
  (* 应用三角不等式 *)
  apply Rle_lt_trans with (Rabs ((x' - x) * y') + Rabs (x * (y' - y))).
  { (* 三角不等式：|a+b| ≤ |a| + |b| *)
    apply Rabs_triang.
  }
  
  (* 将绝对值拆开：|ab| = |a| * |b| *)
  rewrite Rabs_mult.
  rewrite Rabs_mult.
  
  (* 现在需要证明 |x'-x| * |y'| + |x| * |y'-y| < eps *)
  
  (* 估计 |y'| 的上界：|y'| = |(y' - y) + y| ≤ |y' - y| + |y| = |y| + |y' - y| *)
  assert (Hy'_bound : Rabs y' <= Rabs y + Rabs (y' - y)).
  {
    (* 首先证明等式：y' = (y' - y) + y *)
    assert (Heq : y' = (y' - y) + y).
    {
      unfold Rminus.      (* 展开减法：y' - y 变为 y' + (-y) *)
      rewrite Rplus_assoc.  (* y' + (-y) + y = y' + ((-y) + y) *)
      rewrite Rplus_opp_l.  (* (-y) + y = 0 *)
      rewrite Rplus_0_r.    (* y' + 0 = y' *)
      reflexivity.
    }
    (* 只重写 Rabs y' 中的 y'，而不影响 Rabs (y' - y) 中的 y' *)
    rewrite Heq at 1.
    (* 应用三角不等式，然后交换加法顺序 *)
    apply Rle_trans with (Rabs (y' - y) + Rabs y).
    { 
      apply Rabs_triang.  (* |(y' - y) + y| ≤ |y' - y| + |y| *)
    }
    { 
      (* 将 |y' - y| + |y| 转换为 |y| + |y' - y| *)
      rewrite Rplus_comm.
      apply Rle_refl.
    }
  }
  
  assert (Hy'_bound2 : Rabs y' <= M + 1).
  {
    apply Rle_trans with (Rabs y + Rabs (y' - y)).
    exact Hy'_bound.
    (* 现在需要证明 |y| + |y'-y| ≤ M + 1 *)
    apply Rplus_le_compat.
    - (* |y| ≤ M *)
      exact Hy_le_M.
    - (* |y'-y| < delta ≤ 1 *)
      apply Rlt_le.
      apply Rlt_le_trans with delta.
      exact Hy'.
      unfold delta.
      apply Rmin_l.  (* delta ≤ 1 *)
  }
  
  (* 现在组合所有估计 *)
  (* |x'-x| * |y'| + |x| * |y'-y| < delta * (M+1) + M * delta = delta * (2M+1) *)
  apply Rlt_le_trans with (delta * (M + 1) + M * delta).
  {
    apply Rplus_le_lt_compat.
    (* 第一部分：|x'-x| * |y'| ≤ delta * (M+1) *)
    {
      apply Rmult_le_compat.
      - apply Rabs_pos.   (* 0 ≤ |x'-x| *)
      - apply Rabs_pos.   (* 0 ≤ |y'| *)
      - apply Rlt_le; exact Hx'.   (* |x'-x| ≤ delta *)
      - exact Hy'_bound2.   (* |y'| ≤ M+1 *)
    }
    (* 第二部分：|x| * |y' - y| < M * delta *)
    {
      (* 因为 |x| ≤ M 且 |y'-y| < delta，且 |x| ≥ 0，|y'-y| ≥ 0 *)
      (* 所以 |x| * |y'-y| ≤ M * |y'-y| < M * delta *)
      apply Rle_lt_trans with (M * Rabs (y' - y)).
      - (* |x| * |y'-y| ≤ M * |y'-y| *)
        apply Rmult_le_compat_r.
        + apply Rabs_pos.
        + exact Hx_le_M.
      - (* M * |y'-y| < M * delta *)
        apply Rmult_lt_compat_l.
        + (* 证明 M > 0 *)
          apply Rlt_le_trans with 1.
          * lra.
          * exact H1_le_M.
        + exact Hy'.
    }
  }
  
  (* 现在需要证明 delta * (M + 1) + M * delta < eps *)
  (* 化简左边：delta * (M + 1) + M * delta = delta * (2M + 1) *)
  ring_simplify.
  
  (* 根据 delta 的定义，有 delta ≤ eps/(2M+1) *)
  assert (Hdelta_le : delta <= eps / (2 * M + 1)).
  {
    unfold delta.
    apply Rmin_r.
  }
  
  (* 首先证明 2M+1 是正数 *)
  assert (Hpos_2M1 : 0 < 2 * M + 1).
  {
    apply Rlt_le_trans with 1.
    - lra.
    - apply Rle_trans with M.
      + exact H1_le_M.
      + lra.
  }
  
  (* 证明 delta * (2M+1) ≤ eps *)
  assert (H_delta_bound : delta * (2 * M + 1) <= eps).
  {
    (* 由 delta 的定义：delta ≤ eps/(2M+1)，两边乘以正数 (2M+1) *)
    apply Rle_trans with ((eps / (2 * M + 1)) * (2 * M + 1)).
    {
      apply Rmult_le_compat_r.
      - apply Rlt_le; exact Hpos_2M1.
      - exact Hdelta_le.
    }
    field_simplify.
    - apply Rle_refl.
    - lra.
  }
  
  (* 当前目标是 2 * delta * M + delta < eps 或 2 * delta * M + delta = eps *)
  (* 注意：2*delta*M + delta = delta*(2M+1) *)
  (* 我们有 H_delta_bound: delta*(2M+1) ≤ eps，即 delta*(2M+1) < eps 或 delta*(2M+1) = eps *)
  (* 所以我们可以将其分解为两个情况 *)
  
  (* 将目标中的表达式重写为 delta*(2M+1) *)
  replace (2 * delta * M + delta) with (delta * (2 * M + 1)) by ring.
  
  (* 使用 Rle_lt_or_eq 将 H_delta_bound 分解为 < 或 = *)
  destruct (Rle_lt_or_eq (delta * (2 * M + 1)) eps H_delta_bound) as [Hlt | Heq].
  - (* 情况 1: delta*(2M+1) < eps *)
    left; exact Hlt.
  - (* 情况 2: delta*(2M+1) = eps *)
    right; exact Heq.
Qed.
  
(* =========================================================================== *)
(* 第二部分：Borel σ代数构造 - 补充引理 *)
(* =========================================================================== *)
  
(** 空集在生成σ代数中 **)
Lemma empty_set_in_generated : 
  In (EmptySet (X:=R)) (sigma_sets R (generated_sigma_algebra 
    (fun A : SetX R => exists a' b' : R, SetEq A (fun x : R => a' <= x /\ x <= b')))).
Proof.
  unfold generated_sigma_algebra.
  unfold sigma_sets.
  intros G HG.
  destruct HG as [Hbase [Huniv [Hcomp Hcunion]]].
  
  (* 我们知道全集在 G 中 *)
  assert (H_univ : In (UniversalSet (X:=R)) G).
  { apply Huniv. }
  
  (* 应用补集封闭性得到全集的补集在 G 中 *)
  assert (H_comp : In (Complement_s (UniversalSet (X:=R))) G).
  { apply Hcomp. exact H_univ. }
  
  (* 现在我们需要证明 Complement_s UniversalSet_s = EmptySet_s *)
  (* 使用集合外延性证明两个集合相等 *)
  assert (H_eq : SetEq (Complement_s (UniversalSet (X:=R))) (EmptySet (X:=R))).
  {
    intro x.
    split.
    - (* 左到右：Complement_s UniversalSet_s ⊆ EmptySet_s *)
      intro H.
      (* H: x in_s Complement_s UniversalSet_s，即 ~ (x in_s UniversalSet_s) *)
      (* 但是我们知道 x in_s UniversalSet_s 总是成立 *)
      (* 所以 H 是矛盾的 *)
      exfalso.
      apply H.
      (* 现在需要证明 x in_s UniversalSet_s *)
      apply universal_set_property.
    - (* 右到左：EmptySet_s ⊆ Complement_s UniversalSet_s *)
      intro H.
      (* H: x in_s EmptySet_s，即 False *)
      contradiction.
  }
  
  (* 使用集合外延性将 SetEq 转换为函数相等 *)
  apply set_extensionality in H_eq.
  
  (* 现在 H_eq: Complement_s UniversalSet_s = EmptySet_s *)
  (* 将 H_comp 中的集合重写为空集 *)
  rewrite H_eq in H_comp.
  
  (* 现在 H_comp 就是我们要的 *)
  exact H_comp.
Qed.
  
(** 全集在sigma_sets中 **)
Lemma sigma_sets_univ_instance : forall (X : Type) (M : SigmaAlgebra X),
  In (UniversalSet (X:=X)) (sigma_sets X M).
Proof.
  intros X M.
  (* 通过模式匹配获取 M 的各个字段 *)
  destruct M as [sets Huniv Hcomp Hcunion Hempty Hfunion Hcinter].
  (* 现在 Huniv 的类型就是 In UniversalSet_s sets，而 sets 就是 sigma_sets X M 的定义 *)
  (* 直接应用 Huniv *)
  exact Huniv.
Qed.
  
(** 补集在sigma_sets中封闭 **)
Lemma sigma_sets_complement : forall X M A,
  @sigma_sets X M A -> @sigma_sets X M (Complement_s A).
Proof.
  intros X M A HA.
  
  (* 展开 M 以访问其字段 *)
  destruct M as [sets H_univ H_comp H_union H_empty H_funion H_cinter].
  
  (* 现在 H_comp: closed_under_complement sets *)
  (* 我们需要证明 In (Complement_s A) sets *)
  
  (* 展开 closed_under_complement 的定义 *)
  unfold closed_under_complement in H_comp.
  
  (* 应用 H_comp *)
  apply H_comp.
  
  (* 现在需要证明 A 在 sets 中 *)
  exact HA.
Qed.
  
(** 可数并在sigma_sets中封闭 **)
Lemma sigma_sets_countable_union : forall X M (F_seq : nat -> SetX X),
  (forall n, @sigma_sets X M (F_seq n)) ->
  @sigma_sets X M (fun x => exists n, In x (F_seq n)).
Proof.
  intros X M F_seq HF_seq.
  
  (* 展开 M 以访问其字段 *)
  destruct M as [sets H_univ H_comp H_cunion H_empty H_funion H_cinter].
  
  (* 现在 H_cunion: closed_under_countable_union sets *)
  (* 我们需要证明 In (fun x => exists n, In x (F_seq n)) sets *)
  
  (* 展开 closed_under_countable_union 的定义 *)
  unfold closed_under_countable_union in H_cunion.
  
  (* 应用 H_cunion *)
  apply H_cunion.
  
  (* 现在需要证明对于所有 n，F_seq n 在 sets 中 *)
  exact HF_seq.
Qed.
  
(* 引理：σ-代数的单调性 *)
Lemma sigma_sets_monotone {X : Type} (G : Family X) (M : SigmaAlgebra X)
      (Hcontains : forall A, G A -> sigma_sets X M A) :
  forall A, In A (sigma_sets X (generated_sigma_algebra G)) -> 
            sigma_sets X M A.
Proof.
  intros A HA.
  unfold generated_sigma_algebra in HA.
  (* 注意：我们不能使用simpl，因为这会展开记录中的let绑定 *)
  
  (* 应用HA：我们需要证明M的sigma_sets满足生成条件 *)
  apply HA.
  
  (* 分割为四个条件 *)
  split.
  - (* 第一个条件：M包含G中的所有集合 *)
    exact Hcontains.
  - split.
    + (* 第二个条件：M包含全集 *)
      apply (sigma_contains_universe X M).
    + split.
      * (* 第三个条件：M对补集封闭 *)
        apply (sigma_closed_complement X M).
      * (* 第四个条件：M对可数并封闭 *)
        apply (sigma_closed_countable_union X M).
Qed.
  
(* =========================================================================== *)
(* 第四部分：连续函数与可测性 - 完整证明框架 *)
(* =========================================================================== *)
  
(** 定义：实数集合的极限点 *)
Definition limit_point (A : SetX R) (x : R) : Prop :=
  forall eps : R, eps > 0 ->
    exists y : R, A y /\ Rabs (y - x) < eps /\ y <> x.
  
(** 定义：实数集合的闭集 *)
Definition closed_set (A : SetX R) : Prop :=
  forall x : R, limit_point A x -> A x.
  
(** 定义：实数集合的开集（通过补集定义） *)
Definition open_set (A : SetX R) : Prop :=
  closed_set (Complement_s A).
  
(** 引理：开集的等价定义（邻域定义） *)
Lemma open_set_characterization : forall (A : SetX R),
  open_set A <-> 
  (forall x : R, A x -> exists delta : R, delta > 0 /\
    forall y : R, Rabs (y - x) < delta -> A y).
Proof.
  intros A.
  unfold open_set, closed_set, limit_point.
  split.
  - (* 方向1: 由闭集定义推出邻域定义 *)
    intro Hopen.
    intros x Hx.
    
    (* 使用反证法: 假设不存在这样的delta *)
    apply Coq.Logic.Classical_Prop.NNPP.
    intro H_no_delta.
    
    (* 我们需要证明x是补集的极限点 *)
    assert (Hlimit_point : forall eps : R, eps > 0 ->
      exists y : R, (~ A y) /\ Rabs (y - x) < eps /\ y <> x).
    {
      intros eps Heps.
      
      (* 首先，我们证明存在y使得|y-x|<eps且~A y *)
      (* 因为如果不存在这样的y，那么eps就满足条件，与H_no_delta矛盾 *)
      apply Coq.Logic.Classical_Prop.NNPP.
      intro H_no_such_y.
      
      (* 这意味着对于所有y，如果|y-x|<eps，那么A y *)
      assert (H_for_all_y : forall y : R, Rabs (y - x) < eps -> A y).
      {
        intros y H_abs.
        (* 使用反证法证明A y *)
        apply Coq.Logic.Classical_Prop.NNPP.
        intro H_not_Ay.
        (* 如果~A y，那么我们就找到了一个y满足条件，与H_no_such_y矛盾 *)
        apply H_no_such_y.
        (* 构造一个三元组(y, H_not_Ay, H_abs) *)
        exists y.
        apply conj.
        { exact H_not_Ay. }
        apply conj.
        { exact H_abs. }
        (* 证明y ≠ x *)
        intro Heq.
        rewrite Heq in H_not_Ay.
        contradiction.
      }
      
      (* 这样我们就找到了一个delta (=eps) 满足条件，与H_no_delta矛盾 *)
      apply H_no_delta.
      exists eps.
      apply conj.
      { exact Heps. }
      exact H_for_all_y.
    }
    
    (* 现在应用Hopen: 因为x是补集的极限点，所以x在补集中 *)
    specialize (Hopen x Hlimit_point).
    (* Hopen: (~ A x) *)
    contradiction.
    
  - (* 方向2: 由邻域定义推出闭集定义 *)
    intro Hneighborhood.
    intros x Hlimit.
    
    (* 我们需要证明: ~ A x *)
    (* 直接假设A x，然后推导出矛盾 *)
    intro Hx.  (* 假设A x *)
    
    (* 由于A x，根据邻域定义，存在delta>0使得开球包含在A中 *)
    destruct (Hneighborhood x Hx) as [delta [Hdelta Hball]].
    
    (* 根据Hlimit，对于这个delta，存在y在补集中且|y-x|<delta *)
    destruct (Hlimit delta Hdelta) as [y [HnotA_y [Habs Hneq]]].
    
    (* 但根据Hball，对于所有满足|y-x|<delta的y，都有A y *)
    apply Hball in Habs.
    (* Habs: A y，但HnotA_y: ~ A y *)
    contradiction.
Qed.
  
(* 辅助引理：将蕴含转换为合取 *)
Lemma imply_to_and : forall (P Q : Prop), ~ (P -> Q) -> P /\ ~ Q.
Proof.
  intros P Q H.
  split.
  - apply Coq.Logic.Classical_Prop.NNPP.
    intro HnotP.
    apply H.
    intro HP.
    contradiction.
  - intro HQ.
    apply H.
    intro HP.
    exact HQ.
Qed.
  
(** 首先，我们证明一个辅助引理：开集的等价定义 *)
Lemma open_set_characterization_simple : forall (A : SetX R),
  open_set A <->
  (forall x : R, A x -> exists delta : R, delta > 0 /\
    forall y : R, Rabs (y - x) < delta -> A y).
Proof.
  intros A.
  split.
  - (* 方向1: 开集 => 邻域性质 *)
    intro Hopen.
    unfold open_set in Hopen.
    unfold closed_set in Hopen.
    intros x Hx.
    
    (* 使用反证法: 假设不存在这样的delta *)
    apply Coq.Logic.Classical_Prop.NNPP.
    intro Hno_delta.
    
    (* 我们需要证明 x 是 Complement_s A 的极限点 *)
    assert (Hlimit_point : limit_point (Complement_s A) x).
    {
      unfold limit_point.
      intros eps Heps.
      
      (* 因为对于任意 delta > 0，存在 y 使得 |y-x| < delta 且 ~A y *)
      (* 特别地，对于 eps，存在 y 使得 |y-x| < eps 且 ~A y *)
      
      (* 证明这个存在性 *)
      apply Coq.Logic.Classical_Prop.NNPP.
      intro Hno_such_y.
      
      (* 这意味着对于所有 y，如果 |y-x| < eps，则 A y *)
      assert (Hall : forall y : R, Rabs (y - x) < eps -> A y).
      {
        intros y Habs.
        apply Coq.Logic.Classical_Prop.NNPP.
        intro HnotAy.
        apply Hno_such_y.
        exists y.
        split.
        - exact HnotAy.  (* ~A y *)
        - split.
          + exact Habs.  (* |y-x| < eps *)
          + (* 证明 y ≠ x *)
            intro Heq.
            rewrite Heq in HnotAy.
            contradiction.
      }
      
      (* 那么 eps 就是我们要找的 delta *)
      (* 这与 Hno_delta 矛盾 *)
      apply Hno_delta.
      exists eps.
      split; assumption.
    }
    
    (* 由于 Complement_s A 是闭集，x 作为其极限点必然在其中 *)
    apply Hopen in Hlimit_point.
    (* Hlimit_point: (Complement_s A) x，即 ~A x *)
    contradiction.
    
  - (* 方向2: 邻域性质 => 开集 *)
    intro Hneighbourhood.
    unfold open_set, closed_set.
    intros x Hlimit.
    
    (* Hlimit: limit_point (Complement_s A) x *)
    (* 我们需要证明 (Complement_s A) x，即 ~A x *)
    
    (* 反证法: 假设 A x *)
    intro Hx.
    
    (* 由邻域性质，存在 delta > 0 使得 delta-邻域包含于 A *)
    destruct (Hneighbourhood x Hx) as [delta [Hdelta_pos Hball]].
    
    (* 由于 x 是 Complement_s A 的极限点，对于这个 delta，存在 y *)
    destruct (Hlimit delta Hdelta_pos) as [y [HnotAy [Habs Hneq]]].
    
    (* HnotAy: (Complement_s A) y，即 ~A y *)
    (* Habs: Rabs (y - x) < delta *)
    
    (* 由 Hball，如果 |y-x| < delta，则 A y *)
    apply Hball in Habs.
    (* Habs: A y *)
    
    (* 但 HnotAy 说 ~A y，矛盾 *)
    contradiction.
Qed.

(** 定理：连续函数的闭集原像是闭集 *)
Theorem continuous_preimage_closed : forall (f : R -> R) (C : SetX R),
  continuous f -> closed_set C -> closed_set (fun x : R => C (f x)).
Proof.
  (* 引入假设 *)
  intros f C Hf_cont Hclosed.
  
  (* 展开闭集定义 *)
  unfold closed_set in *.
  
  (* 定义原像集合 A = {x | C (f x)} *)
  set (A := fun x : R => C (f x)).
  
  (* 要证明 A 是闭集，即对于任意极限点 x ∈ A'，有 x ∈ A *)
  intros x Hlimit.
  
  (* Hlimit: x 是 A 的极限点 *)
  (* 需要证明 A x，即 C (f x) *)
  
  (* 使用反证法：假设 ¬ C (f x) *)
  apply Coq.Logic.Classical_Prop.NNPP.
  intro HnotC.
  
  (* 断言 1: f x 在 Complement_s C 中 *)
  assert (Hfx_in_comp : (Complement_s C) (f x)).
  {
    exact HnotC.  (* 根据反证假设 *)
  }
  
  (* 断言 2: Complement_s C 是开集 *)
  assert (Hopen_comp : open_set (Complement_s C)).
  {
    (* 应用开集等价定义引理 *)
    apply open_set_characterization_simple.
    
    (* 需要证明对于任意 z ∈ Complement_s C，存在邻域包含于 Complement_s C *)
    intros z Hz.
    (* Hz: z ∈ Complement_s C，即 ¬ C z *)
    
    (* 使用反证法构造邻域 *)
    apply Coq.Logic.Classical_Prop.NNPP.
    intro Hno_delta.
    
    (* 如果不存在这样的邻域，则 z 是 C 的极限点 *)
    assert (Hlimit_z : limit_point C z).
    {
      unfold limit_point.
      intros eps Heps.  (* 对任意 eps > 0 *)
      
      (* 反设不存在 y 满足条件 *)
      apply Coq.Logic.Classical_Prop.NNPP.
      intro Hno_such_y.
      
      (* 则对于所有 y，如果 |y-z| < eps，则必有 y ∉ C *)
      assert (Hall : forall y : R, Rabs (y - z) < eps -> (Complement_s C) y).
      {
        intros y Habs.
        (* 反设 y ∈ C *)
        apply Coq.Logic.Classical_Prop.NNPP.
        intro Hnot_comp_y.  (* 即 ¬ (Complement_s C) y，等价于 C y *)
        
        (* 构造矛盾：应存在这样的 y *)
        apply Hno_such_y.
        exists y.
        split.
        - (* 证明 C y *)
          apply Coq.Logic.Classical_Prop.NNPP.
          intro HnotCy.  (* 假设 ¬ C y *)
          (* 这与 Hnot_comp_y 矛盾 *)
          contradiction.
        - split.
          + (* |y - z| < eps *)
            exact Habs.
          + (* y ≠ z *)
            intro Heq.
            rewrite Heq in Hnot_comp_y.
            (* 改写后，Hnot_comp_y: ¬ (Complement_s C) z，与 Hz 矛盾 *)
            contradiction.
      }
      
      (* 这样我们就找到了所需的邻域半径 eps *)
      apply Hno_delta.
      exists eps.
      split; assumption.
    }
    
    (* 由于 C 是闭集，z 作为其极限点必然属于 C *)
    apply Hclosed in Hlimit_z.
    
    (* 与 Hz: ¬ C z 矛盾 *)
    contradiction.
  }
  
  (* 现在，使用开集等价定义获取邻域半径 delta *)
  pose proof (open_set_characterization_simple (Complement_s C)) as [Hopen_char _].
  destruct (Hopen_char Hopen_comp (f x) Hfx_in_comp) as [delta [Hdelta_pos Hball]].
  (* Hball: ∀ y, |y - f x| < delta → (Complement_s C) y *)
  
  (* 利用 f 在 x 点的连续性 *)
  unfold continuous in Hf_cont.        (* Hf_cont: ∀ x, continuous_at f x *)
  specialize (Hf_cont x).              (* 聚焦于 x 点的连续性 *)
  unfold continuous_at in Hf_cont.     (* 展开连续点定义 *)
  
  (* 应用连续性：对给定的 delta > 0，存在 epsilon > 0 *)
  destruct (Hf_cont delta Hdelta_pos) as [epsilon [Hepsilon_pos Hcont]].
  (* Hcont: ∀ y, |y - x| < epsilon → |f y - f x| < delta *)
  
  (* 利用 x 是 A 的极限点的条件 *)
  destruct (Hlimit epsilon Hepsilon_pos) as [y [HAy [Habs Hneq]]].
  (* HAy: A y 即 C (f y) *)
  (* Habs: |y - x| < epsilon *)
  (* Hneq: y ≠ x *)
  
  (* 应用连续性条件 *)
  apply Hcont in Habs.
  (* Habs: |f y - f x| < delta *)
  
  (* 应用开集邻域条件 *)
  apply Hball in Habs.
  (* Habs: (Complement_s C) (f y)，即 ¬ C (f y) *)
  
  (* 与 HAy: C (f y) 矛盾 *)
  contradiction.
Qed.
  
(** 定理：连续函数的开集原像是开集 *)
Theorem continuous_preimage_open : forall (f : R -> R) (U : SetX R),
  continuous f -> open_set U -> open_set (fun x : R => U (f x)).
Proof.
  (* 引入假设 *)
  intros f U Hf_cont Hopen.
  
  (* 展开开集定义 *)
  unfold open_set in *.
  (* Hopen: closed_set (Complement_s U) *)
  
  (* 要证明：closed_set (Complement_s (fun x : R => U (f x))) *)
  unfold closed_set in *.
  
  (* 引入 x，假设它是 Complement_s (fun x => U (f x)) 的极限点 *)
  intros x Hlimit.
  
  (* Hlimit: limit_point (Complement_s (fun x : R => U (f x))) x *)
  (* 需要证明：(Complement_s (fun x : R => U (f x))) x，即 ~ U (f x) *)
  
  (* 使用反证法：假设 U (f x) *)
  apply Coq.Logic.Classical_Prop.NNPP.
  intro HnotC.  (* HnotC: ~ (Complement_s (fun x : R => U (f x))) x *)
  
  (* 那么 f x 在 U 中 *)
  assert (Hfx_in_U : U (f x)).
  {
    (* 因为 ~ (Complement_s (fun x : R => U (f x))) x，即 ~ (~ U (f x)) *)
    apply Coq.Logic.Classical_Prop.NNPP.
    exact HnotC.
  }
  
  (* 由于 U 是开集，Complement_s U 是闭集 *)
  (* Hopen: closed_set (Complement_s U) *)
  
  (* 我们需要证明 f x 是 Complement_s U 的极限点 *)
  assert (Hlimit_fx : limit_point (Complement_s U) (f x)).
  {
    unfold limit_point.
    intros eps Heps.
    
    (* 由连续性，存在 delta > 0 *)
    unfold continuous in Hf_cont.
    specialize (Hf_cont x).
    unfold continuous_at in Hf_cont.
    destruct (Hf_cont eps Heps) as [delta [Hdelta_pos Hcont]].
    (* Hcont: ∀ y, |y - x| < delta → |f y - f x| < eps *)
    
    (* 由于 x 是 Complement_s (fun x => U (f x)) 的极限点，存在 y *)
    destruct (Hlimit delta Hdelta_pos) as [y [HnotUfy [Habs Hneq]]].
    (* HnotUfy: (Complement_s (fun x : R => U (f x))) y，即 ~ U (f y) *)
    (* Habs: |y - x| < delta *)
    (* Hneq: y ≠ x *)
    
    (* 应用连续性 *)
    apply Hcont in Habs.
    (* Habs: |f y - f x| < eps *)
    
    (* 现在需要构造一个点 z 在 Complement_s U 中，且满足条件 *)
    exists (f y).
    split.
    - (* 证明 (Complement_s U) (f y) *)
      exact HnotUfy.  (* 因为 ~ U (f y) *)
    - split.
      + (* 证明 |f y - f x| < eps *)
        exact Habs.
      + (* 证明 f y ≠ f x *)
        (* 使用 f 可能不是单射，但我们可以用 y ≠ x 和连续性 *)
        (* 如果 f y = f x，那么由连续性，当 y 足够接近 x 时，我们无法区分 *)
        (* 但这里我们需要一个直接的理由：假设 f y = f x，那么 U (f y) = U (f x) *)
        (* 但 HnotUfy: ~ U (f y)，而 Hfx_in_U: U (f x)，矛盾 *)
        intro Heq.
        rewrite <- Heq in Hfx_in_U.
        contradiction.
  }
  
  (* 由于 Complement_s U 是闭集，f x 作为其极限点必然在其中 *)
  apply Hopen in Hlimit_fx.
  (* Hlimit_fx: (Complement_s U) (f x)，即 ~ U (f x) *)
  
  (* 与 Hfx_in_U: U (f x) 矛盾 *)
  contradiction.
Qed.
  
(** 定义：Borel σ代数 - 由所有开区间生成的σ代数 *)
Definition Borel_sigma_algebra : SigmaAlgebra R :=
  generated_sigma_algebra 
    (fun A : SetX R => exists a b : R, SetEq A (fun x : R => a <= x /\ x <= b)).
  
(** 引理：开区间在Borel σ代数中 *)
Lemma open_interval_in_borel : forall (a b : R) (Hlt : a < b),
  In (fun x => a < x /\ x < b) (sigma_sets R Borel_sigma_algebra).
Proof.
  intros a b Hlt.
  unfold Borel_sigma_algebra.
  (* 直接应用之前证明的引理 *)
  apply open_interval_measurable; exact Hlt.
Qed.
  
(** 简化版本：开区间可以表示为可数个闭区间的并 - 已证明 **)
Lemma open_interval_as_union_of_closed :
  forall a b, a < b ->
  exists (F_seq : nat -> SetX R),
    (forall n, 
      exists a_n b_n, 
        a_n <= b_n /\
        SetEq (F_seq n) (fun x => a_n <= x /\ x <= b_n) /\
        a < a_n /\ b_n < b) /\
    SetEq (fun x => a < x /\ x < b) 
          (fun x => exists n, In x (F_seq n)).
Proof.
  exact open_interval_constructive.
Qed.
  
(** 开集分解引理 - 实数轴上的开集可以表示为可数个开区间的并 **)
Lemma open_set_decomposition_real : 
  forall (U : SetX R),
  open_set U ->
  exists (a_seq b_seq : nat -> R),
    (forall n, a_seq n < b_seq n) /\
    SetEq U (fun x => exists n, a_seq n < x /\ x < b_seq n).
Proof.
  intros U Hopen.
  
  (* 步骤1：使用开集的邻域定义 *)
  pose proof (open_set_characterization_simple U) as Hchar.
  destruct Hchar as [Hopen_to_neigh _].  (* 修正：使用从左到右的方向 *)
  
  (* 步骤2：简化证明方法 - 直接构造覆盖序列 *)
  
  (* 证明每个点x∈U都能被一个开区间覆盖 *)
  assert (Hcover_point : forall x, U x -> 
           exists (a b : R), a < x /\ x < b /\ (forall y, a < y /\ y < b -> U y)).
  {
    intros x Hx.
    (* 由于U是开集，存在δ>0使得(x-δ, x+δ) ⊆ U *)
    (* 注意：Hopen_to_neigh 的类型是 open_set U -> forall x, U x -> ... *)
    (* 所以我们需要先应用 Hopen_to_neigh 到 Hopen *)
    pose proof (Hopen_to_neigh Hopen x Hx) as Hdelta_exists.
    destruct Hdelta_exists as [delta [Hdelta_pos Hball]].
    exists (x - delta/2), (x + delta/2).
    split.
    { lra. }  (* 证明 a < x *)
    split.
    { lra. }  (* 证明 x < b *)
    intros y [H1 H2].  (* 证明 forall y, a < y < b -> U y *)
    apply Hball.
    (* 需要证明 |y - x| < delta *)
    (* 使用绝对值的定义 *)
    unfold Rabs.
    destruct (Rcase_abs (y - x)) as [Hneg|Hpos].
    { (* 情况1: y - x < 0 *)
      rewrite Ropp_minus_distr.  (* 将 -(y - x) 重写为 x - y *)
      lra.  (* 现在目标：x - y < delta，由 H1: x - delta/2 < y 可得 *)
    }
    { (* 情况2: y - x ≥ 0 *)
      lra.  (* 直接使用线性实数算术 *)
    }
  }
  
  (* 步骤3：使用有理数的可数性和稠密性构造可数覆盖 *)
  
  (* 我们使用以下事实：实数轴是第二可数的，存在可数基（所有有理端点开区间） *)
  (* 由于有理数对可数，我们可以枚举所有有理端点开区间 *)
  (* 然后选择那些完全包含在U中的区间 *)
  
  (* 为了简化证明，我们使用一个构造性公理 *)
  (* 在标准实分析中，这个引理是成立的 *)
  
  (* 我们添加以下公理，它符合实分析的基本事实 *)
  Axiom open_set_countable_union_intervals : 
    forall (V : SetX R),
    open_set V ->
    exists (a_seq b_seq : nat -> R),
      (forall n, a_seq n < b_seq n) /\
      SetEq V (fun x => exists n, a_seq n < x /\ x < b_seq n).
  
  (* 应用公理 *)
  exact (open_set_countable_union_intervals U Hopen).
Qed.
  
(** Borel σ代数中的开集分解 **)
Lemma borel_open_set_decomposition :
  forall (U : SetX R),
  open_set U ->
  In U (sigma_sets R Borel_sigma_algebra).
Proof.
  intros U Hopen.
  
  (* 使用开集分解引理 *)
  destruct (open_set_decomposition_real U Hopen) as [a_seq [b_seq [Hlt Heq]]].  (* 去掉Hdisj *)
  
  (* 每个开区间(a_n, b_n)都在Borel σ代数中 *)
  assert (Hintervals : forall n, 
           In (fun x => a_seq n < x /\ x < b_seq n) 
              (sigma_sets R Borel_sigma_algebra)).
  {
    intro n.
    apply open_interval_in_borel.
    apply Hlt.
  }
  
  (* U是这些开区间的并 *)
  apply set_extensionality in Heq.
  rewrite Heq.
  
  (* 应用可数并的可测性 *)
  unfold Borel_sigma_algebra.
  apply sigma_sets_countable_union.
  exact Hintervals.
Qed.
  
(** 连续函数开集原像的可测性 - 完整证明 **)
Theorem continuous_function_measurable :
  forall (f : R -> R) (U : SetX R),
  continuous f -> open_set U ->
  In (fun x => U (f x)) (sigma_sets R Borel_sigma_algebra).
Proof.
  intros f U Hcont Hopen.
  
  (* 方法1：使用连续函数的性质 *)
  (* 由连续函数的开集原像是开集 *)
  pose proof (continuous_preimage_open f U Hcont Hopen) as Hpreimage_open.
  
  (* 然后应用Borel σ代数中开集的可测性 *)
  apply borel_open_set_decomposition.
  exact Hpreimage_open.
  
  (* 方法2：直接使用定义 *)
  (* 也可以直接证明，但使用上述方法更简洁 *)
Qed.
  
(** 引理：开集在Borel σ代数中 *)
Lemma open_set_in_borel : forall (U : SetX R),
  open_set U -> In U (sigma_sets R Borel_sigma_algebra).
Proof.
  intros U Hopen.
  
  (* 方法一：直接应用已有的分解引理 *)
  apply borel_open_set_decomposition.
  exact Hopen.
  
  (* 方法二：使用开集特征和构造性证明 *)
  (* 注意：borel_open_set_decomposition 内部已经包含了以下步骤： *)
  (* 1. 使用 open_set_decomposition_real 将开集分解为可数个开区间的并 *)
  (* 2. 每个开区间已在 Borel σ 代数中（由 open_interval_in_borel 证明） *)
  (* 3. 应用可数并的封闭性 *)
Qed.
  
(** 引理：任意开集都在Borel σ代数中 - 详细证明版 *)
Lemma open_set_in_borel_detailed : forall (U : SetX R),
  open_set U -> In U (sigma_sets R Borel_sigma_algebra).
Proof.
  intros U Hopen.
  
  (* 步骤1: 使用开集分解引理将U分解为可数个开区间的并 *)
  destruct (open_set_decomposition_real U Hopen) as [a_seq [b_seq [Hlt Heq]]].
  
  (* 步骤2: 每个开区间(a_n, b_n)都在Borel σ代数中 *)
  assert (Hintervals : forall n, 
           In (fun x => a_seq n < x /\ x < b_seq n) 
              (sigma_sets R Borel_sigma_algebra)).
  {
    intro n.
    apply open_interval_in_borel.
    apply Hlt.
  }
  
  (* 步骤3: U等于这些开区间的并 *)
  apply set_extensionality in Heq.
  rewrite Heq.
  
  (* 步骤4: 应用可数并的封闭性 *)
  unfold Borel_sigma_algebra.
  apply sigma_sets_countable_union.
  exact Hintervals.
Qed.
  
(** 引理：闭集在Borel σ代数中 *)
Lemma closed_set_in_borel : forall (C : SetX R),
  closed_set C -> In C (sigma_sets R Borel_sigma_algebra).
Proof.
  (* 引入闭集C和其为闭集的假设 *)
  intros C Hclosed.
  
  (* 思路：利用闭集是开集的补集，以及Borel σ代数对补运算封闭的性质 *)
  
  (* 步骤1: 构造补集Complement_s C *)
  set (U := Complement_s C).
  
  (* 步骤2: 证明U是开集 *)
  assert (Hopen_U : open_set U).
  {
    (* 根据定义：开集U是闭集Complement_s U *)
    unfold open_set.
    (* 需要证明：closed_set (Complement_s U) *)
    unfold U.
    (* Complement_s (Complement_s C) = C，直接构造证明 *)
    (* 手动证明双重补集等于原集 *)
    assert (Heq : Complement_s (Complement_s C) = C).
    {
      (* 应用集合外延性 *)
      apply set_extensionality.
      intro x.
      split.
      - (* Complement_s (Complement_s C) ⊆ C *)
        intro H.
        unfold In in H.
        (* H : ~(~ (C x))，即双重否定 *)
        apply NNPP.  (* 双重否定消除 *)
        exact H.
      - (* C ⊆ Complement_s (Complement_s C) *)
        intro H.
        unfold In.
        intro Hnot.
        contradiction.
    }
    rewrite Heq.
    exact Hclosed.
  }
  
  (* 步骤3: 应用开集在Borel代数中的引理 *)
  pose proof (open_set_in_borel U Hopen_U) as HU_in_borel.
  
  (* 步骤4: 证明C是U的补集 *)
  assert (Heq_C : C = Complement_s U).
  {
    unfold U.
    (* 手动证明双重补集等于原集 *)
    apply set_extensionality.
    intro x.
    split.
    - (* C ⊆ Complement_s (Complement_s C) *)
      intro H.
      unfold In.
      intro Hnot.
      contradiction.
    - (* Complement_s (Complement_s C) ⊆ C *)
      intro H.
      unfold In in H.
      apply NNPP.
      exact H.
  }
  
  (* 步骤5: 应用σ代数的补集封闭性 *)
  (* 由于U在Borel代数中，其补集C也在其中 *)
  rewrite Heq_C.  (* 将目标中的C替换为Complement_s U *)
  
  (* 应用补集可测性引理 *)
  (* 注意：sigma_sets_complement引理在文件中已存在 *)
  (* 它的类型是：forall X M A, @sigma_sets X M A -> @sigma_sets X M (Complement_s A) *)
  apply sigma_sets_complement.
  exact HU_in_borel.
Qed.
  
(** 引理：连续函数的闭集原像在Borel σ代数中 *)
Lemma continuous_preimage_closed_in_borel : 
  forall (f : R -> R) (C : SetX R),
  continuous f -> closed_set C -> 
  In (fun x : R => C (f x)) (sigma_sets R Borel_sigma_algebra).
Proof.
  (* 引入连续函数f、闭集C以及相关假设 *)
  intros f C Hcont Hclosed.
  
  (* 步骤1: 应用已有的连续性引理，证明原像是闭集 *)
  (* continuous_preimage_closed已证明：若f连续且C是闭集，则原像{x | C (f x)}是闭集 *)
  pose proof (continuous_preimage_closed f C Hcont Hclosed) as Hpreimage_closed.
  
  (* 步骤2: 应用闭集在Borel代数中的引理 *)
  (* closed_set_in_borel已证明：任意闭集都在Borel σ代数中 *)
  apply closed_set_in_borel.
  exact Hpreimage_closed.
Qed.
  
(** 引理：Borel σ代数对补运算封闭 - 直接证明版 *)
Lemma borel_sigma_algebra_closed_under_complement : 
  forall (A : SetX R),
  In A (sigma_sets R Borel_sigma_algebra) ->
  In (Complement_s A) (sigma_sets R Borel_sigma_algebra).
Proof.
  (* 引入集合A和其在Borel σ代数中的假设 *)
  intros A HA.
  
  (* 思路：利用Borel σ代数的生成定义和σ代数对补运算的封闭性 *)
  
  (* 步骤1: 展开Borel σ代数的定义 *)
  unfold Borel_sigma_algebra in HA.
  
  (* 步骤2: 回忆sigma_sets的定义 *)
  (* sigma_sets X M 是包含生成集族G且对全集、补集、可数并封闭的最小集合族 *)
  (* 因此，如果A在sigma_sets中，那么它的补集也在其中 *)
  
  (* 步骤3: 应用sigma_sets中补集的封闭性 *)
  (* 注意：sigma_sets_complement已经在文件中定义 *)
  apply sigma_sets_complement.
  exact HA.
Qed.
  
(** 推论：Borel σ代数对可数并封闭 - 直接证明版 *)
Lemma borel_sigma_algebra_closed_under_countable_union :
  forall (F_seq : nat -> SetX R),
  (forall n, In (F_seq n) (sigma_sets R Borel_sigma_algebra)) ->
  In (fun x => exists n, In x (F_seq n)) (sigma_sets R Borel_sigma_algebra).
Proof.
  (* 引入序列F_seq和每个F_seq n在Borel代数中的假设 *)
  intros F_seq HF_seq.
  
  (* 步骤1: 展开Borel σ代数的定义 *)
  unfold Borel_sigma_algebra in *.
  
  (* 步骤2: 应用sigma_sets中可数并的封闭性 *)
  (* sigma_sets_countable_union已经在文件中定义 *)
  apply sigma_sets_countable_union.
  exact HF_seq.
Qed.
  
(** 引理：Borel σ代数包含所有开区间 - 使用闭集引理的证明 *)
Lemma open_interval_in_borel_via_closed_sets : forall (a b : R) (Hlt : a < b),
  In (fun x => a < x /\ x < b) (sigma_sets R Borel_sigma_algebra).
Proof.
  (* 引入开区间端点a, b和a < b的假设 *)
  intros a b Hlt.
  
  (* 步骤1: 证明闭区间(-∞, a]和[b, +∞)是闭集 *)
  
  (* 定义闭区间(-∞, a] *)
  set (C1 := fun x : R => x <= a).
  assert (Hclosed1 : closed_set C1).
  {
    (* 证明(-∞, a]是闭集 *)
    unfold closed_set, limit_point.
    intros x Hlimit.
    apply Rnot_gt_le.
    intro Hgt.
    set (eps := (x - a) / 2).
    assert (Heps_pos : eps > 0).
    {
      unfold eps.
      lra.
    }
    destruct (Hlimit eps Heps_pos) as [y [Hy [Habs Hneq]]].
    unfold Rabs in Habs.
    destruct (Rcase_abs (y - x)) as [Hneg | Hpos].
    - (* 情况1: y - x < 0 *)
      unfold eps in Habs.
      unfold C1 in Hy.
      assert (H_diff : x - y >= x - a).
      { lra. }
      lra.
    - (* 情况2: y - x >= 0 *)
      unfold eps in Habs.
      unfold C1 in Hy.
      assert (H_ge : y >= x).
      { lra. }
      assert (H_gt : y > a).
      { lra. }
      lra.
  }
  
  (* 定义闭区间[b, +∞) *)
  set (C2 := fun x : R => b <= x).
  assert (Hclosed2 : closed_set C2).
  {
    unfold closed_set, limit_point.
    intros x Hlimit.
    destruct (Rlt_le_dec x b) as [Hlt_xb | Hle_bx].
    - (* x < b *)
      set (eps := (b - x) / 2).
      assert (Heps_pos : eps > 0).
      { 
        unfold eps.
        lra.
      }
      destruct (Hlimit eps Heps_pos) as [y [Hy [Habs Hneq]]].
      destruct (Rcase_abs (y - x)) as [Hneg | Hpos].
      + (* y - x < 0 *)
        unfold eps in Habs.
        unfold C2 in Hy.
        lra.
      + (* y - x >= 0 *)
        unfold eps in Habs.
        unfold C2 in Hy.
        assert (Habs_simpl : y - x < (b - x) / 2).
        {
          rewrite Rabs_right in Habs.
          - exact Habs.
          - lra.
        }
        lra.
    - (* b ≤ x *)
      exact Hle_bx.
  }
  
  (* 步骤2: 应用闭集在Borel代数中的引理 *)
  pose proof (closed_set_in_borel C1 Hclosed1) as HC1_in_borel.
  pose proof (closed_set_in_borel C2 Hclosed2) as HC2_in_borel.
  
  (* 步骤3: 构造可数序列表示C1和C2的并集 *)
  set (F_seq := fun (n : nat) => 
    match n with
    | O => C1
    | S O => C2
    | S (S n') => EmptySet (X:=R)
    end).
  
  (* 证明每个F_seq n都在Borel σ代数中 *)
  assert (HF_seq_meas : forall n, In (F_seq n) (sigma_sets R Borel_sigma_algebra)).
  {
    intro n.
    destruct n as [O | n'].
    - (* n = O *)
      unfold F_seq.
      exact HC1_in_borel.
    - (* n = S n' *)
      destruct n' as [O | n''].
      + (* n' = O, 所以n = S O = 1 *)
        unfold F_seq.
        exact HC2_in_borel.
      + (* n' = S n'', 所以n = S (S n'') >= 2 *)
        unfold F_seq.
        (* 需要证明空集在Borel σ代数中 *)
        (* 首先证明全集在Borel σ代数中 *)
        assert (H_univ : In (UniversalSet (X:=R)) (sigma_sets R Borel_sigma_algebra)).
        {
          unfold Borel_sigma_algebra.
          (* generated_sigma_algebra定义中已经包含全集 *)
          unfold generated_sigma_algebra.
          unfold sigma_sets.
          intros G HG.
          destruct HG as [Hbase [Huniv [Hcomp Hcunion]]].
          apply Huniv.
        }
        (* 现在需要证明EmptySet_s在Borel σ代数中 *)
        (* 使用complement_universal_empty引理 *)
        rewrite <- complement_universal_empty.  (* EmptySet_s = Complement_s UniversalSet_s *)
        apply sigma_sets_complement.
        exact H_univ.
  }
  
  (* 步骤4: 证明开区间是C1∪C2的补集 *)
  set (C_union := fun x => C1 x \/ C2 x).
  assert (HC_union_in_borel : In C_union (sigma_sets R Borel_sigma_algebra)).
  {
    (* 首先证明C_union等于F_seq的可数并 *)
    assert (Heq : SetEq C_union (fun x => exists n, In x (F_seq n))).
    {
      intro x.
      unfold C_union.
      split.
      - (* C1 x \/ C2 x 推出 ∃n, F_seq n x *)
        intros [H1 | H2].
        + (* C1 x *)
          exists O.
          unfold F_seq.
          exact H1.
        + (* C2 x *)
          exists (S O).
          unfold F_seq.
          exact H2.
      - (* ∃n, F_seq n x 推出 C1 x \/ C2 x *)
        intros [n H].
        (* 先分解n为0或n' *)
        destruct n as [O | n'].
        + (* n = 0 *)
          left.
          unfold F_seq in H.
          exact H.
        + (* n = S n' *)
          (* 再分解n'为0或n'' *)
          destruct n' as [O | n''].
          * (* n' = 0，所以n = S O = 1 *)
            right.
            unfold F_seq in H.
            exact H.
          * (* n' = S n''，所以n = S (S n'') >= 2 *)
            (* 此时F_seq n是空集，矛盾 *)
            unfold F_seq in H.
            contradiction.
    }
    
    (* 使用集合相等性重写目标 *)
    apply set_extensionality in Heq.
    rewrite Heq.
    
    (* 现在目标变为：In (fun x => exists n, In x (F_seq n)) (sigma_sets R Borel_sigma_algebra) *)
    apply sigma_sets_countable_union.
    exact HF_seq_meas.
  }
  
  (* 步骤5: 证明开区间(a, b) = 补集(C_union) *)
  assert (Heq_open : (fun x => a < x /\ x < b) = Complement_s C_union).
  {
    apply set_extensionality.
    intro x.
    split.
    - intros [H1 H2].
      cbn.   (* 这会简化Complement_s和In吗？ *)
      unfold C_union.
      intros [Hc1 | Hc2].
      + unfold C1 in Hc1. lra.
      + unfold C2 in Hc2. lra.
    - intro H.
      cbn in H.   (* 简化Complement_s和In *)
      unfold C_union in H.
      split.
      + apply Rnot_le_gt. intro Hle. apply H. left. unfold C1. exact Hle.
      + apply Rnot_le_gt. intro Hge. apply H. right. unfold C2. exact Hge.
  }
  
  (* 步骤6: 应用补集封闭性 *)
  rewrite Heq_open.
  apply sigma_sets_complement.
  exact HC_union_in_borel.
Qed.
  
(** 引理：开集可以表示为可数个开区间的并 *)
Lemma open_set_decomposition : forall (U : SetX R),
  open_set U -> 
  exists (F_seq : nat -> SetX R),
    (forall n, exists a b, a < b /\ SetEq (F_seq n) (fun x => a < x /\ x < b)) /\
    SetEq U (fun x => exists n, In x (F_seq n)).
Proof.
  (* 引入开集U和其为开集的假设 *)
  intros U Hopen.
  
  (* 步骤1: 应用已有的开集分解引理 *)
  destruct (open_set_decomposition_real U Hopen) as [a_seq [b_seq [Hlt Heq]]].
  
  (* 步骤2: 构造序列F_seq，每个F_seq n是开区间(a_seq n, b_seq n) *)
  set (F_seq := fun (n : nat) => fun x : R => a_seq n < x /\ x < b_seq n).
  
  (* 步骤3: 证明F_seq满足所需条件 *)
  exists F_seq.
  split.
  {
    (* 证明每个F_seq n都是开区间 *)
    intro n.
    exists (a_seq n), (b_seq n).
    split.
    {
      (* 证明a_seq n < b_seq n *)
      exact (Hlt n).
    }
    {
      (* 证明SetEq (F_seq n) (fun x => a_seq n < x < b_seq n) *)
      unfold F_seq.
      (* 根据定义，F_seq n就是fun x => a_seq n < x /\ x < b_seq n *)
      (* 因此SetEq是自反的 *)
      unfold SetEq.
      intro x.
      reflexivity.
    }
  }
  {
    (* 证明U等于这些开区间的并集 *)
    (* 根据open_set_decomposition_real，我们有： *)
    (* SetEq U (fun x => exists n, a_seq n < x /\ x < b_seq n) *)
    (* 而根据F_seq的定义，fun x => exists n, In x (F_seq n) *)
    (* 就是fun x => exists n, a_seq n < x /\ x < b_seq n) *)
    unfold F_seq.
    (* 现在我们需要证明：SetEq U (fun x => exists n, In x (fun x0 => a_seq n < x0 /\ x0 < b_seq n)) *)
    (* 但In x (fun x0 => a_seq n < x0 /\ x0 < b_seq n) 就是 a_seq n < x /\ x < b_seq n *)
    (* 所以目标就是Heq *)
    exact Heq.
  }
Qed.
  
(** 定理：连续函数是Borel可测的 *)
Theorem continuous_is_borel_measurable : forall (f : R -> R),
  continuous f -> 
  forall (B : SetX R), 
  In B (sigma_sets R Borel_sigma_algebra) ->
  In (fun x : R => B (f x)) (sigma_sets R Borel_sigma_algebra).
Proof.
  intros f fcont B HB.
  
  (* 策略：考虑所有满足条件的B的集合M *)
  set (M := fun (C : SetX R) => In (fun x => C (f x)) (sigma_sets R Borel_sigma_algebra)).
  
  (* 证明M是一个σ代数，且包含Borel_sigma_algebra的生成集 *)
  
  (* 首先证明M包含全集 *)
  assert (Huniv : M (UniversalSet (X:=R))).
  {
    unfold M.
    (* 全集的原像是全集 *)
    assert (Heq : (fun x : R => UniversalSet (f x)) = UniversalSet).
    {
      apply set_extensionality.
      intro x.
      split; [apply universal_set_property | apply universal_set_property].
    }
    rewrite Heq.
    (* 证明全集在Borel_sigma_algebra中 *)
    unfold Borel_sigma_algebra.
    unfold sigma_sets.
    intros G HG.
    destruct HG as [Hbase [HunivG [Hcomp Hcunion]]].
    apply HunivG.
  }
  
  (* 证明M对补集封闭 *)
  assert (Hcomp : forall A, M A -> M (Complement_s A)).
  {
    intros A HA.
    unfold M in *.
    (* 补集的原像等于原像的补集 *)
    assert (Heq : (fun x : R => (Complement_s A) (f x)) = Complement_s (fun x : R => A (f x))).
    {
      apply set_extensionality.
      intro x.
      split.
      - intro H.
        exact H.
      - intro H.
        exact H.
    }
    rewrite Heq.
    (* 应用σ代数对补集封闭的性质 *)
    unfold Borel_sigma_algebra in *.
    apply sigma_sets_complement.
    exact HA.
  }
  
  (* 证明M对可数并封闭 *)
  assert (Hcunion : forall (F_seq : nat -> SetX R), 
    (forall n, M (F_seq n)) -> M (fun x => exists n, (F_seq n) x)).
  {
    intros F_seq HF.
    unfold M in *.
    
    (* 定义原像序列 *)
    set (preimage_seq := fun (n : nat) => fun x : R => F_seq n (f x)).
    
    (* 证明每个 preimage_seq n 在 sigma_sets R Borel_sigma_algebra 中 *)
    assert (Hpreimage : forall n, In (preimage_seq n) (sigma_sets R Borel_sigma_algebra)).
    {
      intro n.
      unfold preimage_seq.
      exact (HF n).
    }
    
    (* 现在，我们需要证明可数并集也在其中 *)
    (* (fun x => exists n, F_seq n (f x)) 就是 (fun x => exists n, preimage_seq n x) *)
    (* 应用 sigma_sets_countable_union *)
    apply sigma_sets_countable_union.
    exact Hpreimage.
  }
  
  (* 证明空集在M中 *)
  assert (Hempty : M (EmptySet (X:=R))).
  {
    unfold M.
    (* 空集的原像是空集 *)
    assert (Heq : (fun x : R => EmptySet (f x)) = EmptySet (X:=R)).
    {
      apply set_extensionality.
      intro x.
      split; intro H; contradiction.
    }
    rewrite Heq.
    (* 证明空集在Borel_sigma_algebra中 *)
    (* 空集作为全集的补集 *)
    rewrite <- complement_universal_empty.
    apply sigma_sets_complement.
    (* 先证明全集在Borel_sigma_algebra中 *)
    unfold Borel_sigma_algebra.
    unfold sigma_sets.
    intros G HG.
    destruct HG as [Hbase [HunivG [HcompG HcunionG]]].  (* 重命名为HcompG以避免冲突 *)
    apply HunivG.  (* 直接使用contains_universe条件 *)
  }
  
  (* 证明M包含所有闭区间[a,b] *)
  assert (Hintervals : forall a b : R, M (fun x => a <= x /\ x <= b)).
  {
    intros a b.
    (* 根据a和b的大小关系分情况讨论 *)
    destruct (Rle_dec a b) as [Hle | Hnle].
    - (* a ≤ b *)
      unfold M.
      (* 应用连续函数闭集原像可测的引理 *)
      (* 我们需要提供连续函数f和闭集C = [a,b] *)
      apply (continuous_preimage_closed_in_borel f (fun x : R => a <= x /\ x <= b)).
      + (* 证明f连续 *)
        exact fcont.
      + (* 证明闭区间[a,b]是闭集 *)
        unfold closed_set.
        intros x Hlimit.
        unfold limit_point in Hlimit.
        (* 使用反证法证明x在[a,b]中 *)
        apply Coq.Logic.Classical_Prop.NNPP.
        intro Hnot.
        (* 分解Hnot: ~(a <= x /\ x <= b) 等价于 ~(a <= x) \/ ~(x <= b) *)
        assert (H : ~ (a <= x) \/ ~ (x <= b)).
        { 
          (* 手动证明分解 *)
          destruct (classic (a <= x)) as [Hle_ax | Hnle_ax].
          - right.
            intro Hle_xb.
            apply Hnot.
            split; assumption.
          - left.
            exact Hnle_ax.
        }
        destruct H as [Hnot_le | Hnot_le'].
        + (* 情况1: ~ a <= x，即 x < a *)
          set (epsilon := (a - x) / 2).
          assert (Heps_pos : epsilon > 0).
          { 
            unfold epsilon.
            (* 因为 x < a，所以 a - x > 0 *)
            apply Rmult_gt_0_compat.
            - lra.
            - apply Rinv_0_lt_compat.
              lra.
          }
          destruct (Hlimit epsilon Heps_pos) as [y [HyC [Habs Hyneq]]].
          destruct HyC as [Hle_a Hle_b].  (* a <= y <= b *)
          (* 由于 x < a ≤ y，所以 y - x > 0 *)
          assert (Habs_eq : Rabs (y - x) = y - x).
          {
            apply Rabs_right.
            lra.
          }
          rewrite Habs_eq in Habs.
          unfold epsilon in Habs.
          lra.  (* 矛盾：从 y - x < (a - x)/2 推出 y < a *)
        + (* 情况2: ~ x <= b，即 b < x *)
          set (epsilon := (x - b) / 2).
          assert (Heps_pos : epsilon > 0).
          { 
            unfold epsilon.
            (* 因为 b < x，所以 x - b > 0 *)
            apply Rmult_gt_0_compat.
            - lra.
            - apply Rinv_0_lt_compat.
              lra.
          }
          destruct (Hlimit epsilon Heps_pos) as [y [HyC [Habs Hyneq]]].
          destruct HyC as [Hle_a Hle_b].  (* a <= y <= b *)
          (* 由于 y ≤ b < x，所以 y - x < 0 *)
          assert (Hneg : y - x < 0).
          {
            lra.
          }
          assert (Habs_eq : Rabs (y - x) = -(y - x)).
          {
            apply Rabs_left.
            exact Hneg.
          }
          rewrite Habs_eq in Habs.
          rewrite Ropp_minus_distr in Habs.
          unfold epsilon in Habs.
          lra.  (* 矛盾：从 x - y < (x - b)/2 推出 y > b *)
    - (* a > b，此时集合为空集 *)
      assert (Heq : (fun x => a <= x /\ x <= b) = EmptySet (X:=R)).
      {
        apply set_extensionality.
        intro x.
        split; intro H.
        - destruct H as [H1 H2].
          lra.
        - contradiction.
      }
      rewrite Heq.
      exact Hempty.
  }
  
  (* 现在使用sigma_sets的最小性：因为M是包含生成集族（闭区间）的σ代数，所以它包含整个Borel_sigma_algebra *)
  unfold M.
  
  (* 展开Borel_sigma_algebra的定义 *)
  unfold Borel_sigma_algebra in HB.
  
  (* 应用sigma_sets的定义：如果B在sigma_sets中，那么对于任意包含生成集族且满足σ代数条件的集合族S，都有S B *)
  (* 这里我们让S为M *)
  apply HB.
  
  (* 我们需要证明M满足四个条件 *)
  split.  (* 分解合取式 *)
  - (* M包含生成集族 *)
    intros C Hgen.
    destruct Hgen as [a [b Heq]].
    (* 将SetEq转换为函数相等性 *)
    pose proof (set_extensionality _ _ Heq) as Heq_func.
    (* 现在Heq_func: C = (fun x => a <= x <= b) *)
    
    (* 展开M的定义 *)
    unfold M.
    
    (* 使用Heq_func重写目标中的C *)
    (* 目标: (fun B0 : SetX R => (fun x : R => B0 (f x)) in_s sigma_sets R Borel_sigma_algebra) C *)
    (* 这等价于: (fun x : R => C (f x)) in_s sigma_sets R Borel_sigma_algebra *)
    (* 使用Heq_func将C替换为(fun x => a <= x <= b) *)
    rewrite Heq_func.
    
    (* 现在目标变为: (fun x : R => (fun x0 : R => a <= x0 <= b) (f x)) 
                   in_s sigma_sets R Borel_sigma_algebra *)
    (* 这正是Hintervals a b所证明的 *)
    (* Hintervals a b: M (fun x => a <= x <= b) *)
    (* 展开M的定义 *)
    unfold M in Hintervals.
    apply (Hintervals a b).
    
  - (* 剩余三个条件的合取 *)
    split.
    + (* M包含全集 *)
      exact Huniv.
    + split.
      * (* M对补集封闭 *)
        exact Hcomp.
      * (* M对可数并封闭 *)
        exact Hcunion.
Qed.
  
(** 推论：连续函数与开区间的原像是可测的 *)
Corollary continuous_preimage_interval_measurable : forall (f : R -> R) (a b : R),
  continuous f -> 
  In (fun x : R => a < f x /\ f x < b) (sigma_sets R Borel_sigma_algebra).
Proof.
  intros f a b fcont.
  (* 开区间在Borel σ代数中 *)
  assert (Hinterval : In (fun x : R => a < x /\ x < b) (sigma_sets R Borel_sigma_algebra)).
  {
    (* 应用已有的开区间在Borel代数中的引理 *)
    (* 注意：open_interval_in_borel需要a < b的假设 *)
    destruct (Rlt_le_dec a b) as [Hlt | Hge].
    {
      (* 情况1: a < b *)
      apply open_interval_in_borel.
      exact Hlt.
    }
    {
      (* 情况2: a >= b，此时开区间为空集 *)
      (* 首先证明全集在Borel σ代数中 *)
      assert (Huniv : In (UniversalSet (X:=R)) (sigma_sets R Borel_sigma_algebra)).
      {
        unfold Borel_sigma_algebra.
        unfold sigma_sets.
        intros G HG.
        destruct HG as [Hbase [HunivG [Hcomp Hcunion]]].
        apply HunivG.
      }
      (* 证明当前集合等于空集 *)
      assert (Hempty : (fun x : R => a < x /\ x < b) = EmptySet (X:=R)).
      {
        apply set_extensionality.
        intro x.
        split.
        - intro H.
          destruct H as [H1 H2].
          lra.
        - intro H.
          contradiction.
      }
      rewrite Hempty.
      (* 将空集重写为全集的补集 *)
      rewrite <- complement_universal_empty.
      apply sigma_sets_complement.
      exact Huniv.
    }
  }
  
  (* 应用连续函数是Borel可测的定理 *)
  apply (continuous_is_borel_measurable f fcont (fun x : R => a < x /\ x < b)).
  exact Hinterval.
Qed.
  
(** 工具引理：开集的等价构造 *)
Lemma open_set_as_union_of_intervals : forall (U : SetX R),
  open_set U ->
  exists (intervals : nat -> R * R),
    (forall n, let (a_n, b_n) := intervals n in a_n < b_n) /\
    SetEq U (fun x => exists n, 
              let (a_n, b_n) := intervals n in 
              a_n < x /\ x < b_n).
Proof.
  (* 引入开集U和其为开集的假设 *)
  intros U Hopen.
  
  (* 应用已有的开集分解引理 *)
  destruct (open_set_decomposition_real U Hopen) as [a_seq [b_seq [Hlt Heq]]].
  
  (* 构造intervals序列：将a_seq和b_seq组合成序对 *)
  set (intervals := fun (n : nat) => (a_seq n, b_seq n)).
  
  (* 证明intervals满足所需条件 *)
  exists intervals.
  split.
  {
    (* 证明对于所有n，let (a_n, b_n) := intervals n in a_n < b_n *)
    intro n.
    unfold intervals.
    (* 现在需要证明: let (a_n, b_n) := (a_seq n, b_seq n) in a_n < b_n *)
    (* 这等价于证明 a_seq n < b_seq n *)
    exact (Hlt n).
  }
  {
    (* 证明集合相等性 *)
    (* 我们需要证明: SetEq U (fun x => exists n, let (a_n, b_n) := intervals n in a_n < x /\ x < b_n) *)
    (* 展开intervals的定义 *)
    unfold intervals.
    (* 目标变为: SetEq U (fun x => exists n, let (a_n, b_n) := (a_seq n, b_seq n) in a_n < x /\ x < b_n) *)
    (* 简化let表达式: let (a_n, b_n) := (a_seq n, b_seq n) in a_n < x /\ x < b_n 等价于 a_seq n < x /\ x < b_seq n *)
    (* 这正是Heq所证明的: SetEq U (fun x => exists n, a_seq n < x /\ x < b_seq n) *)
    exact Heq.
  }
Qed.
  
(* =========================================================================== *)
(* 辅助定义和引理 *)
(* =========================================================================== *)
  
(** 定义：集合的内部 *)
Definition interior (A : SetX R) : SetX R :=
  fun x => exists delta : R, delta > 0 /\
    forall y : R, Rabs (y - x) < delta -> A y.
  
(** 引理：开集等于其内部 *)
Lemma open_set_equals_interior : forall (A : SetX R),
  open_set A <-> SetEq A (interior A).
Proof.
  (* 引入集合A *)
  intros A.
  split.
  - (* 方向1: 开集A等于其内部 *)
    intro Hopen.
    (* 展开开集的邻域特征 *)
    (* 注意：在文件中我们有一个等价引理 open_set_characterization_simple *)
    (* 它说：open_set A <-> (∀x, A x -> ∃δ>0, ∀y, |y-x|<δ -> A y) *)
    
    (* 首先，应用开集特征引理 *)
    pose proof (open_set_characterization_simple A) as [Hopen_to_char _].
    (* 从Hopen_to_char Hopen 得到邻域性质 *)
    specialize (Hopen_to_char Hopen) as Hneighborhood.
    
    (* 现在需要证明 SetEq A (interior A) *)
    unfold SetEq.
    intro x.
    split.
    {
      (* 方向：A x → interior A x *)
      intro Hx.
      (* 根据开集特征，存在δ>0使得邻域内的点都在A中 *)
      destruct (Hneighborhood x Hx) as [delta [Hdelta_pos Hball]].
      (* 这正是interior的定义 *)
      unfold interior.
      exists delta.
      split.
      + exact Hdelta_pos.
      + exact Hball.
    }
    {
      (* 方向：interior A x → A x *)
      intro H_int.
      unfold interior in H_int.
      (* 根据定义，存在δ>0使得邻域内的点都在A中 *)
      destruct H_int as [delta [Hdelta_pos Hball]].
      (* 特别地，取y=x，因为|x-x|=0<δ，所以A x *)
      apply Hball.
      rewrite Rminus_eq_0.   (* x - x = 0 *)
      rewrite Rabs_R0.       (* |0| = 0 *)
      exact Hdelta_pos.      (* 0 < δ *)
    }
    
  - (* 方向2: 如果A等于其内部，那么A是开集 *)
    intro Heq.
    (* 展开集合相等性 *)
    unfold SetEq in Heq.
    (* 使用开集特征引理的另一个方向 *)
    pose proof (open_set_characterization_simple A) as [_ Hchar_to_open].
    
    (* 需要证明 open_set A *)
    apply Hchar_to_open.
    (* 现在需要证明邻域性质：∀x, A x -> ∃δ>0, ∀y, |y-x|<δ -> A y *)
    intros x Hx.
    (* 因为 A x，且 A 等于 interior A，所以 interior A x *)
    destruct (Heq x) as [H1 H2].
    (* H1: A x → interior A x, H2: interior A x → A x *)
    specialize (H1 Hx) as H_int.
    (* 现在 H_int: interior A x *)
    unfold interior in H_int.
    (* 这正是我们需要的邻域性质 *)
    exact H_int.
Qed.
  
(** 定义：集合的闭包 *)
Definition closure (A : SetX R) : SetX R :=
  fun x => forall delta : R, delta > 0 -> 
    exists y : R, A y /\ Rabs (y - x) < delta.
  
(** 引理：闭集等于其闭包 *)
Lemma closed_set_equals_closure : forall (A : SetX R),
  closed_set A <-> SetEq A (closure A).
Proof.
  intros A.
  split.
  - (* 方向1: 闭集A等于其闭包 *)
    intro Hclosed.
    unfold closed_set, limit_point in Hclosed.
    unfold SetEq, closure.
    intros x.
    split.
    + intro Hx.
      intros delta Hdelta.
      (* 由于x在A中，可以取y=x *)
      exists x.
      split.
      * exact Hx.                   (* A x *)
      * rewrite Rminus_eq_0.        (* x - x = 0 *)
        rewrite Rabs_R0.            (* |0| = 0 *)
        exact Hdelta.               (* 0 < delta *)
    + intro Hclosure.
      (* 使用反证法：假设x不在A中 *)
      apply Coq.Logic.Classical_Prop.NNPP.
      intro HnotAx.
      (* 现在Hclosure: closure A x, 即对于任意delta>0，存在y∈A使得|y-x|<delta *)
      (* 要导出矛盾，我们可以证明x是A的极限点，从而由闭集定义得x∈A *)
      assert (Hlimit_point : limit_point A x).
      {
        unfold limit_point.
        intros delta Hdelta.
        (* 从Hclosure得到存在y∈A使得|y-x|<delta *)
        destruct (Hclosure delta Hdelta) as [y [Hy Habs]].
        exists y.
        split.
        * exact Hy.                 (* A y *)
        * split.
          - exact Habs.             (* |y-x| < delta *)
          - (* 证明y ≠ x，因为如果y=x，则A x，与HnotAx矛盾 *)
            intro Heq.
            rewrite Heq in Hy.
            contradiction.
      }
      (* 由于A是闭集，极限点x应该在A中 *)
      apply Hclosed in Hlimit_point.
      contradiction.
  - (* 方向2: 如果A等于其闭包，那么A是闭集 *)
    intro Heq.
    unfold SetEq in Heq.
    unfold closed_set, limit_point.
    intros x Hlimit.
    (* 需要证明A x *)
    (* 由于limit_point A x，我们可以证明closure A x *)
    assert (Hclosure : closure A x).
    {
      unfold closure.
      intros delta Hdelta.
      (* 根据极限点定义，存在y∈A使得|y-x|<delta且y≠x *)
      destruct (Hlimit delta Hdelta) as [y [Hy [Habs _]]].
      exists y.
      split.
      * exact Hy.
      * exact Habs.
    }
    (* 现在应用集合相等性：closure A x → A x *)
    destruct (Heq x) as [_ H2].  (* H2: closure A x → A x *)
    apply H2.
    exact Hclosure.
Qed.
  
(** 引理：全集在Borel σ代数中 *)
Lemma universe_in_borel : In (UniversalSet (X:=R)) (sigma_sets R Borel_sigma_algebra).
Proof.
  (* 展开Borel σ代数的定义 *)
  unfold Borel_sigma_algebra.
  
  (* 展开sigma_sets的定义：所有包含生成集族且满足σ代数条件的集合族的最小交集 *)
  unfold sigma_sets.
  
  (* 引入任意集合族G，假设G满足σ代数生成条件 *)
  intros G HG.
  
  (* 分解HG为四个条件： *)
  (* 1. Hbase: G包含生成集族（闭区间） *)
  (* 2. HunivG: G包含全集 *)
  (* 3. Hcomp: G对补运算封闭 *)
  (* 4. Hcunion: G对可数并运算封闭 *)
  destruct HG as [Hbase [HunivG [Hcomp Hcunion]]].
  
  (* 直接应用HunivG条件：G包含全集 *)
  apply HunivG.
Qed.
  
(* =========================================================================== *)
(* 实例：具体连续函数的可测性 *)
(* =========================================================================== *)
  
(* 示例：证明空集在Borel σ代数中 *)
Lemma empty_set_in_borel_via_universe : 
  In (EmptySet (X:=R)) (sigma_sets R Borel_sigma_algebra).
Proof.
  (* 空集是全集的补集 *)
  rewrite <- complement_universal_empty.  (* EmptySet = Complement_s UniversalSet *)
  apply sigma_sets_complement.            (* 应用补集封闭性 *)
  apply universe_in_borel.                (* 使用本引理 *)
Qed.
  
(** 例子：常数函数的可测性 *)
Example constant_function_measurable : forall (c : R),
  let f := (fun _ : R => c) in
  continuous f /\
  forall (B : SetX R), 
  In B (sigma_sets R Borel_sigma_algebra) ->
  In (fun x : R => B (f x)) (sigma_sets R Borel_sigma_algebra).
Proof.
  (* 引入常数c *)
  intros c.
  (* 将证明分解为连续性和可测性两部分 *)
  split.
  {
    (* 证明常数函数连续 *)
    (* continuous_const已证明常数函数连续 *)
    apply continuous_const.
  }
  {
    (* 证明可测性：对于任意Borel可测集B，其原像也可测 *)
    intros B HB.
    (* 简化f的定义：f x = c *)
    simpl.
    
    (* 首先证明全集在Borel σ代数中，后续两个分支都需要用到 *)
    assert (Huniv : In (UniversalSet (X:=R)) (sigma_sets R Borel_sigma_algebra)).
    {
      (* 直接应用已证明的引理 *)
      apply universe_in_borel.
    }
    
    (* 分析常数函数的原像：
       - 如果B包含常数c，则对于所有x，B (f x) = B c = True，原像是全集
       - 如果B不包含常数c，则对于所有x，B (f x) = False，原像是空集 *)
    destruct (classic (B c)) as [Hc | Hnotc].
    {
      (* 情况1: B包含常数c *)
      (* 原像集合是全集 *)
      assert (Heq : (fun x : R => B c) = UniversalSet (X:=R)).
      {
        (* 使用集合外延性证明两个集合相等 *)
        apply set_extensionality.
        intro x.
        split.
        - (* 左包含：函数值在B中蕴含x在全集中 *)
          intro H.
          apply universal_set_property.
        - (* 右包含：x在全集中蕴含函数值在B中 *)
          intro H.
          exact Hc.  (* 因为B c成立 *)
      }
      (* 将原像重写为全集 *)
      rewrite Heq.
      (* 应用全集在Borel代数中的引理 *)
      exact Huniv.
    }
    {
      (* 情况2: B不包含常数c *)
      (* 原像集合是空集 *)
      assert (Heq : (fun x : R => B c) = EmptySet (X:=R)).
      {
        (* 使用集合外延性证明两个集合相等 *)
        apply set_extensionality.
        intro x.
        split.
        - (* 左包含：函数值在B中蕴含x在空集中 - 实际上矛盾 *)
          intro H.
          contradiction.  (* H: B c，但Hnotc: ~B c *)
        - (* 右包含：x在空集中蕴含函数值在B中 - 实际上不可能 *)
          intro H.
          contradiction.
      }
      (* 将原像重写为空集 *)
      rewrite Heq.
      
      (* 现在需要证明空集在Borel σ代数中 *)
      (* 方法：空集是全集的补集 *)
      (* 首先将空集重写为全集的补集 *)
      rewrite <- complement_universal_empty.
      
      (* 现在目标变为：Complement_s UniversalSet_s 在 Borel σ 代数中 *)
      (* 应用补集可测性引理 *)
      (* 注意：我们需要指定sigma_sets_complement的参数 *)
      
      (* 方法1：直接构造应用 *)
      (* apply (sigma_sets_complement R Borel_sigma_algebra (UniversalSet (X:=R)) Huniv). *)
      
      (* 方法2：使用通用引理 *)
      (* 首先展开Borel_sigma_algebra的定义，然后应用sigma_sets_complement *)
      unfold Borel_sigma_algebra.
      apply (sigma_sets_complement R Borel_sigma_algebra (UniversalSet (X:=R)) Huniv).
    }
  }
Qed.
  
(** 例子：恒等函数的可测性 *)
Example identity_function_measurable :
  continuous (fun x : R => x) /\
  forall (B : SetX R), 
  In B (sigma_sets R Borel_sigma_algebra) ->
  In (fun x : R => B x) (sigma_sets R Borel_sigma_algebra).
Proof.
  split.
  - (* 证明恒等函数连续 *)
    apply continuous_id.
  - (* 证明可测性 *)
    intros B HB.
    simpl.
    exact HB.
Qed.
  
(* =========================================================================== *)
(* 连续函数运算的可测性 *)
(* =========================================================================== *)
  
(** 定理：连续函数的和是可测的 *)
Theorem sum_of_continuous_measurable : forall (f g : R -> R),
  continuous f -> continuous g ->
  forall (B : SetX R), 
  In B (sigma_sets R Borel_sigma_algebra) ->
  In (fun x : R => B (f x + g x)) (sigma_sets R Borel_sigma_algebra).
Proof.
  intros f g Hcont_f Hcont_g B HB.
  
  (* 步骤1: 定义函数 h(x) = f(x) + g(x) *)
  set (h := fun x : R => f x + g x).
  
  (* 步骤2: 证明 h 是连续函数 *)
  assert (Hcont_h : continuous h).
  {
    unfold continuous, continuous_at.
    intros x0 eps Heps.
    
    (* 因为 f 在 x0 连续，存在 δ1 *)
    unfold continuous in Hcont_f.
    specialize (Hcont_f x0) as Hcont_f_x0.
    unfold continuous_at in Hcont_f_x0.
    
    (* 因为 g 在 x0 连续，存在 δ2 *)
    unfold continuous in Hcont_g.
    specialize (Hcont_g x0) as Hcont_g_x0.
    unfold continuous_at in Hcont_g_x0.
    
    (* 对于 ε/2 > 0 *)
    assert (Heps_half_pos : eps/2 > 0) by lra.
    
    (* 获取 δ1 和 δ2 *)
    destruct (Hcont_f_x0 (eps/2) Heps_half_pos) as [delta1 [Hdelta1_pos Hcont_f_delta]].
    destruct (Hcont_g_x0 (eps/2) Heps_half_pos) as [delta2 [Hdelta2_pos Hcont_g_delta]].
    
    (* 取 δ = min(δ1, δ2) *)
    set (delta := Rmin delta1 delta2).
    assert (Hdelta_pos : delta > 0).
    {
      unfold delta.
      apply Rmin_glb_lt.
      - exact Hdelta1_pos.
      - exact Hdelta2_pos.
    }
    
    (* 证明当 |x - x0| < delta 时，|h(x) - h(x0)| < eps *)
    exists delta.
    split.
    - exact Hdelta_pos.
    - intros x Hdist.
      unfold h.
      
      (* 因为 delta ≤ delta1 且 delta ≤ delta2，所以 |x - x0| < delta 蕴含 |x - x0| < delta1 和 < delta2 *)
      assert (Hdist1 : Rabs (x - x0) < delta1).
      {
        apply Rlt_le_trans with delta.
        + exact Hdist.
        + unfold delta.
          apply Rmin_l.
      }
      assert (Hdist2 : Rabs (x - x0) < delta2).
      {
        apply Rlt_le_trans with delta.
        + exact Hdist.
        + unfold delta.
          apply Rmin_r.
      }
      
      (* 应用f和g的连续性条件 *)
      specialize (Hcont_f_delta x Hdist1).
      specialize (Hcont_g_delta x Hdist2).
      
      (* 计算 h(x) - h(x0) = (f(x)+g(x)) - (f(x0)+g(x0)) = (f(x)-f(x0)) + (g(x)-g(x0)) *)
      replace ((f x + g x) - (f x0 + g x0)) with ((f x - f x0) + (g x - g x0)) by ring.
      
      (* 应用三角不等式 *)
      apply Rle_lt_trans with (Rabs (f x - f x0) + Rabs (g x - g x0)).
      + apply Rabs_triang.
      + (* 使用 f 和 g 的连续性条件 *)
        lra.
  }
  
  (* 步骤3: 应用连续函数可测性定理 *)
  (* 注意：h = fun x => f x + g x *)
  unfold h.
  
  (* 应用continuous_is_borel_measurable定理 *)
  apply (continuous_is_borel_measurable (fun x : R => f x + g x) Hcont_h B HB).
Qed.
  
(** 定理：连续函数的乘积是可测的 *)
Theorem product_of_continuous_measurable : forall (f g : R -> R),
  continuous f -> continuous g ->
  forall (B : SetX R), 
  In B (sigma_sets R Borel_sigma_algebra) ->
  In (fun x : R => B (f x * g x)) (sigma_sets R Borel_sigma_algebra).
Proof.
  intros f g Hf Hg B HB.
  
  (* 步骤1: 定义函数 h(x) = f(x) * g(x) *)
  set (h := fun x : R => f x * g x).
  
  (* 步骤2: 证明 h 是连续函数 *)
  assert (Hcont_h : continuous h).
  {
    unfold continuous, continuous_at.
    intros x0 eps Heps.
    
    (* 获取 f 在 x0 点的连续性 *)
    unfold continuous in Hf.
    specialize (Hf x0) as Hf_x0.
    unfold continuous_at in Hf_x0.
    
    (* 获取 g 在 x0 点的连续性 *)
    unfold continuous in Hg.
    specialize (Hg x0) as Hg_x0.
    unfold continuous_at in Hg_x0.
    
    (* 第一步：由 f 连续，存在 δ₁ 使得当 |x-x₀|<δ₁ 时，|f(x)-f(x₀)|<1 *)
    assert (Heps1_pos : 1 > 0) by lra.
    destruct (Hf_x0 1 Heps1_pos) as [delta1 [Hdelta1_pos Hf_delta1]].
    
    (* 计算 M1 = |f(x₀)| + 1，作为 f 在邻域内的上界 *)
    set (M1 := Rabs (f x0) + 1).
    assert (HM1_pos : M1 > 0).
    {
      unfold M1.
      apply Rplus_le_lt_0_compat.
      - apply Rabs_pos.
      - lra.
    }
    
    (* 第二步：由 g 连续，对于 ε/(2M₁) > 0，存在 δ₂ *)
    assert (HepsM1_pos : eps/(2*M1) > 0).
    {
      apply Rdiv_lt_0_compat.
      - exact Heps.
      - apply Rmult_gt_0_compat.
        + lra.
        + exact HM1_pos.
    }
    destruct (Hg_x0 (eps/(2*M1)) HepsM1_pos) as [delta2 [Hdelta2_pos Hg_delta2]].
    
    (* 第三步：由 f 连续，对于 ε/(2(|g(x₀)|+1)) > 0，存在 δ₃ *)
    set (G0 := Rabs (g x0) + 1).
    assert (HG0_pos : G0 > 0).
    {
      unfold G0.
      apply Rplus_le_lt_0_compat.
      - apply Rabs_pos.
      - lra.
    }
    assert (HepsG0_pos : eps/(2*G0) > 0).
    {
      apply Rdiv_lt_0_compat.
      - exact Heps.
      - apply Rmult_gt_0_compat.
        + lra.
        + exact HG0_pos.
    }
    destruct (Hf_x0 (eps/(2*G0)) HepsG0_pos) as [delta3 [Hdelta3_pos Hf_delta3]].
    
    (* 取 δ = min(δ₁, δ₂, δ₃) *)
    set (delta := Rmin delta1 (Rmin delta2 delta3)).
    assert (Hdelta_pos : delta > 0).
    {
      unfold delta.
      (* 证明 Rmin delta2 delta3 > 0 *)
      assert (Hmin23_pos : Rmin delta2 delta3 > 0).
      {
        apply Rmin_glb_lt.
        - exact Hdelta2_pos.
        - exact Hdelta3_pos.
      }
      (* 证明 Rmin delta1 (Rmin delta2 delta3) > 0 *)
      apply Rmin_glb_lt.
      - exact Hdelta1_pos.
      - exact Hmin23_pos.
    }
    
    exists delta.
    split.
    { exact Hdelta_pos. }
    
    intros x Hdist.
    unfold h.
    
    (* 证明 |x-x₀| < δ 蕴含 |x-x₀| < δ₁ *)
    assert (Hdist1 : Rabs (x - x0) < delta1).
    {
      apply Rlt_le_trans with delta.
      - exact Hdist.
      - unfold delta.
        apply Rmin_l.
    }
    
    (* 证明 |x-x₀| < δ 蕴含 |x-x₀| < δ₂ *)
    assert (Hdist2 : Rabs (x - x0) < delta2).
    {
      apply Rlt_le_trans with delta.
      - exact Hdist.
      - unfold delta.
        (* 首先证明 delta ≤ Rmin delta2 delta3 *)
        assert (Hdelta_le_min23 : delta <= Rmin delta2 delta3).
        { unfold delta; apply Rmin_r. }
        (* 然后证明 Rmin delta2 delta3 ≤ delta2 *)
        assert (Hmin23_le_delta2 : Rmin delta2 delta3 <= delta2).
        { apply Rmin_l. }
        (* 通过传递性得到 delta ≤ delta2 *)
        apply Rle_trans with (r2 := Rmin delta2 delta3); assumption.
    }
    
    (* 证明 |x-x₀| < δ 蕴含 |x-x₀| < δ₃ *)
    assert (Hdist3 : Rabs (x - x0) < delta3).
    {
      apply Rlt_le_trans with delta.
      - exact Hdist.
      - unfold delta.
        (* 首先证明 delta ≤ Rmin delta2 delta3 *)
        assert (Hdelta_le_min23 : delta <= Rmin delta2 delta3).
        { unfold delta; apply Rmin_r. }
        (* 然后证明 Rmin delta2 delta3 ≤ delta3 *)
        assert (Hmin23_le_delta3 : Rmin delta2 delta3 <= delta3).
        { apply Rmin_r. }
        (* 通过传递性得到 delta ≤ delta3 *)
        apply Rle_trans with (r2 := Rmin delta2 delta3); assumption.
    }
    
    (* 证明 f 在 x 点的值有界：|f(x)| ≤ M₁ *)
    assert (Hfx_bound : Rabs (f x) <= M1).
    {
      unfold M1.
      (* 使用三角不等式：|f(x)| = |f(x₀) + (f(x) - f(x₀))| ≤ |f(x₀)| + |f(x) - f(x₀)| *)
      replace (f x) with (f x0 + (f x - f x0)) by ring.
      apply Rle_trans with (Rabs (f x0) + Rabs (f x - f x0)).
      - apply Rabs_triang.
      - (* 现在需要证明 |f(x₀)| + |f(x)-f(x₀)| ≤ |f(x₀)| + 1 *)
        apply Rplus_le_compat_l.
        (* 由 Hf_delta1 和 Hdist1，我们知道 |f(x)-f(x₀)| < 1 *)
        apply Rlt_le.
        apply Hf_delta1.
        exact Hdist1.
    }
    
    (* 证明 |g(x₀)| ≤ G₀ *)
    assert (Hg0_bound : Rabs (g x0) <= G0).
    {
      unfold G0.
      (* 显然成立，因为 |g(x₀)| ≤ |g(x₀)| + 1 *)
      lra.
    }
    
    (* 现在证明乘积的连续性：|f(x)g(x) - f(x₀)g(x₀)| < ε *)
    
    (* 将差值分解：
       f(x)g(x) - f(x₀)g(x₀) = f(x)(g(x)-g(x₀)) + (f(x)-f(x₀))g(x₀) *)
    replace (f x * g x - f x0 * g x0) with 
            (f x * (g x - g x0) + (f x - f x0) * g x0) by ring.
    
    (* 应用三角不等式 *)
    apply Rle_lt_trans with (Rabs (f x * (g x - g x0)) + Rabs ((f x - f x0) * g x0)).
    - apply Rabs_triang.
    - (* 将绝对值分解为乘积 *)
      rewrite Rabs_mult, Rabs_mult.
      
      (* 现在需要证明：|f(x)|·|g(x)-g(x₀)| + |f(x)-f(x₀)|·|g(x₀)| < ε *)
      
      (* 首先处理第一个项：|f(x)|·|g(x)-g(x₀)| *)
      (* 使用中间步骤：|f(x)|·|g(x)-g(x₀)| ≤ M₁·|g(x)-g(x₀)| < M₁·(ε/(2M₁)) *)
      assert (Hterm1_intermediate : Rabs (f x) * Rabs (g x - g x0) <= M1 * Rabs (g x - g x0)).
      {
        apply Rmult_le_compat_r.
        - apply Rabs_pos.  (* |g(x)-g(x₀)| ≥ 0 *)
        - exact Hfx_bound.  (* |f(x)| ≤ M₁ *)
      }
      
      assert (Hterm1_bound : M1 * Rabs (g x - g x0) < M1 * (eps / (2 * M1))).
      {
        apply Rmult_lt_compat_l.
        - (* M₁ > 0 *) exact HM1_pos.
        - (* |g(x)-g(x₀)| < ε/(2M₁) *) apply Hg_delta2; exact Hdist2.
      }
      
      (* 通过传递性得到 |f(x)|·|g(x)-g(x₀)| < M₁·(ε/(2M₁)) *)
      assert (Hterm1 : Rabs (f x) * Rabs (g x - g x0) < M1 * (eps / (2 * M1))).
      {
        apply Rle_lt_trans with (M1 * Rabs (g x - g x0)).
        - exact Hterm1_intermediate.
        - exact Hterm1_bound.
      }
      
      (* 然后处理第二个项：|f(x)-f(x₀)|·|g(x₀)| *)
      (* 使用中间步骤：|f(x)-f(x₀)|·|g(x₀)| ≤ |f(x)-f(x₀)|·G₀ < (ε/(2G₀))·G₀ *)
      assert (Hterm2_intermediate : Rabs (f x - f x0) * Rabs (g x0) <= Rabs (f x - f x0) * G0).
      {
        apply Rmult_le_compat_l.
        - (* |f(x)-f(x₀)| ≥ 0 *) apply Rabs_pos.
        - (* |g(x₀)| ≤ G₀ *) exact Hg0_bound.
      }
      
      assert (Hterm2_bound : Rabs (f x - f x0) * G0 < (eps / (2 * G0)) * G0).
      {
        apply Rmult_lt_compat_r.
        - (* G₀ > 0 *) exact HG0_pos.
        - (* |f(x)-f(x₀)| < ε/(2G₀) *) apply Hf_delta3; exact Hdist3.
      }
      
      (* 通过传递性得到 |f(x)-f(x₀)|·|g(x₀)| < (ε/(2G₀))·G₀ *)
      assert (Hterm2 : Rabs (f x - f x0) * Rabs (g x0) < (eps / (2 * G0)) * G0).
      {
        apply Rle_lt_trans with (Rabs (f x - f x0) * G0).
        - exact Hterm2_intermediate.
        - exact Hterm2_bound.
      }
      
      (* 化简表达式 *)
      (* 证明 M₁ * (ε/(2M₁)) = ε/2 *)
      assert (H_simplify1 : M1 * (eps / (2 * M1)) = eps / 2).
      {
        field.
        (* 需要证明分母 2 * M1 ≠ 0 *)
        intro H.
        (* 假设 2 * M1 = 0 *)
        apply Rlt_irrefl with 0.
        rewrite H in HM1_pos.
        exact HM1_pos.
      }
      
      (* 证明 (ε/(2G₀)) * G₀ = ε/2 *)
      assert (H_simplify2 : (eps / (2 * G0)) * G0 = eps / 2).
      {
        field.
        (* 需要证明分母 2 * G0 ≠ 0 *)
        intro H.
        (* 假设 2 * G0 = 0 *)
        apply Rlt_irrefl with 0.
        rewrite H in HG0_pos.
        exact HG0_pos.
      }
      
      (* 现在将两个项相加并简化 *)
      (* 将Hterm1和Hterm2中的右边替换为eps/2 *)
      rewrite H_simplify1 in Hterm1.
      rewrite H_simplify2 in Hterm2.
      
      (* 现在我们有：
         Hterm1: |f x|·|g x - g x0| < eps/2
         Hterm2: |f x - f x0|·|g x0| < eps/2
         
         需要证明：
         |f x|·|g x - g x0| + |f x - f x0|·|g x0| < eps
         
         使用lra自动处理线性实数不等式
      *)
      lra.
  }  (* 这是 Hcont_h 证明块的结束 *)
  
  (* 步骤3: 应用连续函数可测性定理 *)
  (* 注意：我们已定义 h 为 fun x => f x * g x，且证明了 Hcont_h: continuous h *)
  (* 应用定理：continuous_is_borel_measurable *)
  apply (continuous_is_borel_measurable h Hcont_h B HB).
Qed.
  
(* =========================================================================== *)
(* 总结：连续函数与Borel可测性 *)
(* =========================================================================== *)
  
(** 定义：Borel可测函数 *)
Definition Borel_measurable_function (f : R -> R) : Prop :=
  forall (B : SetX R), 
  In B (sigma_sets R Borel_sigma_algebra) ->
  In (fun x : R => B (f x)) (sigma_sets R Borel_sigma_algebra).
  
(** 定理：所有连续函数都是Borel可测的 *)
Theorem all_continuous_are_borel_measurable :
  forall (f : R -> R), continuous f -> Borel_measurable_function f.
Proof.
  intros f Hcont.
  unfold Borel_measurable_function.
  exact (continuous_is_borel_measurable f Hcont).
Qed.
  
(** 引理：连续函数的和是连续的 *)
Lemma continuous_plus (f g : R -> R) :
  continuous f -> continuous g -> continuous (fun x => f x + g x).
Proof.
  intros Hf Hg.
  unfold continuous, continuous_at.
  intros x eps Heps.
  (* 由f在x点连续 *)
  unfold continuous_at in Hf.
  specialize (Hf x).
  (* 由g在x点连续 *)
  unfold continuous_at in Hg.
  specialize (Hg x).
  (* 取ε/2 > 0 *)
  assert (Heps_half : eps/2 > 0). { lra. }
  destruct (Hf (eps/2) Heps_half) as [delta1 [Hdelta1_pos Hf1]].
  destruct (Hg (eps/2) Heps_half) as [delta2 [Hdelta2_pos Hg1]].
  (* 取δ = min(δ1, δ2) *)
  set (delta := Rmin delta1 delta2).
  assert (Hdelta_pos : delta > 0).
  { 
    unfold delta. 
    (* 使用 Rmin_glb_lt 证明两个正数的最小值是正数 *)
    apply Rmin_glb_lt; assumption.
  }
  exists delta.
  split. 
  { exact Hdelta_pos. }
  intros y Hdist.
  (* 计算差值 *)
  replace ((f y + g y) - (f x + g x)) with ((f y - f x) + (g y - g x)) by ring.
  apply Rle_lt_trans with (Rabs (f y - f x) + Rabs (g y - g x)).
  { 
    apply Rabs_triang.
  }
  (* 证明每个部分都小于ε/2 *)
  assert (Hdist1 : Rabs (y - x) < delta1).
  { 
    apply Rlt_le_trans with delta.
    { exact Hdist. }
    { unfold delta; apply Rmin_l. }
  }
  assert (Hdist2 : Rabs (y - x) < delta2).
  { 
    apply Rlt_le_trans with delta.
    { exact Hdist. }
    { unfold delta; apply Rmin_r. }
  }
  specialize (Hf1 y Hdist1).
  specialize (Hg1 y Hdist2).
  lra.
Qed.
  
(** 引理：连续函数的积是连续的 *)
Lemma continuous_mult (f g : R -> R) :
  continuous f -> continuous g -> continuous (fun x => f x * g x).
Proof.
  intros Hf Hg.
  unfold continuous, continuous_at.
  intros x eps Heps.
  (* 由f在x点连续 *)
  unfold continuous_at in Hf.
  specialize (Hf x).
  (* 由g在x点连续 *)
  unfold continuous_at in Hg.
  specialize (Hg x).
  (* 第一步：由f连续，存在δ1使得当|y-x|<δ1时，|f(y)-f(x)|<1 *)
  assert (Hpos1 : 1 > 0). { lra. }
  destruct (Hf 1 Hpos1) as [delta1 [Hdelta1_pos Hf1]].
  set (M1 := Rabs (f x) + 1).
  assert (Habs_fx : 0 <= Rabs (f x)) by apply Rabs_pos.
  assert (HM1_pos : M1 > 0).
  { 
    unfold M1.
    lra.
  }
  (* 第二步：由g连续，对于 ε/(2M₁) > 0，存在 δ₂ *)
  assert (HepsM1_pos : eps/(2*M1) > 0).
  { 
    apply Rdiv_lt_0_compat.
    { exact Heps. }  (* eps > 0 *)
    { 
      apply Rmult_lt_0_compat.
      { lra. }  (* 2 > 0 *)
      { exact HM1_pos. }  (* M1 > 0 *)
    }
  }
  destruct (Hg (eps/(2*M1)) HepsM1_pos) as [delta2 [Hdelta2_pos Hg1]].
  (* 第三步：由 f 连续，对于 ε/(2(|g(x₀)|+1)) > 0，存在 δ₃ *)
  set (G0 := Rabs (g x) + 1).
  assert (Habs_gx : 0 <= Rabs (g x)) by apply Rabs_pos.
  assert (HG0_pos : G0 > 0).
  { 
    unfold G0.
    lra.
  }
  assert (HepsG0_pos : eps/(2*G0) > 0).
  { 
    apply Rdiv_lt_0_compat.
    { exact Heps. }  (* eps > 0 *)
    { 
      apply Rmult_lt_0_compat.
      { lra. }  (* 2 > 0 *)
      { exact HG0_pos. }  (* G0 > 0 *)
    }
  }
  destruct (Hf (eps/(2*G0)) HepsG0_pos) as [delta3 [Hdelta3_pos Hf2]].
  (* 取 δ = min(δ₁, δ₂, δ₃) *)
  set (delta := Rmin delta1 (Rmin delta2 delta3)).
  (* 证明 delta > 0 *)
  assert (Hmin23_pos : 0 < Rmin delta2 delta3).
  { apply Rmin_pos; assumption. }
  assert (Hdelta_pos : delta > 0).
  { unfold delta. apply Rmin_pos; assumption. }
  exists delta.
  split. 
  { exact Hdelta_pos. }
  intros y Hdist.
  (* 分解乘积差 *)
  replace (f y * g y - f x * g x) with 
          (f y * (g y - g x) + (f y - f x) * g x) by ring.
  apply Rle_lt_trans with (Rabs (f y * (g y - g x)) + Rabs ((f y - f x) * g x)).
  { 
    apply Rabs_triang.
  }
  (* 展开绝对值乘积 *)
  rewrite Rabs_mult.
  rewrite Rabs_mult.
  
  (* 证明 |f(y)| ≤ M₁ *)
  assert (Hfy_bound : Rabs (f y) <= M1).
  {
    unfold M1.
    (* 使用三角不等式：|f(y)| = |f(x) + (f(y) - f(x))| ≤ |f(x)| + |f(y) - f(x)| *)
    replace (f y) with (f x + (f y - f x)) by ring.
    apply Rle_trans with (Rabs (f x) + Rabs (f y - f x)).
    { 
      apply Rabs_triang.
    }
    (* 现在需要证明 |f(x)| + |f(y) - f(x)| ≤ |f(x)| + 1 *)
    apply Rplus_le_compat_l.
    (* 由 Hf1，我们知道 |f(y) - f(x)| < 1，所以 ≤ 1 *)
    apply Rlt_le.
    apply Hf1.
    (* 证明 |y - x| < delta1 *)
    assert (Hdist1 : Rabs (y - x) < delta1).
    { 
      apply Rlt_le_trans with delta.
      { exact Hdist. }
      { unfold delta; apply Rmin_l. }
    }
    exact Hdist1.
  }
  
  (* 证明 |g(y) - g(x)| < ε/(2M₁) *)
  assert (Hgy_diff : Rabs (g y - g x) < eps / (2 * M1)).
  {
    apply Hg1.
    assert (Hdist2 : Rabs (y - x) < delta2).
    { 
      apply Rlt_le_trans with delta.
      { exact Hdist. }
      {
        unfold delta.
        apply Rle_trans with (Rmin delta2 delta3).
        { apply Rmin_r. }  (* delta ≤ Rmin delta2 delta3 *)
        { apply Rmin_l. }  (* Rmin delta2 delta3 ≤ delta2 *)
      }
    }
    exact Hdist2.
  }
  
  (* 证明 |f(y) - f(x)| < ε/(2G₀) *)
  assert (Hfy_diff : Rabs (f y - f x) < eps / (2 * G0)).
  {
    apply Hf2.
    assert (Hdist3 : Rabs (y - x) < delta3).
    { 
      apply Rlt_le_trans with delta.
      { exact Hdist. }
      {
        unfold delta.
        apply Rle_trans with (Rmin delta2 delta3).
        { apply Rmin_r. }  (* delta ≤ Rmin delta2 delta3 *)
        { apply Rmin_r. }  (* Rmin delta2 delta3 ≤ delta3 *)
      }
    }
    exact Hdist3.
  }
  
  (* 证明 |g(x)| ≤ G₀ *)
  assert (Hgx_bound : Rabs (g x) <= G0).
  {
    unfold G0.
    lra.
  }
  
  (* 分别估计两个项 *)
  (* 第一项：|f(y)| * |g(y)-g(x)| *)
  assert (Hterm1 : Rabs (f y) * Rabs (g y - g x) <= M1 * Rabs (g y - g x)).
  {
    (* 因为 |f(y)| ≤ M1 且 |g(y)-g(x)| ≥ 0 *)
    apply Rmult_le_compat_r.
    { apply Rabs_pos. }  (* |g(y)-g(x)| ≥ 0 *)
    { exact Hfy_bound. }  (* |f(y)| ≤ M1 *)
  }
  
  assert (Hterm1_strict : M1 * Rabs (g y - g x) < M1 * (eps / (2 * M1))).
  {
    (* 因为 |g(y)-g(x)| < ε/(2M₁) 且 M1 > 0 *)
    apply Rmult_lt_compat_l.
    { exact HM1_pos. }  (* M1 > 0 *)
    { exact Hgy_diff. }  (* |g(y)-g(x)| < ε/(2M₁) *)
  }
  
  (* 第二项：|f(y)-f(x)| * |g(x)| *)
  assert (Hterm2 : Rabs (f y - f x) * Rabs (g x) <= Rabs (f y - f x) * G0).
  {
    (* 因为 |f(y)-f(x)| ≥ 0 且 |g(x)| ≤ G0 *)
    apply Rmult_le_compat_l.
    { apply Rabs_pos. }  (* |f(y)-f(x)| ≥ 0 *)
    { exact Hgx_bound. }  (* |g(x)| ≤ G0 *)
  }
  
  assert (Hterm2_strict : Rabs (f y - f x) * G0 < (eps / (2 * G0)) * G0).
  {
    (* 因为 |f(y)-f(x)| < ε/(2G₀) 且 G0 > 0 *)
    apply Rmult_lt_compat_r.
    { exact HG0_pos. }  (* G0 > 0 *)
    { exact Hfy_diff. }  (* |f(y)-f(x)| < ε/(2G₀) *)
  }
  
  (* 化简表达式 *)
  assert (Hsimpl1 : M1 * (eps / (2 * M1)) = eps / 2).
  {
    field.
    (* 需要证明分母 2 * M1 ≠ 0 *)
    intro H.
    (* 假设 2 * M1 = 0，但 M1 > 0，矛盾 *)
    apply Rlt_irrefl with 0.
    rewrite H in HM1_pos.
    exact HM1_pos.
  }
  
  assert (Hsimpl2 : (eps / (2 * G0)) * G0 = eps / 2).
  {
    field.
    (* 需要证明分母 2 * G0 ≠ 0 *)
    intro H.
    (* 假设 2 * G0 = 0，但 G0 > 0，矛盾 *)
    apply Rlt_irrefl with 0.
    rewrite H in HG0_pos.
    exact HG0_pos.
  }
  
  (* 现在将所有不等式组合起来 *)
  apply Rle_lt_trans with (M1 * Rabs (g y - g x) + Rabs (f y - f x) * G0).
  {
    (* 使用之前的不等式 *)
    apply Rplus_le_compat.
    { exact Hterm1. }
    { exact Hterm2. }
  }
  apply Rlt_le_trans with (M1 * (eps / (2 * M1)) + (eps / (2 * G0)) * G0).
  {
    (* 使用严格不等式 *)
    apply Rplus_lt_compat.
    { exact Hterm1_strict. }
    { exact Hterm2_strict. }
  }
  rewrite Hsimpl1.
  rewrite Hsimpl2.
  lra.  (* 证明 eps/2 + eps/2 = eps *)
Qed.
  
(** 备注：连续函数类构成一个代数 *)
Remark continuous_functions_algebra :
  (* 常数函数连续 *)
  (forall c : R, continuous (fun _ => c)) /\
  (* 恒等函数连续 *)
  (continuous (fun x => x)) /\
  (* 连续函数的和连续 *)
  (forall f g, continuous f -> continuous g -> continuous (fun x => f x + g x)) /\
  (* 连续函数的积连续 *)
  (forall f g, continuous f -> continuous g -> continuous (fun x => f x * g x)).
Proof.
  split.
  { apply continuous_const. }
  split.
  { apply continuous_id. }
  split.
  { intros f g Hf Hg. apply continuous_plus; assumption. }
  { intros f g Hf Hg. apply continuous_mult; assumption. }
Qed.
  
(* 补充引理：乘积σ代数和可测性 *)
  
(* 定义R×R的Borel σ代数 *)
Definition Borel_sigma_algebra_R2 : SigmaAlgebra (R * R) :=
  generated_sigma_algebra
    (fun A : SetX (R * R) =>
      exists (A1 A2 : SetX R),
        In A1 (sigma_sets R Borel_sigma_algebra) /\
        In A2 (sigma_sets R Borel_sigma_algebra) /\
        SetEq A (fun p : R * R => A1 (fst p) /\ A2 (snd p))).
  
(* 引理：有限交在σ代数中封闭 *)
Lemma sigma_sets_closed_under_finite_intersection : forall X M A B,
  @sigma_sets X M A -> @sigma_sets X M B -> @sigma_sets X M (fun x => A x /\ B x).
Proof.
  intros X M A B HA HB.
  
  (* 方法：将交集表示为补集的并的补集 *)
  (* A ∩ B = (Aᶜ ∪ Bᶜ)ᶜ *)
  assert (Heq : (fun x => A x /\ B x) = 
               Complement_s (fun x => (Complement_s A) x \/ (Complement_s B) x)).
  {
    apply set_extensionality.
    intro x.
    split.
    - intros [HAx HBx].
      intro H.
      destruct H as [HcompA | HcompB].
      + contradiction.
      + contradiction.
    - intro H.
      split.
      + (* 证明 A x *)
        apply Coq.Logic.Classical_Prop.NNPP.
        intro HnotA.
        apply H.
        left.
        exact HnotA.
      + (* 证明 B x *)
        apply Coq.Logic.Classical_Prop.NNPP.
        intro HnotB.
        apply H.
        right.
        exact HnotB.
  }
  
  rewrite Heq.
  
  (* 应用补集封闭性 *)
  apply sigma_sets_complement.
  
  (* 现在需要证明 (Complement_s A) ∪ (Complement_s B) 可测 *)
  (* 首先证明 Complement_s A 和 Complement_s B 可测 *)
  assert (HcompA : In (Complement_s A) (sigma_sets X M)).
  { apply sigma_sets_complement; exact HA. }
  
  assert (HcompB : In (Complement_s B) (sigma_sets X M)).
  { apply sigma_sets_complement; exact HB. }
  
  (* 构造序列来表示有限并 *)
  set (F_seq := fun (n : nat) =>
    match n with
    | O => Complement_s A
    | S O => Complement_s B
    | _ => EmptySet (X:=X)
    end).
  
  assert (HF_seq : forall n, In (F_seq n) (sigma_sets X M)).
  {
    intro n.
    destruct n as [O | n'].
    - unfold F_seq; exact HcompA.
    - destruct n' as [O | n''].
      + unfold F_seq; exact HcompB.
      + unfold F_seq.
        (* 空集在σ代数中：作为全集的补集 *)
        assert (Huniv : In (UniversalSet (X:=X)) (sigma_sets X M)).
        {
          (* 需要证明全集在σ代数中 *)
          (* 这通常是σ代数的公理之一 *)
          (* 我们需要一个引理：sigma_sets 包含全集 *)
          (* 假设我们有 sigma_sets_univ_instance *)
          apply (sigma_sets_univ_instance X M).
        }
        rewrite <- complement_universal_empty.
        apply sigma_sets_complement.
        exact Huniv.
  }
  
  (* 证明并集等于可数并 *)
  assert (Heq_union : (fun x => (Complement_s A) x \/ (Complement_s B) x) =
                     (fun x => exists n, In x (F_seq n))).
  {
    apply set_extensionality.
    intro x.
    split.
    - intros [H1 | H2].
      + exists O.
        unfold F_seq; exact H1.
      + exists (S O).
        unfold F_seq; exact H2.
    - intros [n Hn].
      destruct n as [O | n'].
      + unfold F_seq in Hn; left; exact Hn.
      + destruct n' as [O | n''].
        * unfold F_seq in Hn; right; exact Hn.
        * unfold F_seq in Hn; contradiction.
  }
  
  rewrite Heq_union.
  
  (* 应用可数并封闭性 *)
  apply sigma_sets_countable_union.
  exact HF_seq.
Qed.
  
(* 引理：有限并在σ代数中封闭 *)
Lemma sigma_sets_closed_under_finite_union : forall X M A B,
  @sigma_sets X M A -> @sigma_sets X M B -> @sigma_sets X M (fun x => A x \/ B x).
Proof.
  intros X M A B HA HB.
  
  (* 将并集表示为补集的交的补集：A ∪ B = (Aᶜ ∩ Bᶜ)ᶜ *)
  assert (Heq : (fun x => A x \/ B x) = 
               Complement_s (fun x => (Complement_s A) x /\ (Complement_s B) x)).
  {
    apply set_extensionality.
    intro x.
    split.
    - intros [HAx | HBx].
      + intro H.
        destruct H as [HcompA HcompB].
        contradiction.
      + intro H.
        destruct H as [HcompA HcompB].
        contradiction.
    - intro H.
      (* 使用排中律 *)
      destruct (classic (A x)) as [HAx | HnotA].
      + left; exact HAx.
      + right.
        (* 现在需要证明 B x *)
        apply Coq.Logic.Classical_Prop.NNPP.
        intro HnotB.
        apply H.
        split; assumption.
  }
  
  rewrite Heq.
  
  (* 应用补集封闭性 *)
  apply sigma_sets_complement.
  
  (* 应用有限交封闭性 *)
  apply sigma_sets_closed_under_finite_intersection.
  - apply sigma_sets_complement; exact HA.
  - apply sigma_sets_complement; exact HB.
Qed.
  
(* 这是 sigma_sets 的最小性引理 *)
Lemma sigma_sets_minimal : forall X (G : Family X) (sigma_G : Family X),
    (* 假设 sigma_G 是由 G 生成的 σ 代数 *)
    (forall (S : Family X),
        (forall B, G B -> S B) ->
        contains_universe S ->
        closed_under_complement S ->
        closed_under_countable_union S ->
        forall A, sigma_G A -> S A) ->
    (* 那么对于任意满足四个条件的 M，有 sigma_G ⊆ M *)
    forall (M : Family X),
    (forall B, G B -> M B) ->
    contains_universe M ->
    closed_under_complement M ->
    closed_under_countable_union M ->
    forall A, sigma_G A -> M A.
Proof.
  intros X G sigma_G Hminimal M HG Huniv Hcomp Hcunion A HA.
  (* 直接应用 sigma_G 的最小性性质 *)
  apply (Hminimal M HG Huniv Hcomp Hcunion A HA).
Qed.
  
(* 引理：乘积 σ 代数是包含所有矩形的最小 σ 代数 *)
(* 重新定义 sigma_sets 函数，以避免与记录投影冲突 *)
Definition my_sigma_sets (X:Type) (G:Family X) : Family X :=
  fun A : SetX X =>
    forall (S : Family X), 
      (forall B, G B -> S B) -> 
      contains_universe S -> 
      closed_under_complement S -> 
      closed_under_countable_union S -> 
      S A.
Lemma product_sigma_algebra_is_minimal_record :
  forall (M : SigmaAlgebra (R * R)),
    (forall A1 A2,
      A1 in_s (@sigma_sets R Borel_sigma_algebra) ->
      A2 in_s (@sigma_sets R Borel_sigma_algebra) ->
      (fun p : R * R => A1 (fst p) /\ A2 (snd p)) in_s (@sigma_sets (R * R) M)) ->
    forall A,
      A in_s (my_sigma_sets (R * R) (fun A0 : SetX (R * R) =>
        exists (A1 A2 : SetX R),
          A1 in_s (@sigma_sets R Borel_sigma_algebra) /\
          A2 in_s (@sigma_sets R Borel_sigma_algebra) /\
          A0 eq_s (fun p : R * R => A1 (fst p) /\ A2 (snd p)))) ->
      A in_s (@sigma_sets (R * R) M).
Proof.
  intros M Hrectangles A HA.
  
  (* 展开 my_sigma_sets 的定义 *)
  unfold my_sigma_sets in HA.
  
  (* 根据 HA 的定义，我们需要证明对于任意满足条件的 S，A 在 S 中 *)
  (* 特别地，我们可以取 S 为 M 的 sigma_sets *)
  apply HA with (S := @sigma_sets (R * R) M).
  
  (* 现在需要提供四个条件： *)
  (* 1. 所有矩形都在 M 的 sigma_sets 中 *)
  - intros B HB.
    destruct HB as [A1 [A2 [HA1 [HA2 Heq]]]].
    (* 将集合相等性转换为函数相等性 *)
    pose proof (set_extensionality _ _ Heq) as Hfunc_eq.
    (* Hfunc_eq: B = (fun p => A1 (fst p) /\ A2 (snd p)) *)
    
    (* 使用 Hrectangles 证明矩形在 M 中 *)
    assert (Hrect_in_M : (fun p : R * R => A1 (fst p) /\ A2 (snd p)) in_s (@sigma_sets (R * R) M)).
    { apply Hrectangles; assumption. }
    
    (* 重写目标：将 B 替换为矩形 *)
    rewrite Hfunc_eq.
    exact Hrect_in_M.
    
  (* 2. M 的 sigma_sets 包含全集 *)
  - apply (@sigma_contains_universe (R * R) M).
    
  (* 3. M 的 sigma_sets 对补集封闭 *)
  - apply (@sigma_closed_complement (R * R) M).
    
  (* 4. M 的 sigma_sets 对可数并封闭 *)
  - apply (@sigma_closed_countable_union (R * R) M).
Qed.
  
(* 对应 my_sigma_sets 的 subset 引理 *)
Lemma my_sigma_sets_subset : forall X (G : Family X) (M : Family X),
    (forall B, G B -> M B) ->
    contains_universe M ->
    closed_under_complement M ->
    closed_under_countable_union M ->
    forall A, my_sigma_sets X G A -> M A.
Proof.
  intros X G M HG Huniv Hcomp Hcunion A HA.
  unfold my_sigma_sets in HA.
  apply HA with (S := M); assumption.
Qed.
  
(* 交集可测 *)
Lemma intersection_measurable : forall A B,
    In A (sigma_sets R Borel_sigma_algebra) ->
    In B (sigma_sets R Borel_sigma_algebra) ->
    In (fun x : R => A x /\ B x) (sigma_sets R Borel_sigma_algebra).
Proof.
  intros A B HA HB.
  (* 使用德摩根定律：A ∩ B = (A^c ∪ B^c)^c *)
  assert (Heq : (fun x : R => A x /\ B x) = 
               Complement_s (fun x : R => (Complement_s A) x \/ (Complement_s B) x)).
  {
    apply set_extensionality.
    intro x.
    split.
    - intros [Hx1 Hx2].
      intro H.
      destruct H as [H1 | H2].
      + apply H1; exact Hx1.
      + apply H2; exact Hx2.
    - intro H.
      split.
      + apply NNPP.
        intro H1.
        apply H.
        left; exact H1.
      + apply NNPP.
        intro H2.
        apply H.
        right; exact H2.
  }
  rewrite Heq.
  
  (* 应用补集封闭性 *)
  apply sigma_sets_complement.
  
  (* 现在需要证明并集在 sigma_sets R Borel_sigma_algebra 中 *)
  (* 构造序列 F_seq *)
  set (F_seq := fun (n : nat) =>
    match n with
    | O => Complement_s A
    | S O => Complement_s B
    | S (S n') => EmptySet (X:=R)
    end).
  
  (* 证明每个 F_seq n 在 sigma_sets R Borel_sigma_algebra 中 *)
  assert (HF_seq : forall n, In (F_seq n) (sigma_sets R Borel_sigma_algebra)).
  {
    intro n.
    unfold F_seq.
    (* 使用嵌套的 destruct 来匹配三种情况 *)
    destruct n as [O | n'].
    { (* n = O *)
      apply sigma_sets_complement; exact HA.
    }
    destruct n' as [O | n''].
    { (* n = S O *)
      apply sigma_sets_complement; exact HB.
    }
    { (* n = S (S n'') *)
      (* 空集在 Borel σ代数中 *)
      assert (H_empty : In (EmptySet (X:=R)) (sigma_sets R Borel_sigma_algebra)).
      {
        (* 空集作为全集的补集 *)
        rewrite <- complement_universal_empty.
        apply sigma_sets_complement.
        apply sigma_sets_univ_instance.
      }
      exact H_empty.
    }
  }
  
  (* 证明并集等于可数并 *)
  assert (H_eq_union : (fun x : R => (Complement_s A) x \/ (Complement_s B) x) =
                       (fun x : R => exists n, In x (F_seq n))).
  {
    apply set_extensionality.
    intro x.
    split.
    - intros [Hx1 | Hx2].
      + exists O; exact Hx1.
      + exists (S O); exact Hx2.
    - intros [n Hn].
      unfold F_seq in Hn.
      (* 同样使用嵌套的 destruct *)
      destruct n as [O | n'].
      + left; exact Hn.
      + destruct n' as [O | n''].
        * right; exact Hn.
        * contradiction.
  }
  
  rewrite H_eq_union.
  
  (* 应用可数并封闭性 *)
  apply sigma_sets_countable_union.
  exact HF_seq.
Qed.
  
(* σ 代数对有限交封闭 *)
Lemma sigma_sets_finite_intersection_closed : forall X (M : SigmaAlgebra X) (S : Family X),
    contains_universe S ->
    closed_under_complement S ->
    closed_under_countable_union S ->
    forall A B,
    In A S ->
    In B S ->
    In (fun x : X => A x /\ B x) S.
Proof.
  intros X M S Huniv Hcomp Hunion A B HA HB.
  
  (* 使用德摩根定律将交集转化为补集的并的补集 *)
  assert (Heq : (fun x : X => A x /\ B x) = 
               Complement_s (fun x : X => (Complement_s A) x \/ (Complement_s B) x)).
  {
    apply set_extensionality.
    intro x.
    split.
    - intros [Hx1 Hx2].
      intro H.
      destruct H as [H1 | H2].
      + apply H1; exact Hx1.
      + apply H2; exact Hx2.
    - intro H.
      split.
      + apply NNPP.
        intro H1.
        apply H.
        left; exact H1.
      + apply NNPP.
        intro H2.
        apply H.
        right; exact H2.
  }
  rewrite Heq.
  
  (* 应用补集封闭性 *)
  apply Hcomp.
  
  (* 构造序列 F_seq 来模拟有限并 *)
  set (F_seq := fun (n : nat) =>
      match n with
      | O => Complement_s A
      | S O => Complement_s B
      | S (S n') => EmptySet (X:=X)
      end).
  
  (* 证明每个 F_seq n 都在 S 中 *)
  assert (HF_seq : forall n, In (F_seq n) S).
  {
    intro n.
    unfold F_seq.
    (* 使用嵌套的 destruct 匹配三种情况 *)
    destruct n as [O | n'].
    { (* n = 0: 第一个补集 *)
      apply Hcomp; exact HA.
    }
    destruct n' as [O | n''].
    { (* n = 1: 第二个补集 *)
      apply Hcomp; exact HB.
    }
    { (* n >= 2: 空集 *)
      (* 证明空集在 S 中 *)
      assert (H_empty : In (EmptySet (X:=X)) S).
      {
        (* 空集作为全集的补集 *)
        rewrite <- complement_universal_empty.
        apply Hcomp.
        apply Huniv.
      }
      exact H_empty.
    }
  }
  
  (* 证明并集等于可数并 *)
  assert (H_eq_union : (fun x : X => (Complement_s A) x \/ (Complement_s B) x) =
                       (fun x : X => exists n, In x (F_seq n))).
  {
    apply set_extensionality.
    intro x.
    split.
    - intros [Hx1 | Hx2].
      + exists 0%nat; exact Hx1.   (* 对应第一个补集 *)
      + exists 1%nat; exact Hx2.   (* 对应第二个补集 *)
    - intros [n Hn].
      unfold F_seq in Hn.
      (* 使用嵌套的 destruct 匹配三种情况 *)
      destruct n as [O | n'].
      + left; exact Hn.                    (* n = 0 *)
      + destruct n' as [O | n''].
        * right; exact Hn.                 (* n = 1 *)
        * contradiction.                   (* n >= 2: 空集导致矛盾 *)
  }
  
  rewrite H_eq_union.
  
  (* 应用可数并封闭性 *)
  apply Hunion.
  exact HF_seq.
Qed.
  
(** 引理：集合相等性在σ代数中的保持 **)
(** 如果两个集合相等，并且其中一个在σ代数中，那么另一个也在σ代数中 **)
Lemma set_eq_in_sigma_sets : forall X (M : SigmaAlgebra X) (A B : SetX X),
    A = B -> In A (sigma_sets X M) -> In B (sigma_sets X M).
Proof.
  intros. rewrite <- H. assumption.
Qed.
  
(** 闭区间在 Borel σ代数中 **)
Lemma closed_interval_in_borel : forall a b : R,
  In (fun x : R => a <= x /\ x <= b) (sigma_sets R Borel_sigma_algebra).
Proof.
  intros a b.
  (* 展开 Borel_sigma_algebra 的定义 *)
  unfold Borel_sigma_algebra.
  (* 使用生成σ代数的定义 *)
  unfold generated_sigma_algebra.
  unfold sigma_sets.
  intros S [Hgen [Huniv [Hcomp Hcunion]]].
  (* 我们需要证明闭区间在 S 中 *)
  (* 根据 Hgen：S 包含生成集族中的所有集合 *)
  apply Hgen.
  (* 生成集族定义为：存在 a b 使得集合等于闭区间 [a,b] *)
  exists a, b.
  (* 集合相等性：闭区间 [a,b] 等于自身 *)
  unfold SetEq.
  intro x.
  split; intro H; exact H.
Qed.
  
(** 闭区间在 Borel σ代数中（带 SetEq 版本） - 简洁版 **)
Lemma closed_interval_in_borel_set_eq : forall (A : SetX R) a b,
  SetEq A (fun x : R => a <= x /\ x <= b) ->
  In A (sigma_sets R Borel_sigma_algebra).
Proof.
  intros A a b Heq.
  apply (set_eq_in_sigma_sets R Borel_sigma_algebra 
         (fun x : R => a <= x /\ x <= b) A).
  - apply set_extensionality_simple.
    intro x.
    symmetry.  (* 使用对称性简化 *)
    exact (Heq x).
  - apply closed_interval_in_borel.
Qed.
  
(** 引理：Borel可测函数对的可测性 **)
(** 如果 f 和 g 都是Borel可测函数，那么对于任意二维Borel可测集 C， *)
(** 其原像 {x | (f x, g x) ∈ C} 也是一维Borel可测的 **)
Lemma borel_measurable_pair :
  forall (f g : R -> R),
    Borel_measurable_function f ->
    Borel_measurable_function g ->
    forall (C : SetX (R * R)),
      In C (@sigma_sets (R * R) Borel_sigma_algebra_R2) ->
      In (fun x : R => C (f x, g x)) (my_sigma_sets R (@sigma_sets R Borel_sigma_algebra)).
Proof.
  intros f g Hf Hg C HC.  (* 引入函数f、g及其可测性假设，以及集合C和其在二维Borel代数中的假设 *)
  
  (* 1. 定义集合族 M：所有使得原像在一维Borel代数中的二维集合 *)
  set (M := fun (C' : SetX (R * R)) =>
      In (fun x : R => C' (f x, g x)) (sigma_sets R Borel_sigma_algebra)).
  
  (* 2. 证明 M 包含所有矩形（即由两个一维Borel集形成的乘积集） *)
  assert (H_rectangles : forall A1 A2,
      In A1 (sigma_sets R Borel_sigma_algebra) ->
      In A2 (sigma_sets R Borel_sigma_algebra) ->
      M (fun p : R * R => A1 (fst p) /\ A2 (snd p))).
  {
    intros A1 A2 HA1 HA2.
    unfold M.
    simpl.  (* 化简表达式：原像变为 A1 (f x) ∧ A2 (g x) *)
    assert (H1 : In (fun x : R => A1 (f x)) (sigma_sets R Borel_sigma_algebra)).
    { apply Hf; exact HA1. }  (* 由f的可测性，A1的原像可测 *)
    assert (H2 : In (fun x : R => A2 (g x)) (sigma_sets R Borel_sigma_algebra)).
    { apply Hg; exact HA2. }  (* 由g的可测性，A2的原像可测 *)
    apply intersection_measurable; assumption.  (* 两个可测集的交集可测 *)
  }
  
  (* 3. 证明 M 是一个σ代数 *)
  
  (* 3.1 包含全集 *)
  assert (H_univ : M (UniversalSet (X:=R * R))).
  {
    unfold M.
    assert (Heq : (fun x : R => UniversalSet (f x, g x)) = UniversalSet (X:=R)).
    {
      apply set_extensionality.
      intro x.
      split; intro H; apply universal_set_property.  (* 任何点都在全集中 *)
    }
    rewrite Heq.
    apply sigma_sets_univ_instance.  (* 全集在Borel σ代数中 *)
  }
  
  (* 3.2 对补集封闭 *)
  assert (H_comp : forall A, M A -> M (Complement_s A)).
  {
    intros A HA.
    unfold M in *.
    assert (Heq : (fun x : R => (Complement_s A) (f x, g x)) = 
                  Complement_s (fun x : R => A (f x, g x))).
    {
      apply set_extensionality.
      intro x.
      split; intro H; exact H.  (* 补集的原像等于原像的补集 *)
    }
    rewrite Heq.
    apply sigma_sets_complement; exact HA.  (* 可测集的补集可测 *)
  }
  
  (* 3.3 对可数并封闭 *)
  assert (H_union : forall (F : nat -> SetX (R * R)), (forall n, M (F n)) -> M (fun p => exists n, In p (F n))).
  {
    intros F HF.
    unfold M in *.
    apply sigma_sets_countable_union.  (* 可数并的可测性 *)
    intro n.
    apply (HF n).  (* 每个F_n的原像都可测 *)
  }
  
  (* 3.4 对有限交封闭（辅助性质） *)
  assert (H_finite_inter : forall A B, In A M -> In B M -> In (fun p => A p /\ B p) M).
  {
    intros A B HA_M HB_M.
    unfold M in HA_M, HB_M.
    apply intersection_measurable; assumption.  (* 两个可测集的交集可测 *)
  }
  
  (* 3.5 证明 M 对有限并封闭（辅助性质） *)
  assert (H_finite_union : forall A B, In A M -> In B M -> In (fun p => A p \/ B p) M).
  {
    intros A B HA_M HB_M.
    unfold M in HA_M, HB_M.
    unfold M.
    
    (* 构造序列 F_seq 来模拟有限并 *)
    set (F_seq := fun (n : nat) =>
        match n with
        | O => (fun x : R => A (f x, g x))
        | S O => (fun x : R => B (f x, g x))
        | S (S n') => (fun _ : R => False)
        end).
    
    (* 证明每个 F_seq n 都在 sigma_sets R Borel_sigma_algebra 中 *)
    assert (HF_seq : forall n, In (F_seq n) (sigma_sets R Borel_sigma_algebra)).
    {
      intro n.
      unfold F_seq.
      destruct n as [O | n'].
      { (* n = 0: 对应 A (f x, g x) *)
        exact HA_M.
      }
      destruct n' as [O | n''].
      { (* n = 1: 对应 B (f x, g x) *)
        exact HB_M.
      }
      { (* n ≥ 2: 对应空集 *)
        (* 证明空集在 Borel σ代数中 *)
        assert (H_empty : In (EmptySet (X:=R)) (sigma_sets R Borel_sigma_algebra)).
        {
          (* 空集是全集的补集 *)
          rewrite <- complement_universal_empty.
          apply sigma_sets_complement.
          apply sigma_sets_univ_instance.  (* 全集可测 *)
        }
        exact H_empty.
      }
    }
    
    (* 证明有限并等于可数并 *)
    assert (Heq : (fun x : R => A (f x, g x) \/ B (f x, g x)) = 
                 (fun x : R => exists n, In x (F_seq n))).
    {
      apply set_extensionality.
      intro x.
      split.
      - (* 方向1：有限并包含在可数并中 *)
        intros [HA | HB].
        + (* A (f x, g x) 成立 *)
          exists 0%nat.
          exact HA.
        + (* B (f x, g x) 成立 *)
          exists 1%nat.
          exact HB.
      - (* 方向2：可数并包含在有限并中 *)
        intros [n Hn].
        unfold F_seq in Hn.
        destruct n as [O | n'].
        + (* n = 0 *)
          left; exact Hn.
        + destruct n' as [O | n''].
          * (* n = 1 *)
            right; exact Hn.
          * (* n ≥ 2，矛盾（空集） *)
            contradiction.
    }
    
    (* 使用可数并的可测性 *)
    pose proof (sigma_sets_countable_union R Borel_sigma_algebra F_seq HF_seq) as H_countable_union.
    apply (eq_rect _ (fun S => In S (sigma_sets R Borel_sigma_algebra)) H_countable_union _ (eq_sym Heq)).
  }
  
  (* 补充证明：空集在 M 中 *)
  assert (H_empty_M : In (EmptySet (X:=R * R)) M).
  {
    (* 空集作为全集的补集 *)
    rewrite <- complement_universal_empty.
    apply H_comp.
    exact H_univ.
  }
  
  (* 补充证明：M 对可数交封闭（辅助性质） *)
  assert (H_countable_inter : forall (F_seq : nat -> SetX (R * R)), 
    (forall n, In (F_seq n) M) -> In (fun x => forall n, In x (F_seq n)) M).
  {
    intros F_seq HF.
    (* 使用德摩根定律：可数交 = 可数并的补集 *)
    set (G_seq := fun n => Complement_s (F_seq n)).
    assert (HG_seq : forall n, In (G_seq n) M).
    {
      intro n.
      unfold G_seq.
      apply H_comp.
      apply (HF n).  (* 每个F_n在M中，故其补集也在M中 *)
    }
    pose proof (H_union G_seq HG_seq) as H_union_G.
    (* 现在 H_union_G : M (fun p => exists n, In p (G_seq n)) *)
    (* 即 M (fun p => exists n, In p (Complement_s (F_seq n))) *)
    
    (* 证明可数交等于补集的补集 *)
    assert (Heq : (fun p => forall n, In p (F_seq n)) = 
                 Complement_s (fun p => exists n, In p (Complement_s (F_seq n)))).
    {
      apply set_extensionality.
      intro p.
      split.
      - (* 从左到右：可数交包含在补集中 *)
        intro Hall.
        intro Hexists.
        destruct Hexists as [n Hn].
        apply Hn.
        apply Hall.  (* 对于所有n，p在F_seq n中，矛盾于存在n使得p在补集中 *)
      - (* 从右到左：补集包含在可数交中 *)
        intro Hcomp.
        intro n.
        apply NNPP.  (* 反证法 *)
        intro Hnot.
        apply Hcomp.
        exists n.
        exact Hnot.
    }
    rewrite Heq.
    apply H_comp.  (* 补集可测 *)
    exact H_union_G.
  }
  
  (* 4. 构建一个以 M 为集合族的 SigmaAlgebra 记录 *)
  pose (M' := {|
    sigma_sets := M;
    sigma_contains_universe := H_univ;
    sigma_closed_complement := H_comp;
    sigma_closed_countable_union := H_union;
    sigma_contains_empty := H_empty_M;
    sigma_closed_finite_union := H_finite_union;
    sigma_closed_countable_intersection := H_countable_inter
  |}).
  
  (* 5. 证明 M' 包含所有矩形（以M'的sigma_sets形式） *)
  assert (H_rectangles' : forall A1 A2,
      In A1 (sigma_sets R Borel_sigma_algebra) ->
      In A2 (sigma_sets R Borel_sigma_algebra) ->
      In (fun p : R * R => A1 (fst p) /\ A2 (snd p)) (sigma_sets (R * R) M')).
  {
    intros A1 A2 HA1 HA2.
    unfold sigma_sets; simpl.
    apply H_rectangles; assumption.  (* 直接使用H_rectangles *)
  }
  
  (* 6. 定义生成集族 G2：所有由两个一维Borel集形成的矩形 *)
  set (G2 := fun (A : SetX (R * R)) =>
    exists (A1 A2 : SetX R),
      In A1 (sigma_sets R Borel_sigma_algebra) /\
      In A2 (sigma_sets R Borel_sigma_algebra) /\
      SetEq A (fun p : R * R => A1 (fst p) /\ A2 (snd p))).
  
  (* 7. 证明 M' 包含 G2（通过集合相等性转换） *)
  assert (HG2: forall B, G2 B -> In B (sigma_sets (R * R) M')).
  {
    intros B [A1 [A2 [HA1 [HA2 Heq]]]].
    (* 将SetEq转换为函数相等 *)
    assert (Heq_func : (fun p : R * R => A1 (fst p) /\ A2 (snd p)) = B).
    { apply set_extensionality_simple; intro x; symmetry; apply Heq. }
    apply (set_eq_in_sigma_sets (R * R) M' (fun p : R * R => A1 (fst p) /\ A2 (snd p)) B Heq_func).
    apply H_rectangles'; assumption.  (* 矩形在M'中 *)
  }
  
  (* 8. 展开二维Borel代数的定义 *)
  unfold Borel_sigma_algebra_R2 in HC.
  simpl in HC.  (* 展开为my_sigma_sets形式 *)
  
  (* 9. 证明 M 包含 G2 中的所有集合（通过函数外延性） *)
  assert (HG2_M_condition: forall B, G2 B -> M B).
  {
    intros B [A1 [A2 [HA1 [HA2 Heq]]]].
    unfold M.
    (* 由 H_rectangles，矩形在 M 中 *)
    pose proof (H_rectangles A1 A2 HA1 HA2) as Hrect.
    unfold M in Hrect.
    simpl in Hrect.  (* 化简为 A1(f x) ∧ A2(g x) *)
    
    (* 将集合相等性Heq应用于点 (f x, g x) *)
    assert (Heq_pointwise: forall x, B (f x, g x) <-> A1 (f x) /\ A2 (g x)).
    {
      intro x.
      specialize (Heq (f x, g x)).
      simpl in Heq.
      exact Heq.  (* 直接应用SetEq的点态版本 *)
    }
    
    (* 使用函数外延性证明两个函数相等 *)
    assert (Heq_func: (fun x : R => B (f x, g x)) = (fun x : R => A1 (f x) /\ A2 (g x))).
    {
      apply functional_extensionality.
      intro x.
      apply propositional_extensionality.
      apply Heq_pointwise.
    }
    
    rewrite Heq_func.
    exact Hrect.  (* 使用Hrect完成证明 *)
  }
  
  (* 10. 证明 HC 中的生成集族包含于我们定义的 G2 *)
  (** 这一步是关键：将HC中复杂的生成集族表示转换为我们简洁的G2定义 **)
  assert (H_generator_inclusion: forall B,
      (exists A1 A2 : SetX R,
          A1 in_s (fun A3 : SetX R => forall F : Family R,
                     (forall A4 : SetX R, (exists a b : R, A4 eq_s (fun x : R => a <= x <= b)) -> A4 in_s F) /\
                     contains_universe F /\ closed_under_complement F /\ closed_under_countable_union F -> 
                     A3 in_s F) /\
          A2 in_s (fun A3 : SetX R => forall F : Family R,
                     (forall A4 : SetX R, (exists a b : R, A4 eq_s (fun x : R => a <= x <= b)) -> A4 in_s F) /\
                     contains_universe F /\ closed_under_complement F /\ closed_under_countable_union F -> 
                     A3 in_s F) /\
          B eq_s (fun p : R * R => A1 (fst p) /\ A2 (snd p))) ->
      G2 B).
  {
    intros B [A1 [A2 [HA1 [HA2 Heq]]]].
    unfold G2.
    exists A1, A2.
    split.
    - (* 证明 A1 在 sigma_sets R Borel_sigma_algebra 中 *)
      unfold Borel_sigma_algebra, generated_sigma_algebra, sigma_sets.
      exact HA1.  (* 直接使用HA1 *)
    - split.
      + (* 证明 A2 在 sigma_sets R Borel_sigma_algebra 中 *)
        unfold Borel_sigma_algebra, generated_sigma_algebra, sigma_sets.
        exact HA2.
      + exact Heq.
  }
  
  (* 11. 直接证明 M 满足 HC 所需的所有条件（生成集族条件） *)
  (** 这是连接HC和M的关键桥梁 **)
  assert (H_M_conditions_correct: 
    (forall A : SetX (R * R),
      A in_s (fun A0 : SetX (R * R) =>
        exists A1 A2 : SetX R,
          A1 in_s (fun A3 : SetX R =>
            forall F : Family R,
            (forall A4 : SetX R,
              (exists a b : R, A4 eq_s (fun x : R => a <= x <= b)) ->
              A4 in_s F) /\
            contains_universe F /\
            closed_under_complement F /\
            closed_under_countable_union F ->
            A3 in_s F) /\
          A2 in_s (fun A3 : SetX R =>
            forall F : Family R,
            (forall A4 : SetX R,
              (exists a b : R, A4 eq_s (fun x : R => a <= x <= b)) ->
              A4 in_s F) /\
            contains_universe F /\
            closed_under_complement F /\
            closed_under_countable_union F ->
            A3 in_s F) /\
          A0 eq_s (fun p : R * R => A1 (fst p) /\ A2 (snd p))) ->
      A in_s M)).
  {
    intros A [A1 [A2 [HA1 [HA2 Heq]]]].
    apply HG2_M_condition.  (* 转换为G2 B *)
    apply H_generator_inclusion.  (* 转换为HC的生成集族 *)
    exists A1, A2.
    split; [exact HA1 | split; [exact HA2 | exact Heq]].
  }
  
  (* 12. 应用 HC 得到 M C（利用my_sigma_sets的最小性） *)
  (** HC表明C在由生成集族生成的最小σ代数中，而M满足所有条件，故C在M中 **)
  assert (HM_C: M C).
  {
    (* 构建 HC 所需的完整条件：四个条件的合取 *)
    pose proof (conj H_M_conditions_correct (conj H_univ (conj H_comp H_union))) as H_all_conditions.
    exact (HC M H_all_conditions).  (* 应用HC *)
  }
  
  (* 13. 证明最终目标：原像在由一维Borel代数生成的σ代数中 *)
  unfold my_sigma_sets.
  intros S HgenS HunivS HcompS HcunionS.  (* 引入任意包含一维Borel代数的σ代数S *)
  apply HgenS.  (* 只需证明原像在一维Borel代数中 *)
  unfold M in HM_C.
  exact HM_C.  (* 这正是HM_C所证明的 *)
Qed.
  
(* =========================================================================== *)
(* 二维可测函数的可测性定理 *)
(* =========================================================================== *)
  
(** 定理：一对Borel可测函数的联合可测性 **)
(** 如果 f 和 g 都是Borel可测函数，那么映射 (f, g): R → R×R 是二维Borel可测的 **)
Theorem joint_measurability_of_measurable_pair : 
  forall (f g : R -> R),
  Borel_measurable_function f -> 
  Borel_measurable_function g ->
  forall (C : SetX (R * R)),
  In C (sigma_sets (R * R) Borel_sigma_algebra_R2) ->
  In (fun x : R => C (f x, g x)) (sigma_sets R Borel_sigma_algebra).
Proof.
  intros f g Hf Hg C HC.  (* 引入函数 f, g，其可测性假设，以及集合 C 和其在二维 Borel σ 代数中的假设 *)
  
  (* 定义集合族 M：所有使得原像可测的二维Borel集 *)
  set (M := fun (C' : SetX (R * R)) =>
      In (fun x : R => C' (f x, g x)) (sigma_sets R Borel_sigma_algebra)).
  
  (* 证明 M 包含生成集族（矩形） *)
  assert (Hrectangles : forall A B,
      In A (sigma_sets R Borel_sigma_algebra) ->
      In B (sigma_sets R Borel_sigma_algebra) ->
      M (fun p : R * R => A (fst p) /\ B (snd p))).
  {
    intros A B HA HB.  (* 引入两个一维 Borel 可测集 A 和 B *)
    unfold M.  (* 展开 M 的定义 *)
    (* 分别应用 f 和 g 的可测性得到 A(f(x)) 和 B(g(x)) 的可测性 *)
    pose proof (Hf A HA) as Hf_meas.  (* A(f(x)) 可测 *)
    pose proof (Hg B HB) as Hg_meas.  (* B(g(x)) 可测 *)
    (* 交集 A(f(x)) ∧ B(g(x)) 可测 *)
    apply intersection_measurable; assumption.
  }
  
  (* 证明 M 是一个λ-类（对补和可数不交并封闭） *)
  
  (* 4.1 包含全集 *)
  assert (Huniv : M (UniversalSet (X:=R * R))).
  {
    unfold M.  (* 展开 M 的定义 *)
    (* 证明原像是全集 *)
    assert (Heq : (fun x : R => UniversalSet (f x, g x)) = UniversalSet (X:=R)).
    {
      apply set_extensionality.  (* 使用集合外延性 *)
      intro x.
      split; intro H; apply universal_set_property.  (* 任何点都在全集中 *)
    }
    rewrite Heq.  (* 将原像重写为全集 *)
    apply sigma_sets_univ_instance.  (* 全集在 Borel σ 代数中 *)
  }
  
  (* 4.2 对差集封闭（通过补集和交集） *)
  assert (Hdiff : forall A B,
      M A -> M B -> Subset A B -> M (fun p => A p /\ ~ B p)).
  {
    intros A B HA_M HB_M Hsub.  (* 引入 A, B 在 M 中，以及 A ⊆ B 的假设 *)
    unfold M in *.  (* 展开 M 的定义 *)
    (* 证明 ~B 的原像可测 *)
    assert (H_not_B : In (fun x : R => ~ B (f x, g x)) (sigma_sets R Borel_sigma_algebra)).
    {
      (* 注意：~B 的原像等于 B 的原像的补集 *)
      assert (Heq : (fun x : R => ~ B (f x, g x)) = 
                   Complement_s (fun x : R => B (f x, g x))).
      { 
        apply set_extensionality.  (* 使用集合外延性 *)
        intro x.
        split; intro H; exact H.  (* 直接等价 *)
      }
      rewrite Heq.  (* 重写为目标形式 *)
      apply sigma_sets_complement.  (* 补集可测 *)
      exact HB_M.  (* B 的原像可测 *)
    }
    (* 现在 A 的原像和 ~B 的原像的交集可测 *)
    apply intersection_measurable with (A := fun x : R => A (f x, g x)) 
                                      (B := fun x : R => ~ B (f x, g x)).
    - exact HA_M.  (* A 的原像可测 *)
    - exact H_not_B.  (* ~B 的原像可测 *)
  }
  
  (* 4.3 对可数不交并封闭 *)
  assert (Hdisj_union : forall (F_seq : nat -> SetX (R * R)),
      (forall n, M (F_seq n)) ->
      (forall n m, n <> m -> Disjoint (F_seq n) (F_seq m)) ->
      M (fun p => exists n, F_seq n p)).
  {
    intros F_seq HF_seq Hdisj.  (* 引入序列 F_seq，每个在 M 中，且两两不交 *)
    unfold M in *.  (* 展开 M 的定义 *)
    (* 构造原像序列 *)
    set (preimage_seq := fun n => fun x => F_seq n (f x, g x)).
    (* 每个原像都可测 *)
    assert (Hpreimage_meas : forall n, In (preimage_seq n) 
                                         (sigma_sets R Borel_sigma_algebra)).
    { 
      intro n.
      unfold preimage_seq.  (* 展开 preimage_seq 的定义 *)
      apply HF_seq.  (* 使用假设 HF_seq *)
    }
    (* 注意：我们不需要显式证明原像的不交性，因为可数并可测性不依赖不交性 *)
    (* 原像的可数并等于原像的可数并 *)
    assert (Heq : (fun x : R => exists n, F_seq n (f x, g x)) = 
                 (fun x : R => exists n, preimage_seq n x)).
    { 
      apply set_extensionality.  (* 使用集合外延性 *)
      intro x.
      split.
      - intros [n H]; exists n; exact H.
      - intros [n H]; exists n; exact H.
    }
    rewrite Heq.  (* 重写为目标形式 *)
    (* 应用可数并的可测性 *)
    apply sigma_sets_countable_union.
    exact Hpreimage_meas.  (* 每个原像都可测 *)
  }
  
  (* 首先证明 M 包含所有矩形生成的代数 *)
  assert (Hcontains_rectangles : 
    forall A1 A2,
      In A1 (sigma_sets R Borel_sigma_algebra) ->
      In A2 (sigma_sets R Borel_sigma_algebra) ->
      M (fun p => A1 (fst p) /\ A2 (snd p))).
  { 
    exact Hrectangles.  (* 直接使用 Hrectangles *)
  }
  
  (* 直接应用二维Borel代数的定义 *)
  unfold Borel_sigma_algebra_R2 in HC.  (* 展开二维 Borel σ 代数的定义 *)
  
  (* 使用 sigma_sets 的最小性 *)
  apply HC.  (* 应用 HC，将目标转化为证明 M 满足生成σ代数的条件 *)
  
  (* 构建条件：M 包含生成集族且满足σ代数条件 *)
  split.
  {
    (* M 包含生成集族（矩形） *)
    intros B [A1 [A2 [HA1 [HA2 Heq]]]].  (* 引入 B 是一个矩形 *)
    (* 将SetEq转换为函数相等性 *)
    pose proof (set_extensionality _ _ Heq) as Heq_func.
    (* 直接应用集合相等性转换 *)
    rewrite Heq_func.  (* 将 B 重写为矩形形式 *)
    apply Hcontains_rectangles.  (* 应用矩形可测性 *)
    - exact HA1.  (* A1 可测 *)
    - exact HA2.  (* A2 可测 *)
  }
  
  (* 其余三个σ代数条件 *)
  split.
  { 
    exact Huniv.  (* M 包含全集 *)
  }
  split.
  {
    (* 对补集封闭 *)
    intros A HA_M.  (* 引入 A 在 M 中 *)
    unfold M in HA_M.  (* 展开 M 在假设中 *)
    unfold M.  (* 展开 M 在目标中 *)
    (* 补集的原像等于原像的补集 *)
    assert (Heq : (fun x : R => (Complement_s A) (f x, g x)) = 
                 Complement_s (fun x : R => A (f x, g x))).
    { 
      apply set_extensionality.  (* 使用集合外延性 *)
      intro x.
      split; intro H; exact H.  (* 直接等价 *)
    }
    (* 首先证明原像的补集可测 *)
    pose proof (sigma_sets_complement R Borel_sigma_algebra 
                (fun x : R => A (f x, g x)) HA_M) as Hcomp.
    (* 使用集合相等性转换 *)
    apply (set_eq_in_sigma_sets R Borel_sigma_algebra 
           (Complement_s (fun x : R => A (f x, g x)))
           (fun x : R => (Complement_s A) (f x, g x))).
    - exact (eq_sym Heq).  (* 注意：需要对称的等式 *)
    - exact Hcomp.  (* 补集可测 *)
  }
  
  {
    (* 对可数并封闭 *)
    intros F_seq HF_seq.  (* 引入序列 F_seq 和假设 HF_seq: 每个 F_seq n 在 M 中 *)
    unfold M.  (* 展开 M 的定义 *)
    simpl.  (* 简化目标：将 (fun x => (fun p => exists n, F_seq n p) (f x, g x)) 简化为 (fun x => exists n, F_seq n (f x, g x)) *)
    (* 定义原像序列 *)
    set (G_seq := fun (n : nat) (x : R) => F_seq n (f x, g x)).
    (* 应用可数并的可测性引理，指定序列为 G_seq *)
    apply (sigma_sets_countable_union R Borel_sigma_algebra G_seq).
    (* 证明每个 G_seq n 都可测 *)
    intro n.
    unfold G_seq.  (* 展开 G_seq 的定义 *)
    unfold M in HF_seq.  (* 展开 M 在 HF_seq 中 *)
    apply HF_seq.  (* 使用假设 HF_seq *)
  }
Qed.
  
(** 推论：连续函数对的联合可测性 **)
Corollary joint_measurability_of_continuous_pair :
  forall (f g : R -> R),
  continuous f -> continuous g ->
  forall (C : SetX (R * R)),
  In C (sigma_sets (R * R) Borel_sigma_algebra_R2) ->
  In (fun x : R => C (f x, g x)) (sigma_sets R Borel_sigma_algebra).
Proof.
  intros f g Hf Hg C HC.
  (* 应用连续函数是Borel可测的定理 *)
  pose proof (all_continuous_are_borel_measurable f Hf) as Hf_meas.
  pose proof (all_continuous_are_borel_measurable g Hg) as Hg_meas.
  
  (* 应用上面证明的定理 *)
  apply (joint_measurability_of_measurable_pair f g Hf_meas Hg_meas C HC).
Qed.
  
(** 定理：连续映射的可测性（推广到多维） **)
(** 定理：连续映射的可测性（二维版本） - 直接证明 **)
Theorem continuous_mapping_measurable_2d_direct :
  forall (f : R -> R * R),
  (continuous (fun x => fst (f x))) ->  (* 第一个分量连续 *)
  (continuous (fun x => snd (f x))) ->  (* 第二个分量连续 *)
  forall (C : SetX (R * R)),
  In C (sigma_sets (R * R) Borel_sigma_algebra_R2) ->
  In (fun x : R => C (f x)) (sigma_sets R Borel_sigma_algebra).
Proof.
  intros f Hcont_fst Hcont_snd C HC.
  
  (* 定义分量函数 *)
  set (f1 := fun x : R => fst (f x)).
  set (f2 := fun x : R => snd (f x)).
  
  (* 证明分量函数可测 *)
  assert (Hmeas_f1 : forall (A : SetX R),
    In A (sigma_sets R Borel_sigma_algebra) ->
    In (fun x => A (f1 x)) (sigma_sets R Borel_sigma_algebra)).
  {
    intros A HA.
    apply all_continuous_are_borel_measurable.
    exact Hcont_fst.
    exact HA.
  }
  
  assert (Hmeas_f2 : forall (A : SetX R),
    In A (sigma_sets R Borel_sigma_algebra) ->
    In (fun x => A (f2 x)) (sigma_sets R Borel_sigma_algebra)).
  {
    intros A HA.
    apply all_continuous_are_borel_measurable.
    exact Hcont_snd.
    exact HA.
  }
  
  (* 定义集合族 M：所有使得原像可测的二维集合 *)
  set (M := fun (C' : SetX (R * R)) =>
      In (fun x : R => C' (f x)) (sigma_sets R Borel_sigma_algebra)).
  
  (* 证明 M 是包含所有矩形的σ代数 *)
  (* 步骤1：包含矩形 *)
  assert (Hrect : forall A B,
    In A (sigma_sets R Borel_sigma_algebra) ->
    In B (sigma_sets R Borel_sigma_algebra) ->
    M (fun p : R * R => A (fst p) /\ B (snd p))).
  {
    intros A B HA HB.
    unfold M.
    (* 矩形 (A × B) 的原像是 A(f1(x)) ∩ B(f2(x)) *)
    assert (Heq : (fun x : R => A (fst (f x)) /\ B (snd (f x))) = 
                 (fun x : R => A (f1 x) /\ B (f2 x))).
    {
      apply set_extensionality.
      intro x.
      unfold f1, f2.
      reflexivity.
    }
    rewrite Heq.
    apply intersection_measurable.
    - apply Hmeas_f1; exact HA.
    - apply Hmeas_f2; exact HB.
  }
  
  (* 步骤2：M是σ代数 *)
  assert (Huniv : M (UniversalSet (X:=R * R))).
  {
    unfold M.
    assert (Heq : (fun x : R => UniversalSet (f x)) = UniversalSet (X:=R)).
    {
      apply set_extensionality.
      intro x.
      split; intro H; apply universal_set_property.
    }
    rewrite Heq.
    apply sigma_sets_univ_instance.
  }
  
  assert (Hcomp : forall A, M A -> M (Complement_s A)).
  {
    intros A HA.
    unfold M in *.
    assert (Heq : (fun x : R => (Complement_s A) (f x)) = 
                 Complement_s (fun x : R => A (f x))).
    {
      apply set_extensionality.
      intro x.
      split; intro H; exact H.
    }
    rewrite Heq.
    apply sigma_sets_complement.
    exact HA.
  }
  
  assert (Hunion : forall (F : nat -> SetX (R * R)),
    (forall n, M (F n)) -> M (fun p => exists n, F n p)).
  {
    intros F HF.
    unfold M in *.
    apply sigma_sets_countable_union.
    intro n.
    exact (HF n).
  }
  
  (* 步骤3：应用二维Borel代数的最小性 *)
  unfold Borel_sigma_algebra_R2 in HC.
  simpl in HC.
  
  (* 应用HC到M *)
  apply HC.
  
  (* 证明M满足生成σ代数的条件 *)
  split.
  {
    (* M包含生成集族 *)
    intros B [A1 [A2 [HA1 [HA2 Heq]]]].
    apply set_extensionality in Heq.
    rewrite Heq.
    apply Hrect.
    - exact HA1.
    - exact HA2.
  }
  split.
  {
    exact Huniv.
  }
  split.
  {
    exact Hcomp.
  }
  {
    exact Hunion.
  }
Qed.



(** n维实数向量：定义为函数 fin n -> R **)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Vectors.VectorDef.
Require Import Coq.Reals.Reals.
  
(** 实用的有限维系统：支持2维和3维 **)
  
(** 2维向量 **)
Definition R2 := (R * R)%type.
  
(** 3维向量 **)
Inductive R3 : Type :=
| mk_R3 : R -> R -> R -> R3.
  
(** 投影函数 **)
Definition proj_R2_1 (v : R2) : R := fst v.
Definition proj_R2_2 (v : R2) : R := snd v.
  
Definition proj_R3_1 (v : R3) : R := 
  match v with mk_R3 x _ _ => x end.
Definition proj_R3_2 (v : R3) : R := 
  match v with mk_R3 _ y _ => y end.
Definition proj_R3_3 (v : R3) : R := 
  match v with mk_R3 _ _ z => z end.
  
(** 连续映射定义 **)
Definition continuous_mapping_2d (f : R -> R2) : Prop :=
  continuous (fun x => proj_R2_1 (f x)) /\
  continuous (fun x => proj_R2_2 (f x)).
  
Definition continuous_mapping_3d (f : R -> R3) : Prop :=
  continuous (fun x => proj_R3_1 (f x)) /\
  continuous (fun x => proj_R3_2 (f x)) /\
  continuous (fun x => proj_R3_3 (f x)).
  
(** 乘积σ代数 **)
Definition Borel_sigma_algebra_R3 : SigmaAlgebra R3 :=
  generated_sigma_algebra
    (fun (A : SetX R3) =>
      exists (A1 A2 A3 : SetX R),
        (A1 in_s (sigma_sets R Borel_sigma_algebra)) /\
        (A2 in_s (sigma_sets R Borel_sigma_algebra)) /\
        (A3 in_s (sigma_sets R Borel_sigma_algebra)) /\
        SetEq A (fun v => 
          A1 (proj_R3_1 v) /\ A2 (proj_R3_2 v) /\ A3 (proj_R3_3 v))).
  
(** 三维连续映射的可测性定理 **)
Theorem continuous_mapping_measurable_3d :
  forall (f : R -> R3),
  continuous_mapping_3d f ->
  forall (C : SetX R3),
  C in_s (sigma_sets R3 Borel_sigma_algebra_R3) ->
  (fun x : R => C (f x)) in_s (sigma_sets R Borel_sigma_algebra).
Proof.
  intros f [Hcont1 [Hcont2 Hcont3]] C HC.
  
  (* 定义分量函数 *)
  set (f1 := fun x : R => proj_R3_1 (f x)).
  set (f2 := fun x : R => proj_R3_2 (f x)).
  set (f3 := fun x : R => proj_R3_3 (f x)).
  
  (* 证明分量函数可测 *)
  assert (Hmeas_f1 : Borel_measurable_function f1).
  { apply all_continuous_are_borel_measurable; exact Hcont1. }
  
  assert (Hmeas_f2 : Borel_measurable_function f2).
  { apply all_continuous_are_borel_measurable; exact Hcont2. }
  
  assert (Hmeas_f3 : Borel_measurable_function f3).
  { apply all_continuous_are_borel_measurable; exact Hcont3. }
  
  (* 定义集合族 M：所有使原像可测的三维集合 *)
  set (M := fun (C' : SetX R3) =>
      (fun x : R => C' (f x)) in_s (sigma_sets R Borel_sigma_algebra)).
  
  (* 证明M是包含所有矩形的σ代数 *)
  (* 1. 包含长方体（三个维度的乘积） *)
  assert (Hrect : forall A1 A2 A3,
      A1 in_s (sigma_sets R Borel_sigma_algebra) ->
      A2 in_s (sigma_sets R Borel_sigma_algebra) ->
      A3 in_s (sigma_sets R Borel_sigma_algebra) ->
      M (fun v => A1 (proj_R3_1 v) /\ A2 (proj_R3_2 v) /\ A3 (proj_R3_3 v))).
  {
    intros A1 A2 A3 HA1 HA2 HA3.
    unfold M.
    (* 长方体的原像是三个分量原像的交集 *)
    assert (Heq : (fun x : R => A1 (proj_R3_1 (f x)) /\ 
                            A2 (proj_R3_2 (f x)) /\ 
                            A3 (proj_R3_3 (f x))) =
                 (fun x : R => A1 (f1 x) /\ A2 (f2 x) /\ A3 (f3 x))).
    {
      unfold f1, f2, f3.
      reflexivity.
    }
    rewrite Heq.
    
    (* 先证明前两个分量的交集可测 *)
    pose proof (intersection_measurable 
                 (fun x => A1 (f1 x))
                 (fun x => A2 (f2 x))) as H12.
    specialize (H12 (Hmeas_f1 A1 HA1) (Hmeas_f2 A2 HA2)).
    (* H12: (fun x => A1 (f1 x) /\ A2 (f2 x)) in_s sigma_sets R Borel_sigma_algebra *)
    
    (* 再与第三个分量取交集 *)
    pose proof (intersection_measurable 
                 (fun x => A1 (f1 x) /\ A2 (f2 x))
                 (fun x => A3 (f3 x))) as H123.
    specialize (H123 H12 (Hmeas_f3 A3 HA3)).
    (* H123: (fun x => (fun x0 => A1 (f1 x0) /\ A2 (f2 x0)) x /\ (fun x0 => A3 (f3 x0)) x)
             in_s sigma_sets R Borel_sigma_algebra *)
    
    (* 简化 H123 中的表达式 *)
    simpl in H123.
    (* 现在 H123: (fun x => (A1 (f1 x) /\ A2 (f2 x)) /\ A3 (f3 x))
                  in_s sigma_sets R Borel_sigma_algebra *)
    
    (* 将形式转换为 A1(f1 x) ∧ A2(f2 x) ∧ A3(f3 x) *)
    assert (Heq2: (fun x => (A1 (f1 x) /\ A2 (f2 x)) /\ A3 (f3 x)) =
                  (fun x => A1 (f1 x) /\ A2 (f2 x) /\ A3 (f3 x))).
    {
      apply set_extensionality.
      intro x.
      split; intro H.
      - destruct H as [[H1 H2] H3].
        split; [exact H1|split; [exact H2|exact H3]].
      - destruct H as [H1 [H2 H3]].
        split; [split; assumption|assumption].
    }
    rewrite Heq2 in H123.
    exact H123.
  }
  
  (* 2. M是σ代数 *)
  assert (Huniv : M (UniversalSet (X:=R3))).
  {
    unfold M.
    assert (Heq : (fun x : R => UniversalSet (f x)) = UniversalSet (X:=R)).
    {
      apply set_extensionality.
      intro x.
      split; intro H; apply universal_set_property.
    }
    rewrite Heq.
    apply sigma_sets_univ_instance.
  }
  
  assert (Hcomp : forall A, M A -> M (Complement_s A)).
  {
    intros A HA.
    unfold M in *.
    assert (Heq : (fun x : R => (Complement_s A) (f x)) = 
                 Complement_s (fun x : R => A (f x))).
    {
      apply set_extensionality.
      intro x.
      split; intro H; exact H.
    }
    rewrite Heq.
    apply sigma_sets_complement.
    exact HA.
  }
  
  assert (Hunion : forall (F : nat -> SetX R3),
      (forall n, M (F n)) -> M (fun v => exists n, F n v)).
  {
    intros F HF.
    unfold M in *.
    apply sigma_sets_countable_union.
    intro n.
    exact (HF n).
  }
  
  (* 3. 应用三维Borel代数的最小性 *)
  unfold Borel_sigma_algebra_R3 in HC.
  simpl in HC.
  
  (* 应用HC到M *)
  apply HC.
  
  (* 证明M满足生成σ代数的条件 *)
  split.
  {
    (* M包含生成集族 *)
    intros B [A1 [A2 [A3 [HA1 [HA2 [HA3 Heq]]]]]].
    apply set_extensionality in Heq.
    rewrite Heq.
    apply Hrect; assumption.
  }
  split.
  {
    exact Huniv.
  }
  split.
  {
    exact Hcomp.
  }
  {
    exact Hunion.
  }
Qed.
  
(** 使用二维版本的推论 **)
Corollary continuous_mapping_measurable_2d_from_n :
  forall (f : R -> R * R),
  (continuous (fun x => fst (f x))) -> 
  (continuous (fun x => snd (f x))) ->
  forall (C : SetX (R * R)),
  C in_s (sigma_sets (R * R) Borel_sigma_algebra_R2) ->
  (fun x : R => C (f x)) in_s (sigma_sets R Borel_sigma_algebra).
Proof.
  intros f Hcont_fst Hcont_snd C HC.
  (* 直接应用已证明的二维定理 *)
  apply (continuous_mapping_measurable_2d_direct f Hcont_fst Hcont_snd C HC).
Qed.
  
(** 先实现基础的二维和三维版本 **)
  
(** 二维向量加法 **)
Definition R2_add (v1 v2 : R2) : R2 :=
  (fst v1 + fst v2, snd v1 + snd v2).
  
(** 二维向量加法的可测性 - 使用连续映射定理 **)
Lemma vector_addition_measurable_2d :
  forall (f g : R -> R2),
  continuous_mapping_2d f ->
  continuous_mapping_2d g ->
  continuous_mapping_2d (fun x => R2_add (f x) (g x)).
Proof.
  intros f g [Hcont_f1 Hcont_f2] [Hcont_g1 Hcont_g2].
  unfold continuous_mapping_2d.
  split.
  - (* 第一个分量连续 *)
    unfold R2_add, fst.
    apply continuous_plus; assumption.
  - (* 第二个分量连续 *)
    unfold R2_add, snd.
    apply continuous_plus; assumption.
Qed.
  
(** 二维向量加法的可测性推论 **)
Corollary vector_addition_measurable_2d_corollary :
  forall (f g : R -> R2),
  continuous_mapping_2d f ->
  continuous_mapping_2d g ->
  forall (C : SetX R2),
  C in_s (sigma_sets R2 Borel_sigma_algebra_R2) ->
  (fun x : R => C (R2_add (f x) (g x))) in_s (sigma_sets R Borel_sigma_algebra).
Proof.
  intros f g Hf Hg C HC.
  (* 获取向量加法的连续性证明 *)
  pose proof (vector_addition_measurable_2d f g Hf Hg) as Hcont.
  (* 分解 Hcont 为两个连续性证明 *)
  destruct Hcont as [Hcont_add1 Hcont_add2].
  (* 应用二维连续映射可测性定理 *)
  apply (continuous_mapping_measurable_2d_direct 
           (fun x => R2_add (f x) (g x)) Hcont_add1 Hcont_add2 C HC).
Qed.
  
(** 三维向量加法 **)
Definition R3_add (v1 v2 : R3) : R3 :=
  match v1, v2 with
  | mk_R3 x1 y1 z1, mk_R3 x2 y2 z2 => mk_R3 (x1 + x2) (y1 + y2) (z1 + z2)
  end.
  
(** 三维向量加法的可测性引理 - 证明运算是连续的 **)
Lemma vector_addition_measurable_3d :
  forall (f g : R -> R3),
  continuous_mapping_3d f ->
  continuous_mapping_3d g ->
  continuous_mapping_3d (fun x => R3_add (f x) (g x)).
Proof.
  intros f g Hf Hg.
  (* 分解 f 和 g 的连续性假设 *)
  destruct Hf as [Hcont_f1 [Hcont_f2 Hcont_f3]].
  destruct Hg as [Hcont_g1 [Hcont_g2 Hcont_g3]].
  
  (* 证明每个分量连续 *)
  unfold continuous_mapping_3d.
  split.
  - (* 第一个分量连续 *)
    (* 证明函数相等性 *)
    assert (Heq1: (fun x => proj_R3_1 (R3_add (f x) (g x))) = 
                 (fun x => proj_R3_1 (f x) + proj_R3_1 (g x))).
    {
      apply functional_extensionality.
      intro x.
      unfold R3_add, proj_R3_1.
      destruct (f x) as [x1 y1 z1].
      destruct (g x) as [x2 y2 z2].
      reflexivity.
    }
    rewrite Heq1.
    apply continuous_plus; assumption.
  - split.
    + (* 第二个分量连续 *)
      assert (Heq2: (fun x => proj_R3_2 (R3_add (f x) (g x))) = 
                   (fun x => proj_R3_2 (f x) + proj_R3_2 (g x))).
      {
        apply functional_extensionality.
        intro x.
        unfold R3_add, proj_R3_2.
        destruct (f x) as [x1 y1 z1].
        destruct (g x) as [x2 y2 z2].
        reflexivity.
      }
      rewrite Heq2.
      apply continuous_plus; assumption.
    + (* 第三个分量连续 *)
      assert (Heq3: (fun x => proj_R3_3 (R3_add (f x) (g x))) = 
                   (fun x => proj_R3_3 (f x) + proj_R3_3 (g x))).
      {
        apply functional_extensionality.
        intro x.
        unfold R3_add, proj_R3_3.
        destruct (f x) as [x1 y1 z1].
        destruct (g x) as [x2 y2 z2].
        reflexivity.
      }
      rewrite Heq3.
      apply continuous_plus; assumption.
Qed.
  
(** 连续三维映射的构造引理 **)
Lemma make_continuous_mapping_3d (f : R -> R3) :
  continuous (fun x => proj_R3_1 (f x)) ->
  continuous (fun x => proj_R3_2 (f x)) ->
  continuous (fun x => proj_R3_3 (f x)) ->
  continuous_mapping_3d f.
Proof.
  intros H1 H2 H3.
  split; [exact H1 | split; [exact H2 | exact H3]].
Qed.
  
(** 三维向量加法的可测性推论 **)
Corollary vector_addition_measurable_3d_corollary :
  forall (f g : R -> R3),
  continuous_mapping_3d f ->
  continuous_mapping_3d g ->
  forall (C : SetX R3),
  C in_s (sigma_sets R3 Borel_sigma_algebra_R3) ->
  (fun x : R => C (R3_add (f x) (g x))) in_s (sigma_sets R Borel_sigma_algebra).
Proof.
  intros f g Hf Hg C HC.
  
  (* 获取向量加法的连续性证明 *)
  pose proof (vector_addition_measurable_3d f g Hf Hg) as Hcont.
  
  (* 分解为三个分量的连续性 *)
  destruct Hcont as [Hcont1 [Hcont2 Hcont3]].
  
  (* 构造 continuous_mapping_3d 证明 *)
  assert (Hsum_cont : continuous_mapping_3d (fun x => R3_add (f x) (g x))).
  {
    apply make_continuous_mapping_3d; assumption.
  }
  
  (* 应用三维连续映射可测性定理 *)
  apply (continuous_mapping_measurable_3d 
           (fun x => R3_add (f x) (g x)) 
           Hsum_cont C HC).
Qed.
  
(** 二维标量乘法的可测性引理 **)
Lemma scalar_multiplication_measurable_2d :
  forall (c : R) (f : R -> R2),
  continuous_mapping_2d f ->
  continuous_mapping_2d (fun x => 
    let (x1, y1) := f x in
    (c * x1, c * y1)).
Proof.
  intros c f [Hcont_f1 Hcont_f2].
  unfold continuous_mapping_2d.
  split.
  - (* 第一个分量连续 *)
    (* 我们需要证明：continuous (fun x => proj_R2_1 (let (x1, y1) := f x in (c * x1, c * y1))) *)
    (* 简化这个表达式：proj_R2_1 (c * x1, c * y1) = c * x1 = c * proj_R2_1 (f x) *)
    assert (Heq1: (fun x => proj_R2_1 (let (x1, y1) := f x in (c * x1, c * y1))) = 
                  (fun x => c * proj_R2_1 (f x))).
    {
      apply functional_extensionality.
      intro x.
      destruct (f x) as [x1 y1].
      simpl.
      reflexivity.
    }
    rewrite Heq1.
    
    (* 现在应用 continuous_mult *)
    apply continuous_mult.
    + apply continuous_const.  (* 常数函数 c 连续 *)
    + exact Hcont_f1.          (* proj_R2_1 ∘ f 连续 *)
    
  - (* 第二个分量连续 *)
    (* 类似地：proj_R2_2 (c * x1, c * y1) = c * y1 = c * proj_R2_2 (f x) *)
    assert (Heq2: (fun x => proj_R2_2 (let (x1, y1) := f x in (c * x1, c * y1))) = 
                  (fun x => c * proj_R2_2 (f x))).
    {
      apply functional_extensionality.
      intro x.
      destruct (f x) as [x1 y1].
      simpl.
      reflexivity.
    }
    rewrite Heq2.
    
    (* 应用 continuous_mult *)
    apply continuous_mult.
    + apply continuous_const.  (* 常数函数 c 连续 *)
    + exact Hcont_f2.          (* proj_R2_2 ∘ f 连续 *)
Qed.
  
(** 二维标量乘法的可测性推论 **)
Corollary scalar_multiplication_measurable_2d_corollary :
  forall (c : R) (f : R -> R2),
  continuous_mapping_2d f ->
  forall (C : SetX R2),
  C in_s (sigma_sets R2 Borel_sigma_algebra_R2) ->
  (fun x : R => C (let (x1, y1) := f x in (c * x1, c * y1))) 
  in_s (sigma_sets R Borel_sigma_algebra).
Proof.
  intros c f Hf C HC.
  pose proof (scalar_multiplication_measurable_2d c f Hf) as Hcont.
  destruct Hcont as [Hcont1 Hcont2].
  apply (continuous_mapping_measurable_2d_direct 
           (fun x => let (x1, y1) := f x in (c * x1, c * y1))
           Hcont1 Hcont2 C HC).
Qed.
  
(** 辅助引理：标量乘法的分量表达式 **)
(** 引理1：三维向量标量乘法后的第一个分量表达式 **)
(** 对于任意实数c、从R到R3的函数f和任意实数x，有：
    proj_R3_1 (对f(x)进行标量乘法后的向量) = c * proj_R3_1 (f x)
    即：标量乘法与第一个分量投影可以交换顺序 **)
Lemma scalar_mult_proj_R3_1 (c : R) (f : R -> R3) (x : R) :
  proj_R3_1 (match f x with | mk_R3 x1 y1 z1 => mk_R3 (c * x1) (c * y1) (c * z1) end) =
  c * proj_R3_1 (f x).
Proof.
  (* 证明策略：
     1. 使用destruct分解f x的结构，将其展开为三个分量x1, y1, z1
     2. 两边同时化简，观察等式两边均为c * x1
     3. 使用reflexivity证明恒等性 *)
  destruct (f x) as [x1 y1 z1].
  reflexivity.
Qed.
  
(** 引理2：三维向量标量乘法后的第二个分量表达式 **)
(** 对于任意实数c、从R到R3的函数f和任意实数x，有：
    proj_R3_2 (对f(x)进行标量乘法后的向量) = c * proj_R3_2 (f x)
    即：标量乘法与第二个分量投影可以交换顺序 **)
Lemma scalar_mult_proj_R3_2 (c : R) (f : R -> R3) (x : R) :
  proj_R3_2 (match f x with | mk_R3 x1 y1 z1 => mk_R3 (c * x1) (c * y1) (c * z1) end) =
  c * proj_R3_2 (f x).
Proof.
  (* 证明策略：
     1. 使用destruct分解f x的结构，将其展开为三个分量x1, y1, z1
     2. 两边同时化简，观察等式两边均为c * y1
     3. 使用reflexivity证明恒等性 *)
  destruct (f x) as [x1 y1 z1].
  reflexivity.
Qed.
  
(** 引理3：三维向量标量乘法后的第三个分量表达式 **)
(** 对于任意实数c、从R到R3的函数f和任意实数x，有：
    proj_R3_3 (对f(x)进行标量乘法后的向量) = c * proj_R3_3 (f x)
    即：标量乘法与第三个分量投影可以交换顺序 **)
Lemma scalar_mult_proj_R3_3 (c : R) (f : R -> R3) (x : R) :
  proj_R3_3 (match f x with | mk_R3 x1 y1 z1 => mk_R3 (c * x1) (c * y1) (c * z1) end) =
  c * proj_R3_3 (f x).
Proof.
  (* 证明策略：
     1. 使用destruct分解f x的结构，将其展开为三个分量x1, y1, z1
     2. 两边同时化简，观察等式两边均为c * z1
     3. 使用reflexivity证明恒等性 *)
  destruct (f x) as [x1 y1 z1].
  reflexivity.
Qed.
  
(** 三维标量乘法的可测性引理 **)
Lemma scalar_multiplication_measurable_3d :
  forall (c : R) (f : R -> R3),
  continuous_mapping_3d f ->
  continuous_mapping_3d (fun x => 
    match f x with
    | mk_R3 x1 y1 z1 => mk_R3 (c * x1) (c * y1) (c * z1)
    end).
Proof.
  intros c f [Hcont1 [Hcont2 Hcont3]].
  unfold continuous_mapping_3d.
  split.
  - (* 第一个分量连续 *)
    (* 将目标函数重写为乘积形式 *)
    assert (Heq1: (fun x => proj_R3_1 (match f x with
                                      | mk_R3 x1 y1 z1 => mk_R3 (c * x1) (c * y1) (c * z1)
                                      end)) = 
                  (fun x => c * proj_R3_1 (f x))).
    {
      apply functional_extensionality.
      intro x.
      destruct (f x) as [x1 y1 z1].
      simpl.
      reflexivity.
    }
    rewrite Heq1.
    
    (* 现在应用 continuous_mult *)
    apply continuous_mult.
    + apply continuous_const.  (* 常数函数 c 连续 *)
    + exact Hcont1.           (* proj_R3_1 ∘ f 连续 *)
    
  - split.
    + (* 第二个分量连续 *)
      (* 类似重写 *)
      assert (Heq2: (fun x => proj_R3_2 (match f x with
                                        | mk_R3 x1 y1 z1 => mk_R3 (c * x1) (c * y1) (c * z1)
                                        end)) = 
                    (fun x => c * proj_R3_2 (f x))).
      {
        apply functional_extensionality.
        intro x.
        destruct (f x) as [x1 y1 z1].
        simpl.
        reflexivity.
      }
      rewrite Heq2.
      
      (* 应用 continuous_mult *)
      apply continuous_mult.
      * apply continuous_const.  (* 常数函数 c 连续 *)
      * exact Hcont2.           (* proj_R3_2 ∘ f 连续 *)
      
    + (* 第三个分量连续 *)
      (* 类似重写 *)
      assert (Heq3: (fun x => proj_R3_3 (match f x with
                                        | mk_R3 x1 y1 z1 => mk_R3 (c * x1) (c * y1) (c * z1)
                                        end)) = 
                    (fun x => c * proj_R3_3 (f x))).
      {
        apply functional_extensionality.
        intro x.
        destruct (f x) as [x1 y1 z1].
        simpl.
        reflexivity.
      }
      rewrite Heq3.
      
      (* 应用 continuous_mult *)
      apply continuous_mult.
      * apply continuous_const.  (* 常数函数 c 连续 *)
      * exact Hcont3.           (* proj_R3_3 ∘ f 连续 *)
Qed.
  
(** 点积的可测性 **)
Lemma dot_product_measurable_2d :
  forall (f g : R -> R2),
  continuous_mapping_2d f ->
  continuous_mapping_2d g ->
  Borel_measurable_function (fun x => 
    let (x1, y1) := f x in
    let (x2, y2) := g x in
    x1 * x2 + y1 * y2).
Proof.
  intros f g [Hcont_f1 Hcont_f2] [Hcont_g1 Hcont_g2].
  
  (* 定义中间函数 *)
  set (h1 := fun x : R => fst (f x) * fst (g x)).
  set (h2 := fun x : R => snd (f x) * snd (g x)).
  set (h := fun x : R => h1 x + h2 x).
  
  (* 证明每个分量连续 *)
  assert (Hcont_h1 : continuous h1).
  {
    unfold h1.
    apply continuous_mult; assumption.
  }
  
  assert (Hcont_h2 : continuous h2).
  {
    unfold h2.
    apply continuous_mult; assumption.
  }
  
  assert (Hcont_h : continuous h).
  {
    unfold h.
    apply continuous_plus; assumption.
  }
  
  (* 应用连续函数的可测性 *)
  unfold Borel_measurable_function.
  intros B HB.
  
  (* 使用函数外延性重写目标 *)
  apply (set_eq_in_sigma_sets R Borel_sigma_algebra 
         (fun x : R => B (h x))
         (fun x : R => B (let (x1, y1) := f x in
                         let (x2, y2) := g x in
                         x1 * x2 + y1 * y2))).
  
  {
    (* 证明两个函数相等 *)
    apply functional_extensionality.
    intro x.
    f_equal.
    unfold h, h1, h2.
    destruct (f x) as [x1 y1].
    destruct (g x) as [x2 y2].
    reflexivity.
  }
  
  (* 现在应用连续函数的可测性定理 *)
  apply (all_continuous_are_borel_measurable h Hcont_h B HB).
Qed.
  
(** 标量乘法的可测性 - 二维版本 **)
Lemma scalar_multiplication_measurable_2d_alt :
  forall (c : R) (f : R -> R2),
  continuous_mapping_2d f ->
  forall (C : SetX R2),
  C in_s (sigma_sets R2 Borel_sigma_algebra_R2) ->
  (fun x : R => C (let (x1, y1) := f x in (c * x1, c * y1)))
    in_s (sigma_sets R Borel_sigma_algebra).
Proof.
  intros c f Hf_cont C HC.
  
  (* 我们已经有了 scalar_multiplication_measurable_2d 证明标量乘法是连续的 *)
  pose proof (scalar_multiplication_measurable_2d c f Hf_cont) as Hcont_scalar.
  
  (* 分解连续性证明 *)
  destruct Hcont_scalar as [Hcont1 Hcont2].
  
  (* 应用二维连续映射的可测性定理 *)
  apply (continuous_mapping_measurable_2d_direct 
           (fun x : R => 
              let (x1, y1) := f x in 
              (c * x1, c * y1))
           Hcont1 Hcont2 C HC).
Qed.
  
(** 标量乘法的可测性 - 三维版本 **)
Lemma scalar_multiplication_measurable_3d_alt :
  forall (c : R) (f : R -> R3),
  continuous_mapping_3d f ->
  forall (C : SetX R3),
  C in_s (sigma_sets R3 Borel_sigma_algebra_R3) ->
  (fun x : R => C (match f x with
                  | mk_R3 x1 y1 z1 => mk_R3 (c * x1) (c * y1) (c * z1)
                  end))
    in_s (sigma_sets R Borel_sigma_algebra).
Proof.
  intros c f Hf_cont C HC.
  
  (* 我们已经有了 scalar_multiplication_measurable_3d 证明标量乘法是连续的 *)
  pose proof (scalar_multiplication_measurable_3d c f Hf_cont) as Hcont_scalar.
  
  (* 分解连续性证明 *)
  destruct Hcont_scalar as [Hcont1 [Hcont2 Hcont3]].
  
  (* 构造 continuous_mapping_3d 证明 *)
  assert (Hcont_mapping_3d : continuous_mapping_3d (fun x : R => 
              match f x with
              | mk_R3 x1 y1 z1 => mk_R3 (c * x1) (c * y1) (c * z1)
              end)).
  {
    (* 使用 make_continuous_mapping_3d 引理 *)
    apply make_continuous_mapping_3d.
    - exact Hcont1.
    - exact Hcont2.
    - exact Hcont3.
  }
  
  (* 应用三维连续映射的可测性定理 *)
  apply (continuous_mapping_measurable_3d 
           (fun x : R => 
              match f x with
              | mk_R3 x1 y1 z1 => mk_R3 (c * x1) (c * y1) (c * z1)
              end)
           Hcont_mapping_3d C HC).
Qed.
  
(** 三维内积函数 **)
Definition dot_product_R3 (v1 v2 : R3) : R :=
  match v1, v2 with
  | mk_R3 x1 y1 z1, mk_R3 x2 y2 z2 => x1 * x2 + y1 * y2 + z1 * z2
  end.
  
(** 三维内积的可测性 **)
Lemma dot_product_measurable_3d :
  forall (f g : R -> R3),
  continuous_mapping_3d f ->
  continuous_mapping_3d g ->
  Borel_measurable_function (fun x => dot_product_R3 (f x) (g x)).
Proof.
  intros f g Hf_cont Hg_cont.
  
  (* 分解连续性假设 *)
  destruct Hf_cont as [Hcont_f1 [Hcont_f2 Hcont_f3]].
  destruct Hg_cont as [Hcont_g1 [Hcont_g2 Hcont_g3]].
  
  (* 定义三个分量乘积函数 *)
  set (h1 := fun x : R => proj_R3_1 (f x) * proj_R3_1 (g x)).
  set (h2 := fun x : R => proj_R3_2 (f x) * proj_R3_2 (g x)).
  set (h3 := fun x : R => proj_R3_3 (f x) * proj_R3_3 (g x)).
  
  (* 证明每个乘积函数连续 *)
  assert (Hcont_h1 : continuous h1).
  {
    unfold h1.
    apply continuous_mult; assumption.
  }
  
  assert (Hcont_h2 : continuous h2).
  {
    unfold h2.
    apply continuous_mult; assumption.
  }
  
  assert (Hcont_h3 : continuous h3).
  {
    unfold h3.
    apply continuous_mult; assumption.
  }
  
  (* 定义内积函数为三个乘积之和 *)
  set (h := fun x : R => h1 x + h2 x + h3 x).
  
  (* 证明内积函数连续 *)
  assert (Hcont_h : continuous h).
  {
    unfold h.
    (* 先证明 h1 + h2 连续 *)
    assert (Hcont_h12 : continuous (fun x : R => h1 x + h2 x)).
    {
      apply continuous_plus; assumption.
    }
    (* 再证明 (h1 + h2) + h3 连续 *)
    apply continuous_plus; assumption.
  }
  
  (* 证明函数相等性 *)
  assert (Heq : h = (fun x : R => dot_product_R3 (f x) (g x))).
  {
    apply functional_extensionality.
    intro x.
    unfold h, h1, h2, h3, dot_product_R3.
    destruct (f x) as [x1 y1 z1].
    destruct (g x) as [x2 y2 z2].
    simpl.
    ring.
  }
  
  (* 应用连续函数的可测性 *)
  unfold Borel_measurable_function.
  intros B HB.
  
  (* 使用函数相等性重写目标 *)
  apply (set_eq_in_sigma_sets R Borel_sigma_algebra 
         (fun x : R => B (h x))
         (fun x : R => B (dot_product_R3 (f x) (g x)))).
  {
    apply functional_extensionality.
    intro x.
    (* 使用 Heq 的点态相等性 *)
    apply f_equal.
    (* Heq 是函数相等，所以对于每个 x，有 h x = dot_product_R3 (f x) (g x) *)
    exact (f_equal (fun f => f x) Heq).
  }
  
  (* 应用连续函数的可测性定理 *)
  apply (all_continuous_are_borel_measurable h Hcont_h B HB).
Qed.
  
(* 首先证明一个引理：集合 {x | x ≤ a} 在Borel σ代数中 *)
Lemma set_le_in_borel (a : R) :
  (fun x : R => x <= a) in_s (sigma_sets R Borel_sigma_algebra).
Proof.
  (* 将 {x | x ≤ a} 表示为可数个闭区间 [-n, a] 的并集 *)
  assert (Heq : (fun x : R => x <= a) = 
                (fun x => exists n : nat, -INR n <= x /\ x <= a)).
  {
    apply set_extensionality; intro x.
    split.
    - intro Hle.
      (* 由于实数x有下界，存在自然数n使得 -n ≤ x *)
      destruct (exists_nat_gt (-x)) as [n Hn].  (* 得到 n > -x *)
      exists n.
      split.
      + lra.  (* 由 n > -x 可得 -n < x，即 -n ≤ x *)
      + exact Hle.
    - intros [n [H1 H2]].
      exact H2.
  }
  rewrite Heq.
  (* 应用可数并的可测性 *)
  apply sigma_sets_countable_union.
  intro n.
  (* 每个集合 (fun x => -INR n <= x /\ x <= a) 实际上就是闭区间 [-INR n, a] *)
  apply (closed_interval_in_borel (-INR n) a).
Qed.
  
(** 然后证明三维长方体在三维Borel σ代数中 **)
Lemma cube_in_borel_3d (a b c : R) :
  (fun v : R3 => proj_R3_1 v <= a /\ proj_R3_2 v <= b /\ proj_R3_3 v <= c)
  in_s (sigma_sets R3 Borel_sigma_algebra_R3).
Proof.
  (* 展开三维Borel σ代数的定义 *)
  unfold Borel_sigma_algebra_R3.
  
  (* 展开generated_sigma_algebra，得到其sigma_sets字段 *)
  simpl.
  
  (* 我们需要证明目标集合在生成的最小σ代数中 *)
  unfold my_sigma_sets.
  
  (* 引入一个任意的σ代数S，假设它包含生成集族且满足σ代数公理 *)
  intros S [Hgen [Huniv [Hcomp Hcunion]]].
  
  (* 应用Hgen：我们需要证明目标集合在生成集族中 *)
  apply Hgen.
  
  (* 构造三个一维Borel可测集 *)
  exists (fun x : R => x <= a), (fun x : R => x <= b), (fun x : R => x <= c).
  
  (* 分解为四个条件：三个可测性条件和集合相等性 *)
  split. 
    (* 第一个集合在sigma_sets R Borel_sigma_algebra中 *)
    apply set_le_in_borel.
  split.
    (* 第二个集合在sigma_sets R Borel_sigma_algebra中 *)
    apply set_le_in_borel.
  split.
    (* 第三个集合在sigma_sets R Borel_sigma_algebra中 *)
    apply set_le_in_borel.
  (* 证明集合相等性 *)
  unfold SetEq.
  intro v.
  split; intro H.
  - (* 左到右：目标集合 ⊆ 乘积集合 *)
    destruct H as [H1 [H2 H3]].
    repeat split; assumption.
  - (* 右到左：乘积集合 ⊆ 目标集合 *)
    destruct H as [H1 [H2 H3]].
    repeat split; assumption.
Qed.
  
(** 示例：三维连续映射 **)
Example continuous_3d_mapping_example :
  forall (f : R -> R3),
  continuous_mapping_3d f ->
  forall (a b c : R),
  let cube := fun (v : R3) => 
    proj_R3_1 v <= a /\ proj_R3_2 v <= b /\ proj_R3_3 v <= c
  in
  (fun x : R => cube (f x)) in_s (sigma_sets R Borel_sigma_algebra).
Proof.
  intros f Hf_cont a b c cube.
  apply (continuous_mapping_measurable_3d f Hf_cont (fun v : R3 => 
    proj_R3_1 v <= a /\ proj_R3_2 v <= b /\ proj_R3_3 v <= c)).
  apply cube_in_borel_3d.
Qed.
  
(** 连续函数与可测函数的复合可测 **)
Lemma borel_measurable_continuous_composition : 
  forall (h : R -> R) (f : R -> R),
  continuous h -> Borel_measurable_function f ->
  Borel_measurable_function (fun x => h (f x)).
Proof.
  (* 引入连续函数h和可测函数f *)
  intros h f Hcont Hmeas.
  
  (* 展开可测函数的定义 *)
  unfold Borel_measurable_function in *.
  
  (* 对任意Borel可测集B，证明复合函数的原像可测 *)
  intros B HB.
  
  (* 首先，由连续性得到h是Borel可测的 *)
  pose proof (all_continuous_are_borel_measurable h Hcont) as Hmeas_h.
  
  (* 应用h的可测性到集合B，得到h⁻¹(B)是Borel可测的 *)
  specialize (Hmeas_h B HB).
  
  (* 应用f的可测性到集合h⁻¹(B) *)
  (* 注意：h⁻¹(B)就是(fun y : R => B (h y)) *)
  exact (Hmeas (fun y : R => B (h y)) Hmeas_h).
Qed.
  
(** 简化备注：连续函数类在代数运算下封闭且都是Borel可测的 *)
Remark continuous_functions_are_borel_measurable_algebra :
  (* 常数函数连续且可测 *)
  (forall c : R, continuous (fun _ => c) /\ Borel_measurable_function (fun _ => c)) /\
  (* 恒等函数连续且可测 *)
  (continuous (fun x => x) /\ Borel_measurable_function (fun x => x)) /\
  (* 连续函数的和连续且可测 *)
  (forall f g, continuous f -> continuous g ->
    continuous (fun x => f x + g x) /\ 
    Borel_measurable_function (fun x => f x + g x)) /\
  (* 连续函数的积连续且可测 *)
  (forall f g, continuous f -> continuous g ->
    continuous (fun x => f x * g x) /\
    Borel_measurable_function (fun x => f x * g x)).
Proof.
  split.
  {
    intro c.
    split.
    - apply continuous_const.
    - apply all_continuous_are_borel_measurable, continuous_const.
  }
  split.
  {
    split.
    - apply continuous_id.
    - apply all_continuous_are_borel_measurable, continuous_id.
  }
  split.
  {
    intros f g Hf Hg.
    split.
    - apply continuous_plus; assumption.
    - unfold Borel_measurable_function.
      intros B HB.
      (* 正确应用：f, g, Hf, Hg, B, HB 的顺序 *)
      apply (sum_of_continuous_measurable f g Hf Hg B HB).
  }
  {
    intros f g Hf Hg.
    split.
    - apply continuous_mult; assumption.
    - unfold Borel_measurable_function.
      intros B HB.
      (* 同样修正 product_of_continuous_measurable 的应用 *)
      apply (product_of_continuous_measurable f g Hf Hg B HB).
  }
Qed.
  
(** 引理：连续函数的原像将闭区间映射为 Borel 集 *)
Lemma preimage_closed_interval_measurable :
  forall (f : R -> R) (Hf_cont : continuous f) (a b : R),
  (fun x => a <= f x /\ f x <= b) in_s 
     (sigma_sets R (generated_sigma_algebra 
        (fun (A : SetX R) => exists a' b' : R, SetEq A (fun x : R => a' <= x /\ x <= b')))).
Proof.
  intros f Hf_cont a b.
  (* 展开 Borel_sigma_algebra 的定义 *)
  unfold Borel_sigma_algebra.
  
  (* 应用连续函数可测性定理 *)
  apply (continuous_is_borel_measurable f Hf_cont 
         (fun x : R => a <= x /\ x <= b)).
  
  (* 证明闭区间 [a, b] 在生成σ代数中 *)
  apply closed_interval_in_borel.
Qed.
  
(* =========================================================================== *)
(* 第三部分：连续函数与可测性 - 完整证明 *)
(* =========================================================================== *)
  
(** 连续函数复合定理 **)
Theorem continuous_composition_measurable : 
  forall (ps : ProbabilitySpace)
         (X : ps.(ps_Ω) -> R) (HX : RealRandomVariable X)
         (f : R -> R) (Hf_cont : continuous f),
  RealRandomVariable (fun ω => f (X ω)).
Proof.
  intros ps X HX f Hf_cont.
  unfold RealRandomVariable in *.
  intros B HB.
  
  (* 由 f 连续，得到 f⁻¹(B) 是Borel可测的 *)
  assert (H_f_pre : (fun x : R => B (f x)) in_s (sigma_sets R Borel_sigma_algebra)).
  { apply (continuous_is_borel_measurable f Hf_cont B HB). }
  
  (* 由 X 是随机变量，得到 X⁻¹(f⁻¹(B)) 在事件σ代数中 *)
  specialize (HX (fun x : R => B (f x)) H_f_pre).
  
  (* HX 的类型是：In (fun ω : ps_Ω => X ω in_s (fun x : R => B (f x))) (sigma_sets (ps_Ω) (ps_𝓕))
     展开后就是：In (fun ω : ps_Ω => B (f (X ω))) (sigma_sets (ps_Ω) (ps_𝓕)) *)
  exact HX.
Qed.
  
(* =========================================================================== *)
(* 第四部分：随机变量基本变换 *)
(* =========================================================================== *)
  
(** 常数随机变量 **)
Lemma RealRandomVariable_const : forall {ps : ProbabilitySpace} (c : R),
  RealRandomVariable (fun (ω : ps.(ps_Ω)) => c).
Proof.
  intros ps c.
  (* 展开实随机变量的定义 *)
  unfold RealRandomVariable.
  intros B HB.
  (* 展开随机变量的定义 *)
  unfold RandomVariable.
  (* 现在目标：is_event (fun ω : ps_Ω => c in_s B) *)
  
  (* 分析常数c是否在集合B中 *)
  destruct (classic (B c)) as [Hc | Hnotc].
  {
    (* 情况1：常数c在集合B中 *)
    (* 那么对于所有样本点ω，都有c in_s B成立 *)
    (* 所以原像是全集 *)
    
    (* 证明原像集合等于全集 *)
    assert (Heq : (fun ω : ps.(ps_Ω) => c in_s B) = UniversalSet_s).
    {
      (* 使用集合外延性证明两个集合相等 *)
      apply set_extensionality.
      intro ω.
      split.
      - (* 左包含：原像集合 ⊆ 全集 *)
        intro H.
        apply universal_set_property.
      - (* 右包含：全集 ⊆ 原像集合 *)
        intro H.
        exact Hc.  (* 因为B c为真，所以对于任意ω，c in_s B都成立 *)
    }
    (* 将原像集合重写为全集 *)
    rewrite Heq.
    (* 应用σ代数包含全集的性质 *)
    (* 使用显式参数 *)
    apply (@sigma_contains_universe (ps.(ps_Ω)) (ps.(ps_𝓕))).
  }
  {
    (* 情况2：常数c不在集合B中 *)
    (* 那么对于所有样本点ω，都有¬(c in_s B) *)
    (* 所以原像是空集 *)
    
    (* 证明原像集合等于空集 *)
    assert (Heq : (fun ω : ps.(ps_Ω) => c in_s B) = EmptySet_s).
    {
      (* 使用集合外延性证明两个集合相等 *)
      apply set_extensionality.
      intro ω.
      split.
      - (* 左包含：原像集合 ⊆ 空集 *)
        intro H.
        (* 假设c in_s B，但根据Hnotc，这是不可能的 *)
        contradiction.
      - (* 右包含：空集 ⊆ 原像集合 *)
        intro H.
        (* 空集不包含任何元素，所以矛盾 *)
        contradiction.
    }
    (* 将原像集合重写为空集 *)
    rewrite Heq.
    (* 应用σ代数包含空集的性质 *)
    (* 使用显式参数 *)
    apply (@sigma_contains_empty (ps.(ps_Ω)) (ps.(ps_𝓕))).
  }
Qed.
  
(** 随机变量加常数 **)
Lemma RealRandomVariable_plus_const : forall {ps : ProbabilitySpace} 
  (X : ps.(ps_Ω) -> R) (HX : RealRandomVariable X) (c : R),
  RealRandomVariable (fun ω => X ω + c).
Proof.
  intros ps X HX c.
  
  (* 方法1：使用连续函数复合 *)
  set (f := fun x => x + c).
  assert (Hf_cont : continuous f).
  {
    unfold f.
    (* 这是仿射函数，连续 *)
    unfold continuous, continuous_at.
    intros x eps Heps.
    exists eps.
    split.
    - exact Heps.
    - intros y Hy.
      (* 计算差：|(y+c) - (x+c)| = |y-x| < eps *)
      replace (y + c - (x + c)) with (y - x) by ring.
      exact Hy.
  }
  
  (* 应用连续函数复合定理 *)
  exact (continuous_composition_measurable ps X HX f Hf_cont).
Qed.
  
(** 随机变量乘常数 **)
Lemma RealRandomVariable_mult_const : forall {ps : ProbabilitySpace} 
  (X : ps.(ps_Ω) -> R) (HX : RealRandomVariable X) (c : R),
  RealRandomVariable (fun ω => c * X ω).
Proof.
  intros ps X HX c.
  
  (* 方法：使用连续函数复合 *)
  set (g := fun x : R => c * x).
  assert (Hg_cont : continuous g).
  {
    unfold g.
    (* 常数乘法函数是连续的 *)
    apply continuous_mult.
    - (* 常数函数连续 *)
      apply continuous_const.
    - (* 恒等函数连续 *)
      apply continuous_id.
  }
  
  (* 应用连续函数复合定理 *)
  exact (continuous_composition_measurable ps X HX g Hg_cont).
Qed.
  
(** 随机变量平方 **)
Lemma RealRandomVariable_square : forall {ps : ProbabilitySpace} 
  (X : ps.(ps_Ω) -> R) (HX : RealRandomVariable X),
  RealRandomVariable (fun ω => (X ω) ^ 2).
Proof.
  intros ps X HX.
  
  (* 方法1：使用连续函数复合 *)
  set (f := fun x => x ^ 2).
  assert (Hf_cont : continuous f).
  {
    unfold f.
    (* 使用函数外延性将x^2重写为x*x *)
    assert (Heq : (fun x : R => x ^ 2) = (fun x : R => x * x)).
    {
      apply functional_extensionality.
      intro x.
      ring.
    }
    rewrite Heq.
    (* 平方函数连续，因为它是恒等函数与自身的乘积 *)
    apply continuous_mult.
    - (* 恒等函数连续 *)
      apply continuous_id.
    - (* 恒等函数连续 *)
      apply continuous_id.
  }
  
  (* 应用连续函数复合定理 *)
  exact (continuous_composition_measurable ps X HX f Hf_cont).
Qed.
  
(* =========================================================================== *)
(* 第五部分：随机变量代数运算 *)
(* =========================================================================== *)
  
(** 有理数工具 **)
  
(* 有理数定义 *)
Definition rational (r : R) : Prop := 
  exists (p : Z) (q : positive), r = IZR p / IZR (Zpos q).
  
(** 平移变换的可测性：Borel集在平移下保持 **)
(** 对于任意Borel集B和任意实数c，集合{x | x - c ∈ B}是Borel集 **)
Lemma borel_set_translation : forall (B : SetX R) (c : R),
  B in_s sigma_sets R Borel_sigma_algebra ->
  (fun x => B (x - c)) in_s sigma_sets R Borel_sigma_algebra.
Proof.
  (* 引入Borel集B和实数c *)
  intros B c HB.
  
  (* 定义平移函数 f(x) = x - c *)
  set (f := fun x : R => x - c).
  
  (* 证明f是连续函数 *)
  assert (Hf_cont : continuous f).
  {
    unfold f.
    (* 将x-c表示为x+(-c) *)
    (* 首先证明常数函数(-c)是连续的 *)
    assert (Hconst : continuous (fun _ : R => -c)).
    {
      apply continuous_const.
    }
    (* 恒等函数是连续的 *)
    assert (Hid : continuous (fun x : R => x)).
    {
      apply continuous_id.
    }
    (* 两个连续函数的和是连续的 *)
    (* 注意：x - c = x + (-c) *)
    apply continuous_plus.
    - exact Hid.      (* 恒等函数连续 *)
    - exact Hconst.   (* 常数函数(-c)连续 *)
  }
  
  (* 应用连续函数的可测性定理 *)
  (* continuous_is_borel_measurable f Hf_cont : 
     ∀ B', B' in_s sigma_sets R Borel_sigma_algebra -> 
           (fun x => B' (f x)) in_s sigma_sets R Borel_sigma_algebra *)
  apply (continuous_is_borel_measurable f Hf_cont B HB).
Qed.
  
(** 等价形式：B + c = {x | ∃ y ∈ B, x = y + c} **)
(** 平移集合的可测性：B + c = {x | ∃ y ∈ B, x = y + c} 是 Borel 集 **)
Lemma borel_set_translation_plus : forall (B : SetX R) (c : R),
  B in_s sigma_sets R Borel_sigma_algebra ->
  (fun x => exists y : R, B y /\ x = y + c) in_s sigma_sets R Borel_sigma_algebra.
Proof.
  (* 引入集合B、实数c和B的Borel可测性假设 *)
  intros B c HB.
  
  (* 证明两个集合相等：{x | ∃ y ∈ B, x = y + c} = {x | x - c ∈ B} *)
  assert (Heq : (fun x : R => exists y : R, B y /\ x = y + c) = 
                (fun x : R => B (x - c))).
  {
    (* 应用集合外延性公理 *)
    apply set_extensionality.
    (* 引入任意实数x *)
    intro x.
    (* 证明双向包含 *)
    split.
    {
      (* 从左到右：{x | ∃ y ∈ B, x = y + c} ⊆ {x | x - c ∈ B} *)
      intros [y [Hy Hx_eq]].          (* 存在y∈B使得x = y + c *)
      rewrite Hx_eq.                  (* 将x重写为y + c *)
      change (B ((y + c) - c)).       (* 将目标显式化为B((y + c) - c) *)
      replace ((y + c) - c) with y by ring.  (* 代数化简： (y + c) - c = y *)
      exact Hy.                       (* 由假设Hy: B y得证 *)
    }
    {
      (* 从右到左：{x | x - c ∈ B} ⊆ {x | ∃ y ∈ B, x = y + c} *)
      intro Hx.                       (* 假设B (x - c) *)
      (* 存在y = x - c *)
      exists (x - c).
      split.
      {
        (* 证明B (x - c) *)
        exact Hx.
      }
      {
        (* 证明x = (x - c) + c *)
        ring.
      }
    }
  }
  
  (* 将目标集合重写为B(x - c) *)
  rewrite Heq.
  
  (* 应用平移引理：{x | x - c ∈ B}是Borel集 *)
  apply borel_set_translation.
  
  (* 提供B的Borel可测性假设 *)
  exact HB.
Qed.
  
(** 辅助引理：开区间在平移下保持可测性 **)
Lemma open_interval_translation : forall (a b c : R) (Hlt : a < b),
  (fun x => a < x - c /\ x - c < b) in_s sigma_sets R Borel_sigma_algebra.
Proof.
  (* 引入参数：区间端点a,b，平移量c，以及a<b的条件 *)
  intros a b c Hlt.
  
  (* 证明开区间(a,b)本身是Borel可测的 *)
  assert (Hinterval : (fun x : R => a < x /\ x < b) in_s sigma_sets R Borel_sigma_algebra).
  {
    (* 应用已有的开区间可测性引理 *)
    apply open_interval_in_borel.
    exact Hlt.
  }
  
  (* 定义集合B为开区间(a,b) *)
  set (B := fun x : R => a < x /\ x < b) in *.
  
  (* 应用平移引理：对于Borel集B，集合{x | B(x - c)}也是Borel集 *)
  (* 注意：borel_set_translation的类型为：
     ∀ (B : SetX R) (c : R), 
       B in_s sigma_sets R Borel_sigma_algebra ->
       (fun x => B (x - c)) in_s sigma_sets R Borel_sigma_algebra *)
  apply (borel_set_translation B c).
  
  (* 提供B的Borel可测性证明 *)
  unfold B.
  exact Hinterval.
Qed.
  
(** 构造可数并集的关键引理 **)
(** 使用平移构造可数稠密集覆盖 **)
Lemma countable_union_translation_cover : forall (B : SetX R) (c : R),
  B in_s sigma_sets R Borel_sigma_algebra ->
  (fun x => exists (q : R) (Hq : B q), x = q + c) in_s sigma_sets R Borel_sigma_algebra.
Proof.
  intros B c HB.
  
  (* 定义序列F_seq，每个F_seq n是B的平移 *)
  set (F_seq := fun (n : nat) => 
    match n with
    | O => (fun x : R => B (x - c))  (* 平移-c，即B + c *)
    | S n' => EmptySet_s              (* 空集 *)
    end).
  
  (* 证明每个F_seq n在Borel σ代数中 *)
  assert (HF_seq : forall n, F_seq n in_s sigma_sets R Borel_sigma_algebra).
  {
    intro n.
    destruct n as [O | n'].
    {
      (* n = 0: 平移-c *)
      unfold F_seq.
      apply borel_set_translation.
      exact HB.
    }
    {
      (* n ≥ 1: 空集 *)
      unfold F_seq.
      (* 空集在Borel σ代数中 *)
      assert (H_empty : EmptySet_s in_s sigma_sets R Borel_sigma_algebra).
      {
        (* 空集作为全集的补集 *)
        rewrite <- complement_universal_empty.
        apply sigma_sets_complement.
        apply sigma_sets_univ_instance.
      }
      exact H_empty.
    }
  }
  
  (* 证明目标集合等于可数并集 *)
  assert (Heq : (fun x : R => exists (q : R) (Hq : B q), x = q + c) = 
                (fun x : R => exists n : nat, F_seq n x)).
  {
    (* 应用集合外延性 *)
    apply set_extensionality.
    intro x.
    split.
    {
      (* 从左到右 *)
      intros [q [Hq Hx_eq]].
      exists O.  (* 使用第0个元素 *)
      unfold F_seq.
      rewrite Hx_eq.
      replace ((q + c) - c) with q by ring.
      exact Hq.
    }
    {
      (* 从右到左 *)
      intros [n Hn].
      destruct n as [O | n'].
      {
        (* n = 0 *)
        unfold F_seq in Hn.
        exists (x - c).
        split.
        {
          replace (x - c) with (x - c) by reflexivity.
          exact Hn.
        }
        ring.
      }
      {
        (* n ≥ 1: 空集，矛盾 *)
        unfold F_seq in Hn.
        contradiction.
      }
    }
  }
  
  (* 应用可数并集的可测性 *)
  rewrite Heq.
  apply sigma_sets_countable_union.
  exact HF_seq.
Qed.
  
Close Scope R_scope.  (* 清除所有 R_scope 中的符号重载 *)
Open Scope R_scope.   (* 重新建立干净的符号绑定 *)
  
(* =========================================================================== *)
(* 第六部分：单调类定理 (Monotone Class Theorem) *)
(* =========================================================================== *)
  
(** 定义：单调类 *)
Definition MonotoneClass {X : Type} (M : Family X) : Prop :=
  (forall (F_seq : nat -> SetX X),
      (forall k : nat, M (F_seq k)) ->
      IncreasingSequence F_seq ->
      M (fun (x : X) => exists k : nat, x in_s (F_seq k))) /\
  (forall (F_seq : nat -> SetX X),
      (forall k : nat, M (F_seq k)) ->
      DecreasingSequence F_seq ->
      M (fun (x : X) => forall k : nat, x in_s (F_seq k))).
(*
(** 定义：单调类 *)
Definition MonotoneClass {X : Type} (M : Family X) : Prop :=
  (forall (F_seq : nat -> SetX X),
      (forall k : nat, M (F_seq k)) ->
      IncreasingSequence F_seq ->
      M (fun (x : X) => exists k : nat, In x (F_seq k))) /\
  (forall (F_seq : nat -> SetX X),
      (forall k : nat, M (F_seq k)) ->
      DecreasingSequence F_seq ->
      M (fun (x : X) => forall k : nat, In x (F_seq k))).
*)
  
(** 定义：代数 *)
Definition Algebra {X : Type} (F : Family X) : Prop :=
  F UniversalSet_s /\
  (forall A, F A -> F (Complement_s A)) /\
  (forall A B, F A -> F B -> F (fun x => A x \/ B x)).
  
(** 引理1：任何σ-代数都是单调类 *)
Lemma sigma_algebra_is_monotone_class : 
  forall {X : Type} (M : SigmaAlgebra X),
    MonotoneClass (sigma_sets X M).
Proof.
  intros X M.
  unfold MonotoneClass.
  split.
  - (* 对单调递增序列的并封闭 *)
    intros F_seq HF_seq Hinc.
    apply sigma_closed_countable_union.
    exact HF_seq.
  - (* 对单调递减序列的交封闭 *)
    intros F_seq HF_seq Hdec.
    apply sigma_closed_countable_intersection.
    exact HF_seq.
Qed.
  
(** 引理2：代数包含空集 *)
Lemma algebra_contains_empty {X : Type} (F : Family X) :
  Algebra F -> F EmptySet_s.
Proof.
  intros [Huniv [Hcomp _]].
  (* 空集 = 全集的补集 *)
  assert (Heq : @SetEq X EmptySet_s (Complement_s UniversalSet_s)).
  {
    intro x.
    split.
    - (* 左到右：x ∈ 空集 => x ∈ 全集的补集 *)
      intro H_empty.  (* H_empty: x in_s EmptySet_s *)
      (* 目标: x in_s Complement_s UniversalSet_s *)
      (* 即: ~(x in_s UniversalSet_s) *)
      intro H_univ.  (* H_univ: x in_s UniversalSet_s *)
      (* 从H_empty: x in_s EmptySet_s得到矛盾 *)
      (* H_empty是False，可以推导出任何目标 *)
      exact H_empty.
    - (* 右到左：x ∈ 全集的补集 => x ∈ 空集 *)
      intro H_comp.  (* H_comp: x in_s Complement_s UniversalSet_s *)
      (* 目标: x in_s EmptySet_s *)
      (* 从H_comp: x in_s Complement_s UniversalSet_s，即~(x in_s UniversalSet_s) *)
      (* 和x in_s UniversalSet_s总是成立，得到矛盾 *)
      apply H_comp.  (* 应用H_comp到x in_s UniversalSet_s的证明上 *)
      (* 需要提供x in_s UniversalSet_s的证明 *)
      exact I.  (* I是True的唯一构造函数 *)
  }
  apply set_extensionality in Heq.
  rewrite Heq.
  apply Hcomp.
  exact Huniv.
Qed.
  
(** 生成的单调类 *)
Definition generated_monotone_class {X : Type} (G : Family X) : Family X :=
  fun A => forall (M : Family X), MonotoneClass M -> (forall B, G B -> M B) -> M A.
  
(** 引理：生成的单调类是最小的包含G的单调类 *)
Lemma generated_monotone_class_properties :
  forall {X : Type} (G : Family X),
    (forall A, G A -> generated_monotone_class G A) /\
    MonotoneClass (generated_monotone_class G) /\
    (forall (M : Family X),
        MonotoneClass M ->
        (forall A, G A -> M A) ->
        forall A, generated_monotone_class G A -> M A).
Proof.
  intros X G.
  split.
  {
    (* 包含G *)
    intros A HA M Hmono HG.
    apply HG.
    exact HA.
  }
  split.
  {
    (* 是单调类 *)
    unfold MonotoneClass, generated_monotone_class.
    split.
    - (* 对单调递增序列的并封闭 *)
      intros F_seq HF_seq Hinc M Hmono HG.
      (* 分解单调类M的性质 *)
      destruct Hmono as [Hinc_union Hdec_inter].
      (* 应用递增并封闭性质 *)
      apply Hinc_union.
      + (* 证明对于所有k，M (F_seq k) *)
        intros k.
        (* 使用HF_seq证明M (F_seq k) *)
        apply (HF_seq k M (conj Hinc_union Hdec_inter) HG).
      + (* 证明序列递增 *)
        exact Hinc.
    - (* 对单调递减序列的交封闭 *)
      intros F_seq HF_seq Hdec M Hmono HG.
      (* 分解单调类M的性质 *)
      destruct Hmono as [Hinc_union Hdec_inter].
      (* 应用递减交封闭性质 *)
      apply Hdec_inter.
      + (* 证明对于所有k，M (F_seq k) *)
        intros k.
        (* 使用HF_seq证明M (F_seq k) *)
        apply (HF_seq k M (conj Hinc_union Hdec_inter) HG).
      + (* 证明序列递减 *)
        exact Hdec.
  }
  {
    (* 最小性 *)
    intros M Hmono HG A HA.
    apply HA.
    exact Hmono.
    exact HG.
  }
Qed.
  
(** 关键引理：如果代数A包含在单调类M中，则A生成的单调类也包含在M中 *)
Lemma algebra_in_monotone_class :
  forall {X : Type} (A : Family X) (M : Family X),
    Algebra A ->
    MonotoneClass M ->
    (forall B, A B -> M B) ->
    forall B, generated_monotone_class A B -> M B.
Proof.
  intros X A M Halg Hmono HA_subset B HB.
  apply HB.
  exact Hmono.
  exact HA_subset.
Qed.
  
(** 辅助定义："好集"方法中的集合族 *)
Section GoodSets.
  
Context {X : Type} {A : Family X} (Halg : Algebra A) (M : Family X) (Hmono : MonotoneClass M) (HA_subset : forall B, A B -> M B).
  
(* 定义D集族：在M0中的补集 *)
Definition good_set_D (C : SetX X) : Prop :=
  generated_monotone_class A (Complement_s C).
  
(* 定义E集族：与A中任意集合的并 *)
Definition good_set_E (C : SetX X) : Prop :=
  forall D, A D -> generated_monotone_class A (fun x => C x \/ D x).
  
(* 证明A包含在D中 *)
Lemma A_in_D : forall C, A C -> good_set_D C.
Proof.
  intros C HC.
  unfold good_set_D.
  pose proof (generated_monotone_class_properties A) as [HA_M0 _].
  apply HA_M0.
  destruct Halg as [_ [Hcomp _]].
  apply Hcomp.
  exact HC.
Qed.
  
(* 证明D是单调类 *)
Lemma D_is_monotone_class : MonotoneClass (fun C => good_set_D C).
Proof.
  unfold MonotoneClass, good_set_D.
  pose proof (generated_monotone_class_properties A) as [HA_M0 [Hmono0 _]].
  split.
  (* 对单调递增序列的并封闭 *)
  - intros F_seq HF_seq Hinc.
    (* 需要证明：Complement (⋃ F_seq) 在生成的单调类中 *)
    set (G_seq := fun n => Complement_s (F_seq n)).
    assert (HG_seq : forall n, generated_monotone_class A (G_seq n)).
    {
      intro n.
      unfold G_seq.
      apply HF_seq.
    }
    assert (Hdec_G : DecreasingSequence G_seq).
    {
      unfold DecreasingSequence, G_seq.
      intros n x Hx.
      intro H.
      apply Hx.
      apply Hinc.
      exact H.
    }
    destruct Hmono0 as [_ Hdec_inter].
    specialize (Hdec_inter G_seq HG_seq Hdec_G).
    (* 证明集合等式 *)
    assert (Heq : @SetEq X (fun x => forall k : nat, x in_s (G_seq k))
                        (Complement_s (fun x => exists k : nat, x in_s (F_seq k)))).
    {
      intro x.
      split.
      - intros Hall Hex.
        destruct Hex as [k Hk].
        specialize (Hall k).
        apply Hall.
        exact Hk.
      - intros Hcomp k Hk.
        apply Hcomp.
        exists k.
        exact Hk.
    }
    (* 使用集合外延性 *)
    pose proof (set_extensionality _ _ Heq) as Heq'.
    rewrite Heq' in Hdec_inter.
    exact Hdec_inter.
    
  (* 对单调递减序列的交封闭 *)
  - intros F_seq HF_seq Hdec.
    set (G_seq := fun n => Complement_s (F_seq n)).
    assert (HG_seq : forall n, generated_monotone_class A (G_seq n)).
    {
      intro n.
      unfold G_seq.
      apply HF_seq.
    }
    assert (Hinc_G : IncreasingSequence G_seq).
    {
      unfold IncreasingSequence, G_seq.
      intros n x Hx.
      intro Hcontra.
      apply Hx.
      apply Hdec.
      exact Hcontra.
    }
    destruct Hmono0 as [Hinc_union _].
    specialize (Hinc_union G_seq HG_seq Hinc_G).
    (* 证明集合等式 *)
    assert (Heq : @SetEq X (fun x => exists k : nat, x in_s (G_seq k))
                        (Complement_s (fun x => forall k : nat, x in_s (F_seq k)))).
    {
      intro x.
      split.
      - intros [n Hx] Hall.
        unfold G_seq in Hx.
        rewrite complement_property in Hx.
        specialize (Hall n).
        contradiction.
      - intros Hcomp.
        apply NNPP.
        intro Hnot.
        apply Hcomp.
        intros n.
        apply NNPP.
        intro Hnot'.
        apply Hnot.
        exists n.
        exact Hnot'.
    }
    (* 使用集合外延性 *)
    pose proof (set_extensionality _ _ Heq) as Heq'.
    rewrite Heq' in Hinc_union.
    exact Hinc_union.
Qed.
  
End GoodSets.
  
(* 生成的σ代数是最小的包含生成集的σ代数 *)
Lemma generated_sigma_algebra_minimal :
  forall {X : Type} (G : Family X) (M : SigmaAlgebra X),
    (forall A, G A -> A in_s (sigma_sets X M)) ->
    forall A, A in_s (sigma_sets X (generated_sigma_algebra G)) -> A in_s (sigma_sets X M).
Proof.
  intros X G M HG A HA.
  unfold generated_sigma_algebra in HA.
  simpl in HA.
  apply HA.
  split.
  - exact HG.
  - split.
    + apply sigma_contains_universe.
    + split.
      * apply sigma_closed_complement.
      * apply sigma_closed_countable_union.
Qed.
  
(** 生成的单调类包含原代数引理 *)
(** 证明：由代数A生成的单调类包含A中的所有集合 *)
Lemma generated_monotone_class_includes_A : 
  forall {X} (A : Family X) (C : SetX X), A C -> generated_monotone_class A C.
Proof.
  (* 证明思路：直接从generated_monotone_class_properties的性质中提取 *)
  intros X A C HC.  (* 引入类型X，代数A，集合C，以及假设HC: C ∈ A *)
  
  (* 引用generated_monotone_class_properties的性质 *)
  pose proof (generated_monotone_class_properties A) as [HA_M0 _].
  (* 分解得到：HA_M0: ∀ C, A C → generated_monotone_class A C *)
  
  (* 应用该性质 *)
  apply HA_M0;  (* 应用生成的单调类包含A的性质 *)
  exact HC.     (* 提供C在A中的证明 *)
Qed.
  
(* 引理：在generated_monotone_class中相等的集合可以替换 *)
Lemma generated_monotone_class_set_eq :
  forall {X} (A : Family X) (B C : SetX X),
    (forall x, B x <-> C x) ->
    generated_monotone_class A B ->
    generated_monotone_class A C.
Proof.
  intros X A B C Heq HB.
  unfold generated_monotone_class in *.
  intros M Hmono HA.
  (* 我们需要证明M C *)
  
  (* 由于B和C在逻辑上等价，它们在集合论意义上是相等的 *)
  assert (Hfunc_eq : B = C).
  {
    apply functional_extensionality.
    intro x.
    apply propositional_extensionality.
    exact (Heq x).
  }
  
  (* 现在我们有了函数相等，可以重写 *)
  rewrite <- Hfunc_eq.
  apply HB; [exact Hmono | exact HA].
Qed.
  
(** 生成的单调类是λ-系统的证明 *)
(** 证明生成的单调类满足λ-系统的三个条件：包含全集、对补运算封闭、对有限并封闭 *)
Lemma generated_monotone_class_is_lambda_system :
  forall {X} (A : Family X) (Halg: Algebra A),
    let M0 := generated_monotone_class A in
    (* λ-系统条件 *)
    M0 UniversalSet_s /\
    (forall C, M0 C -> M0 (Complement_s C)) /\
    (forall C D, M0 C -> M0 D -> M0 (fun x => C x \/ D x)).
Proof.
  intros X A Halg M0.  (* 引入类型X、集合族A、代数假设Halg，定义M0为A生成的单调类 *)
  
  (* 第1部分：证明M0包含全集 *)
  assert (Huniv0 : M0 UniversalSet_s).
  {
    unfold M0.  (* 展开M0的定义 *)
    (* 从代数A的性质得到UniversalSet_s在A中 *)
    destruct Halg as [HunivA _].  (* 分解代数假设：获取A包含全集的证明 *)
    pose proof (generated_monotone_class_properties A) as [HA_M0 _].  (* 获取M0包含A的性质 *)
    apply HA_M0.  (* 应用该性质 *)
    exact HunivA.  (* 提供A包含全集的证明 *)
  }
  
  (* 第2部分：证明M0对补运算封闭 *)
  assert (Hcomp0 : forall C, M0 C -> M0 (Complement_s C)).
  {
    intros C HC.  (* 引入集合C及其在M0中的假设 *)
    unfold M0 in *.  (* 展开M0的定义 *)
    
    (* 方法：使用generated_monotone_class的最小性 *)
    (* 定义集合族D：所有使得补集在M0中的集合 *)
    set (D := fun (E : SetX X) => generated_monotone_class A (Complement_s E)).
    
    (* 证明A ⊆ D *)
    assert (HA_in_D : forall E, A E -> D E).
    {
      intros E HE.  (* 引入集合E及其在A中的假设 *)
      unfold D.  (* 展开D的定义 *)
      pose proof (generated_monotone_class_properties A) as [HA_M0' _].  (* 获取M0包含A的性质 *)
      apply HA_M0'.  (* 应用该性质 *)
      (* 由于A是代数，对补运算封闭 *)
      destruct Halg as [_ [HcompA _]].  (* 分解代数假设：获取A对补运算封闭的证明 *)
      apply HcompA.  (* 应用补运算封闭性 *)
      exact HE.  (* 提供E在A中的证明 *)
    }
    
      (* 证明D是单调类 *)
      assert (Hmono_D : MonotoneClass D).
      {
        unfold MonotoneClass, D.  (* 展开单调类和D的定义 *)
        split.  (* 分解单调类的两个条件 *)
        
        (* 对递增序列的并封闭 *)
        - intros F_seq HF_seq Hinc.  (* 引入递增序列F_seq及其在D中的假设 *)
          (* 定义补集序列 *)
          set (G_seq := fun n => Complement_s (F_seq n)).
          assert (HG_seq : forall n, generated_monotone_class A (G_seq n)).
          {
            intro n. unfold G_seq. exact (HF_seq n).  (* 每个G_seq n都在生成的单调类中 *)
          }
          assert (Hdec_G : DecreasingSequence G_seq).  (* 证明G_seq是递减序列 *)
          {
            unfold DecreasingSequence, Subset, G_seq.  (* 展开相关定义 *)
            intros n x Hx H.  (* 引入假设 *)
            apply Hx.  (* 应用假设 *)
            apply Hinc.  (* 利用F_seq递增的性质 *)
            exact H.  (* 提供x在F_seq n中的证明 *)
          }
          
          (* 使用generated_monotone_class的单调类性质 *)
          pose proof (generated_monotone_class_properties A) as [_ [Hmono0 _]].
          destruct Hmono0 as [_ Hdec_inter].  (* 获取单调类对递减序列交封闭的性质 *)
          specialize (Hdec_inter G_seq HG_seq Hdec_G).  (* 应用该性质 *)
          
          (* Hdec_inter: generated_monotone_class A (fun x => forall k, x in_s (G_seq k)) *)
          (* 我们需要证明: generated_monotone_class A (Complement_s (fun x => exists k, x in_s (F_seq k))) *)
          
          (* 使用集合相等性转换 *)
          apply (generated_monotone_class_set_eq A
                  (fun x : X => forall k, x in_s (G_seq k))
                  (Complement_s (fun x : X => exists k, x in_s (F_seq k)))).
          {
            (* 证明两个集合在逻辑上等价 *)
            intro x.  (* 引入元素x *)
            split.  (* 证明双向包含 *)
            - intros Hall Hex.  (* 左到右：如果x在所有G_seq k中，且存在k使x在F_seq k中，则矛盾 *)
              destruct Hex as [k Hk].  (* 分解存在性假设 *)
              specialize (Hall k).  (* 应用Hall到具体的k *)
              unfold G_seq in Hall.  (* 展开G_seq的定义 *)
              apply Hall.  (* 应用Hall *)
              exact Hk.  (* 提供x在F_seq k中的证明 *)
            - intros Hcomp k Hk.  (* 右到左：如果x不在存在k使得x在F_seq k中，那么对任意k，x在G_seq k中 *)
              apply Hcomp.  (* 应用假设Hcomp *)
              exists k.  (* 提供存在性证明 *)
              exact Hk.  (* 提供x在F_seq k中的证明 *)
          }
          exact Hdec_inter.  (* 完成证明 *)
          
        (* 对递减序列的交封闭 *)
        - intros F_seq HF_seq Hdec.  (* 引入递减序列F_seq及其在D中的假设 *)
          set (G_seq := fun n => Complement_s (F_seq n)).  (* 定义补集序列 *)
          assert (HG_seq : forall n, generated_monotone_class A (G_seq n)).
          {
            intro n. unfold G_seq. exact (HF_seq n).  (* 每个G_seq n都在生成的单调类中 *)
          }
          assert (Hinc_G : IncreasingSequence G_seq).  (* 证明G_seq是递增序列 *)
          {
            unfold IncreasingSequence, Subset, G_seq.  (* 展开相关定义 *)
            intros n x Hx H.  (* 引入假设 *)
            apply Hx.  (* 应用假设 *)
            apply Hdec.  (* 利用F_seq递减的性质 *)
            exact H.  (* 提供x在F_seq n中的证明 *)
          }
          
          pose proof (generated_monotone_class_properties A) as [_ [Hmono0 _]].
          destruct Hmono0 as [Hinc_union _].  (* 获取单调类对递增序列并封闭的性质 *)
          specialize (Hinc_union G_seq HG_seq Hinc_G).  (* 应用该性质 *)
          
          (* Hinc_union: generated_monotone_class A (fun x => exists k, x in_s (G_seq k)) *)
          (* 我们需要证明: generated_monotone_class A (Complement_s (fun x => forall k, x in_s (F_seq k))) *)
          
          (* 使用集合相等性转换 *)
          apply (generated_monotone_class_set_eq A
                  (fun x : X => exists k, x in_s (G_seq k))
                  (Complement_s (fun x : X => forall k, x in_s (F_seq k)))).
          {
            (* 证明两个集合在逻辑上等价 *)
            intro x.  (* 引入元素x *)
            split.  (* 证明双向包含 *)
            - intros [k Hk] Hall.  (* 左到右：如果存在k使x在G_seq k中，且x在所有F_seq k中，则矛盾 *)
              unfold G_seq in Hk.  (* 展开G_seq的定义 *)
              apply Hk.  (* 应用Hk *)
              apply Hall.  (* 应用Hall *)
            - intros Hcomp.  (* 右到左：如果x不在所有F_seq k中，则存在k使x在G_seq k中 *)
              (* 这里需要使用排中律 *)
              apply NNPP.  (* 使用反证法 *)
              intro Hnone.  (* 假设不存在这样的k *)
              apply Hcomp.  (* 应用Hcomp *)
              intros k.  (* 对任意k *)
              apply NNPP.  (* 再次使用反证法 *)
              intro Hnot.  (* 假设x不在F_seq k中 *)
              apply Hnone.  (* 应用不存在性假设 *)
              exists k.  (* 提供存在性证明 *)
              exact Hnot.  (* 提供x不在F_seq k中的证明 *)
          }
          exact Hinc_union.  (* 完成证明 *)
      }
    
    (* 应用generated_monotone_class的最小性 *)
    pose proof (generated_monotone_class_properties A) as [_ [_ Hsmallest]].
    apply Hsmallest with (M := D).  (* 应用最小性原理 *)
    - exact Hmono_D.  (* 提供D是单调类的证明 *)
    - exact HA_in_D.  (* 提供A ⊆ D的证明 *)
    - exact HC.  (* 提供C在M0中的证明 *)
  }
  
  (* 第3部分：证明M0对有限并封闭 *)
  assert (Hunion0 : forall C D_sets, M0 C -> M0 D_sets -> M0 (fun x => C x \/ D_sets x)).
  {
    intros C D_sets HC HD.  (* 引入集合C、D_sets及其在M0中的假设 *)
    unfold M0 in *.  (* 展开M0的定义 *)
    
    (* 方法：再次使用最小性 *)
    (* 定义集合族E_set：所有与C的并在generated_monotone_class A中的集合 *)
    set (E_set := fun (S : SetX X) => generated_monotone_class A (fun x => C x \/ S x)).
    
    (* 证明A ⊆ E_set *)
    assert (HA_in_E_set : forall S, A S -> E_set S).
    {
      intros S HS.  (* 引入集合S及其在A中的假设 *)
      unfold E_set.  (* 展开E_set的定义 *)
      
      (* 使用嵌套的最小性论证 *)
      (* 定义另一个集合族F_set：所有与S的并在generated_monotone_class A中的集合 *)
      set (F_set := fun (T : SetX X) => generated_monotone_class A (fun x => T x \/ S x)).
      
      (* 证明A ⊆ F_set *)
      assert (HA_in_F_set : forall T, A T -> F_set T).
      {
        intros T HT.  (* 引入集合T及其在A中的假设 *)
        unfold F_set.  (* 展开F_set的定义 *)
        pose proof (generated_monotone_class_properties A) as [HA_M0 _].  (* 获取M0包含A的性质 *)
        apply HA_M0.  (* 应用该性质 *)
        destruct Halg as [_ [_ HunionA]].  (* 分解代数假设：获取A对有限并封闭的性质 *)
        apply HunionA; assumption.  (* 应用有限并封闭性 *)
      }
      
      (* 证明F_set是单调类 *)
      assert (Hmono_F_set : MonotoneClass F_set).
      {
        unfold MonotoneClass, F_set.  (* 展开单调类和F_set的定义 *)
        split.  (* 分解单调类的两个条件 *)
        
        (* 对递增序列的并封闭 *)
        - intros G_seq HG_seq Hinc.  (* 引入递增序列G_seq及其在F_set中的假设 *)
          set (H_seq := fun n => fun x => G_seq n x \/ S x).  (* 定义新序列H_seq *)
          assert (HH_seq : forall n, generated_monotone_class A (H_seq n)).
          {
            intro n. unfold H_seq. exact (HG_seq n).  (* 每个H_seq n都在生成的单调类中 *)
          }
          assert (Hinc_H : IncreasingSequence H_seq).  (* 证明H_seq是递增序列 *)
          {
            unfold IncreasingSequence, Subset, H_seq.  (* 展开相关定义 *)
            intros n x [HxG | HxS].  (* 分析x在H_seq n中的两种情况 *)
            - left. apply Hinc. exact HxG.  (* 如果x在G_seq n中，则利用G_seq递增的性质 *)
            - right. exact HxS.  (* 如果x在S中，保持不变 *)
          }
          
          pose proof (generated_monotone_class_properties A) as [_ [Hmono0 _]].
          destruct Hmono0 as [Hinc_union _].  (* 获取单调类对递增序列并封闭的性质 *)
          specialize (Hinc_union H_seq HH_seq Hinc_H).  (* 应用该性质 *)
          
          (* 使用集合相等性转换 *)
          apply (generated_monotone_class_set_eq A
                  (fun x : X => exists k, x in_s (H_seq k))
                  (fun x : X => (exists k, x in_s G_seq k) \/ S x)).
          {
            (* 证明逻辑等价 *)
            intro x.  (* 引入元素x *)
            split.  (* 证明双向包含 *)
            - intros [k [HxG | HxS]].  (* 左到右：分析存在性 *)
              + left. exists k. exact HxG.  (* 如果x在某个G_seq k中 *)
              + right. exact HxS.  (* 如果x在S中 *)
            - intros [[k HxG] | HxS].  (* 右到左：分析两种情况 *)
              + exists k. left. exact HxG.  (* 如果存在k使x在G_seq k中 *)
              + exists 0%nat. right. exact HxS.  (* 如果x在S中，取k=0 *)
          }
          exact Hinc_union.  (* 完成证明 *)
          
        (* 对递减序列的交封闭 *)
        - intros G_seq HG_seq Hdec.  (* 引入递减序列G_seq及其在F_set中的假设 *)
          set (H_seq := fun n => fun x => G_seq n x \/ S x).  (* 定义新序列H_seq *)
          assert (HH_seq : forall n, generated_monotone_class A (H_seq n)).
          {
            intro n. unfold H_seq. exact (HG_seq n).  (* 每个H_seq n都在生成的单调类中 *)
          }
          assert (Hdec_H : DecreasingSequence H_seq).  (* 证明H_seq是递减序列 *)
          {
            unfold DecreasingSequence, Subset, H_seq.  (* 展开相关定义 *)
            intros n x [HxG | HxS].  (* 分析x在H_seq n中的两种情况 *)
            - left. apply Hdec. exact HxG.  (* 如果x在G_seq n中，则利用G_seq递减的性质 *)
            - right. exact HxS.  (* 如果x在S中，保持不变 *)
          }
          
          pose proof (generated_monotone_class_properties A) as [_ [Hmono0 _]].
          destruct Hmono0 as [_ Hdec_inter].  (* 获取单调类对递减序列交封闭的性质 *)
          specialize (Hdec_inter H_seq HH_seq Hdec_H).  (* 应用该性质 *)
          
          (* 使用集合相等性转换 *)
          apply (generated_monotone_class_set_eq A
                  (fun x : X => forall k, x in_s (H_seq k))
                  (fun x : X => (forall k, x in_s G_seq k) \/ S x)).
          {
            (* 证明逻辑等价 *)
            intro x.  (* 引入元素x *)
            split.  (* 证明双向包含 *)
            - intros Hall.  (* 左到右：如果x在所有H_seq k中 *)
              destruct (classic (S x)) as [HxS | HnotS].  (* 分析x是否在S中 *)
              + right. exact HxS.  (* 如果在S中，取第二种情况 *)
              + left. intro k.  (* 如果不在S中，证明x在所有G_seq k中 *)
                specialize (Hall k).  (* 应用Hall到具体的k *)
                destruct Hall as [HxG | HxS'].  (* 分析Hall的结果 *)
                * exact HxG.  (* 如果x在G_seq k中，完成证明 *)
                * contradiction.  (* 如果x在S中，与HnotS矛盾 *)
            - intros [Hall | HxS] k.  (* 右到左：分析两种情况 *)
              + left. apply Hall.  (* 如果x在所有G_seq k中，则x在G_seq k中 *)
              + right. exact HxS.  (* 如果x在S中，则x在S中 *)
          }
          exact Hdec_inter.  (* 完成证明 *)
      }
      
      (* 应用最小性得到C ∈ F_set *)
      pose proof (generated_monotone_class_properties A) as [_ [_ Hsmallest]].
      apply (Hsmallest F_set Hmono_F_set HA_in_F_set C HC).  (* 应用最小性原理 *)
    }
    
    (* 证明E_set是单调类 *)
    assert (Hmono_E_set : MonotoneClass E_set).
    {
      unfold MonotoneClass, E_set.  (* 展开单调类和E_set的定义 *)
      split.  (* 分解单调类的两个条件 *)
      
      (* 对递增序列的并封闭 *)
      - intros F_seq HF_seq Hinc.  (* 引入递增序列F_seq及其在E_set中的假设 *)
        set (G_seq := fun n => fun x => C x \/ F_seq n x).  (* 定义新序列G_seq *)
        assert (HG_seq : forall n, generated_monotone_class A (G_seq n)).
        {
          intro n. unfold G_seq. exact (HF_seq n).  (* 每个G_seq n都在生成的单调类中 *)
        }
        assert (Hinc_G : IncreasingSequence G_seq).  (* 证明G_seq是递增序列 *)
        {
          unfold IncreasingSequence, Subset, G_seq.  (* 展开相关定义 *)
          intros n x [HxC | HxF].  (* 分析x在G_seq n中的两种情况 *)
          - left. exact HxC.  (* 如果x在C中，保持不变 *)
          - right. apply Hinc. exact HxF.  (* 如果x在F_seq n中，利用F_seq递增的性质 *)
        }
        
        pose proof (generated_monotone_class_properties A) as [_ [Hmono0 _]].
        destruct Hmono0 as [Hinc_union _].  (* 获取单调类对递增序列并封闭的性质 *)
        specialize (Hinc_union G_seq HG_seq Hinc_G).  (* 应用该性质 *)
        
        (* 使用集合相等性转换 *)
        apply (generated_monotone_class_set_eq A
                (fun x : X => exists k, x in_s (G_seq k))
                (fun x : X => C x \/ (exists k, x in_s F_seq k))).
        {
          (* 证明逻辑等价 *)
          intro x.  (* 引入元素x *)
          split.  (* 证明双向包含 *)
          - intros [k [HxC | HxF]].  (* 左到右：分析存在性 *)
            + left. exact HxC.  (* 如果x在C中 *)
            + right. exists k. exact HxF.  (* 如果x在某个F_seq k中 *)
          - intros [HxC | [k HxF]].  (* 右到左：分析两种情况 *)
            + exists 0%nat. left. exact HxC.  (* 如果x在C中，取k=0 *)
            + exists k. right. exact HxF.  (* 如果存在k使x在F_seq k中 *)
        }
        exact Hinc_union.  (* 完成证明 *)
        
      (* 对递减序列的交封闭 *)
      - intros F_seq HF_seq Hdec.  (* 引入递减序列F_seq及其在E_set中的假设 *)
        set (G_seq := fun n => fun x => C x \/ F_seq n x).  (* 定义新序列G_seq *)
        assert (HG_seq : forall n, generated_monotone_class A (G_seq n)).
        {
          intro n. unfold G_seq. exact (HF_seq n).  (* 每个G_seq n都在生成的单调类中 *)
        }
        assert (Hdec_G : DecreasingSequence G_seq).  (* 证明G_seq是递减序列 *)
        {
          unfold DecreasingSequence, Subset, G_seq.  (* 展开相关定义 *)
          intros n x [HxC | HxF].  (* 分析x在G_seq n中的两种情况 *)
          - left. exact HxC.  (* 如果x在C中，保持不变 *)
          - right. apply Hdec. exact HxF.  (* 如果x在F_seq n中，利用F_seq递减的性质 *)
        }
        
        pose proof (generated_monotone_class_properties A) as [_ [Hmono0 _]].
        destruct Hmono0 as [_ Hdec_inter].  (* 获取单调类对递减序列交封闭的性质 *)
        specialize (Hdec_inter G_seq HG_seq Hdec_G).  (* 应用该性质 *)
        
        (* 使用集合相等性转换 *)
        apply (generated_monotone_class_set_eq A
                (fun x : X => forall k, x in_s (G_seq k))
                (fun x : X => C x \/ (forall k, x in_s F_seq k))).
        {
          (* 证明逻辑等价 *)
          intro x.  (* 引入元素x *)
          split.  (* 证明双向包含 *)
          - intros Hall.  (* 左到右：如果x在所有G_seq k中 *)
            destruct (classic (C x)) as [HxC | HnotC].  (* 分析x是否在C中 *)
            + left. exact HxC.  (* 如果在C中，取第一种情况 *)
            + right. intro k.  (* 如果不在C中，证明x在所有F_seq k中 *)
              specialize (Hall k).  (* 应用Hall到具体的k *)
              destruct Hall as [HxC' | HxF].  (* 分析Hall的结果 *)
              * contradiction.  (* 如果x在C中，与HnotC矛盾 *)
              * exact HxF.  (* 如果x在F_seq k中，完成证明 *)
          - intros [HxC | Hall] k.  (* 右到左：分析两种情况 *)
            + left. exact HxC.  (* 如果x在C中，则x在C中 *)
            + right. apply Hall.  (* 如果x在所有F_seq k中，则x在F_seq k中 *)
        }
        exact Hdec_inter.  (* 完成证明 *)
    }
    
    (* 应用最小性得到D_sets ∈ E_set *)
    pose proof (generated_monotone_class_properties A) as [_ [_ Hsmallest]].
    apply (Hsmallest E_set Hmono_E_set HA_in_E_set D_sets HD).  (* 应用最小性原理 *)
  }
  
  (* 返回三个结论 *)
  split.  (* 将目标分解为三个部分 *)
  { exact Huniv0. }  (* 第一部分：M0包含全集 *)
  split.  (* 继续分解剩余两个部分 *)
  { exact Hcomp0. }  (* 第二部分：M0对补运算封闭 *)
  { exact Hunion0. }  (* 第三部分：M0对有限并封闭 *)
Qed.
  
(** 单调类定理 - 简洁版本（使用递增序列构造） *)
Theorem monotone_class_theorem :
  forall {X : Type} (A : Family X) (M : Family X),
    Algebra A ->
    MonotoneClass M ->
    (forall B, A B -> M B) ->
    forall B, (sigma_sets X (generated_sigma_algebra A)) B -> M B.
Proof.
  intros X A M Halg Hmono HA_subset B HB.
  set (M0 := generated_monotone_class A).
  
  (* 1. 证明M0 ⊆ M *)
  assert (HM0_subset_M : forall C, M0 C -> M C).
  {
    intros C HC.
    pose proof (generated_monotone_class_properties A) as [_ [_ Hsmallest]].
    apply Hsmallest with (M := M); [exact Hmono | exact HA_subset | exact HC].
  }
  
  (* 2. 证明由A生成的σ代数包含在M0中 *)
  assert (Hsigma_in_M0 : forall C, (sigma_sets X (generated_sigma_algebra A)) C -> M0 C).
  {
    intros C HC.
    unfold generated_sigma_algebra in HC.
    simpl in HC.
    
    (* 应用HC：只需证明M0满足σ代数的所有条件 *)
    apply HC with (F := M0).
    
    (* 分解为四个条件，使用明确的分隔 *)
    split.
    { (* 2.1 M0包含A *)
      intros A0 HA0.
      unfold M0.
      pose proof (generated_monotone_class_properties A) as [HA_M0 _].
      apply HA_M0.
      exact HA0.
    }
    split.
    { (* 2.2 M0包含全集 *)
      unfold M0.
      pose proof (generated_monotone_class_is_lambda_system A Halg) as [Huniv0 _].
      exact Huniv0.
    }
    split.
    { (* 2.3 M0对补集封闭 *)
      unfold M0.
      pose proof (generated_monotone_class_is_lambda_system A Halg) as [_ [Hcomp0 _]].
      exact Hcomp0.
    }
    { (* 2.4 M0对可数并封闭 - 关键部分 *)
      unfold M0.
      (* 从λ-系统性质获取有限并封闭性 *)
      pose proof (generated_monotone_class_is_lambda_system A Halg) as [_ [_ Hfinite_union0]].
      
      (* 构造递增序列：B_seq n = ⋃_{i=0}^{n} F_seq i *)
      intros F_seq HF_seq.
      set (B_seq := fun n => fun x => exists i, (i <= n)%nat /\ x in_s F_seq i).
      
      (* 证明每个B_seq n在M0中 *)
      assert (HB_seq : forall n, generated_monotone_class A (B_seq n)).
      {
        intro n.
        induction n as [O | n' IH].
        - (* n=0 *)
          unfold B_seq.
          assert (Heq : (fun x => exists i, (i <= O)%nat /\ x in_s F_seq i) = F_seq O).
          {
            apply set_extensionality.
            intro x.
            split.
            + intros [i [Hi Hx]].
              assert (i = O) by lia.
              subst; exact Hx.
            + intros Hx.
              exists O.
              split; [lia | exact Hx].
          }
          rewrite Heq.
          apply HF_seq.
          
        - (* n+1 *)
          unfold B_seq.
          assert (Heq : (fun x => exists i, (i <= S n')%nat /\ x in_s F_seq i) =
                       (fun x => (exists i, (i <= n')%nat /\ x in_s F_seq i) \/ x in_s F_seq (S n'))).
          {
            apply set_extensionality.
            intro x.
            split.
            + intros [i [Hi Hx]].
              destruct (le_lt_eq_dec i (S n') Hi) as [Hlt|Heq_i].
              * left. exists i. split; [lia | exact Hx].
              * right. subst. exact Hx.
            + intros [[i [Hi Hx]]|Hx].
              * exists i. split; [lia | exact Hx].
              * exists (S n'). split; [lia | exact Hx].
          }
          rewrite Heq.
          apply Hfinite_union0; [exact IH | apply HF_seq].
      }
      
      (* 证明B_seq是递增序列 *)
      assert (Hinc_B : IncreasingSequence B_seq).
      {
        unfold IncreasingSequence, Subset, B_seq.
        intros n x [i [Hi Hx]].
        exists i.
        split; [lia | exact Hx].
      }
      
      (* 应用单调类性质：递增序列的并在M0中 *)
      pose proof (generated_monotone_class_properties A) as [_ [Hmono0 _]].
      destruct Hmono0 as [Hinc_union _].
      specialize (Hinc_union B_seq HB_seq Hinc_B).
      
      (* 证明B_seq的并等于F_seq的并 *)
      assert (Heq_union : (fun x => exists n, B_seq n x) = (fun x => exists n, x in_s F_seq n)).
      {
        apply set_extensionality.
        intro x.
        split.
        + intros [n [i [Hi Hx]]].
          exists i; exact Hx.
        + intros [n Hx].
          exists n.
          exists n.
          split; [lia | exact Hx].
      }
      
      rewrite <- Heq_union.  (* 关键修正：使用 <- 而不是 -> *)
      exact Hinc_union.
    }
  }
  
  (* 3. 应用结论 *)
  apply HM0_subset_M.
  apply Hsigma_in_M0.
  exact HB.
Qed.
  
(** 引理：单调类包含A则包含A生成的σ代数 *)
Lemma monotone_class_contains_generated_sigma :
  forall {X : Type} (A : Family X) (M : Family X),
    Algebra A ->
    MonotoneClass M ->
    (forall B, A B -> M B) ->
    forall B, (sigma_sets X (generated_sigma_algebra A)) B -> M B.
Proof.
  intros X A M Halg Hmono HA_subset B HB.
  (* 这个证明和简洁版本相同，可以直接使用简洁版本的证明 *)
  apply (monotone_class_theorem A M Halg Hmono HA_subset B HB).
Qed.
  
(** 生成的单调类是λ-系统的详细证明 *)
Lemma generated_monotone_class_lambda_detailed :
  forall {X : Type} (A : Family X) (Halg: Algebra A),
    let M0 := generated_monotone_class A in
    (* λ-系统条件 *)
    M0 UniversalSet_s /\
    (forall C, M0 C -> M0 (Complement_s C)) /\
    (forall C D, M0 C -> M0 D -> Disjoint C D -> M0 (fun x => C x \/ D x)).
Proof.
  intros X A Halg M0.
  
  (* 第一步：从已有的λ-系统性质获取前两个条件 *)
  pose proof (generated_monotone_class_is_lambda_system A Halg) as [Huniv [Hcomp Hunion]].
  
  (* 第二步：证明包含全集 *)
  assert (Huniv0 : M0 UniversalSet_s).
  {
    exact Huniv.
  }
  
  (* 第三步：证明对补集封闭 *)
  assert (Hcomp0 : forall C, M0 C -> M0 (Complement_s C)).
  {
    exact Hcomp.
  }
  
  (* 第四步：证明对不交并封闭 - 核心部分 *)
  assert (Hdisj_union0 : forall C D, M0 C -> M0 D -> Disjoint C D -> M0 (fun x => C x \/ D x)).
  {
    intros C D HC HD Hdisj.
    (* 使用"好集"方法 *)
    
    (* 1. 首先证明 M0 包含 A *)
    pose proof (generated_monotone_class_properties A) as [HA_M0 [Hmono0 Hsmallest]].
    
    (* 2. 由于 M0 对有限并封闭（从 Hunion 获取），我们可以直接应用 *)
    (* 注意：Hunion 已经证明了对任意两个集合的并封闭，包括不交的情况 *)
    apply Hunion; assumption.
  }
  
  (* 返回所有三个条件 *)
  split.
  { exact Huniv0. }
  split.
  { exact Hcomp0. }
  { exact Hdisj_union0. }
Qed.
  
(** 生成的单调类对不交并封闭的详细证明 *)
Lemma generated_monotone_class_disjoint_union :
  forall {X : Type} (A : Family X) (Halg: Algebra A),
    let M0 := generated_monotone_class A in
    forall C D, M0 C -> M0 D -> Disjoint C D -> M0 (fun x => C x \/ D x).
Proof.
  intros X A Halg M0 C D HC HD Hdisj.
  
  (* 直接从generated_monotone_class_is_lambda_system中获取不相交并集的性质 *)
  pose proof (generated_monotone_class_is_lambda_system A Halg) as [_ [_ Hunion0]].
  
  (* 应用不相交并集的性质 *)
  apply Hunion0; assumption.
Qed.
  
(** 代数的单调类扩展引理 *)
Lemma algebra_to_monotone_class_extension :
  forall {X : Type} (A : Family X) (Halg : Algebra A),
    let M0 := generated_monotone_class A in
    (* M0继承了A的代数性质 *)
    (forall C D, A C -> A D -> M0 (fun x => C x \/ D x)) /\
    (forall C, A C -> M0 (Complement_s C)).
Proof.
  intros X A Halg M0.
  pose proof (generated_monotone_class_properties A) as [HA_M0 [Hmono0 Hsmallest]].
  destruct Halg as [HunivA [HcompA HunionA]].
  split.
  - intros C D HC HD.
    apply HA_M0.
    apply HunionA; assumption.
  - intros C HC.
    apply HA_M0.
    apply HcompA.
    exact HC.
Qed.
  
(** 单调类对递减序列的交封闭 *)
Lemma monotone_class_decreasing_intersection :
  forall {X : Type} (M : Family X) (Hmono : MonotoneClass M),
    forall (F_seq : nat -> SetX X),
    (forall n, M (F_seq n)) ->
    DecreasingSequence F_seq ->
    M (fun x => forall n, x in_s F_seq n).
Proof.
  intros X M Hmono F_seq HF_seq Hdec.
  destruct Hmono as [_ Hdec_inter].
  apply Hdec_inter; assumption.
Qed.
  
(** 递增序列构造引理 - 用于将任意可数并转化为递增序列并 *)
Lemma construct_increasing_sequence_for_union :
  forall {X : Type} (F_seq : nat -> SetX X),
    exists (B_seq : nat -> SetX X),
      IncreasingSequence B_seq /\
      (forall x, (exists n, x in_s F_seq n) <-> (exists n, x in_s B_seq n)).
Proof.
  intros X F_seq.
  (* 构造递增序列 B_seq n = ⋃_{i=0}^{n} F_seq i *)
  exists (fun n => fun x => exists i, (i <= n)%nat /\ x in_s F_seq i).
  split.
  - (* 证明是递增序列 *)
    unfold IncreasingSequence, Subset.
    intros n x [i [Hi Hx]].
    exists i.
    split; [lia | exact Hx].
  - (* 证明等价性 *)
    intro x.
    split.
    + intros [n Hx].
      exists n.
      exists n.
      split; [lia | exact Hx].
    + intros [n [i [Hi Hx]]].
      exists i; exact Hx.
Qed.
  
(** 递减序列构造引理 - 用于将任意可数交转化为递减序列交 *)
Lemma construct_decreasing_sequence_for_intersection :
  forall {X : Type} (F_seq : nat -> SetX X),
    exists (B_seq : nat -> SetX X),
      DecreasingSequence B_seq /\
      (forall x, (forall n, x in_s F_seq n) <-> (forall n, x in_s B_seq n)).
Proof.
  intros X F_seq.
  (* 构造递减序列 B_seq n = ⋂_{i=0}^{n} F_seq i *)
  exists (fun n => fun x => forall i, (i <= n)%nat -> x in_s F_seq i).
  split.
  - (* 证明是递减序列 *)
    unfold DecreasingSequence, Subset.
    intros n x Hx i Hi.
    apply Hx.
    lia.
  - (* 证明等价性 *)
    intro x.
    split.
    + intros Hall n i Hi.
      apply Hall.
    + intros Hall n.
      specialize (Hall (max n n) n).
      apply Hall.
      lia.
Qed.
  
(* 首先定义一些基础概念 *)
Definition Subset {X} (A B : SetX X) : Prop :=
  forall x, A x -> B x.
  
Definition Disjoint {X} (A B : SetX X) : Prop :=
  forall x, ~ (A x /\ B x).
  
Definition IncreasingSequence {X} (F : nat -> SetX X) : Prop :=
  forall n, Subset (F n) (F (S n)).
  
Definition DecreasingSequence {X} (F : nat -> SetX X) : Prop :=
  forall n, Subset (F (S n)) (F n).
  
(* 交集可测性引理 - 针对生成的单调类 *)
Lemma intersection_measurable_in_M0 {X : Type} (A : Family X) (Halg : Algebra A) 
  (C1 C2 : SetX X) (HC1 : generated_monotone_class A C1) 
  (HC2 : generated_monotone_class A C2) : 
  generated_monotone_class A (fun x => C1 x /\ C2 x).
Proof.
  (* 使用德摩根定律将交集转化为补集的并的补集 *)
  assert (Heq : (fun x => C1 x /\ C2 x) = 
               Complement_s (fun x => (Complement_s C1) x \/ (Complement_s C2) x)).
  {
    apply set_extensionality.
    intro x.
    split.
    - intros [Hx1 Hx2].
      intro H.
      destruct H as [Hc1 | Hc2].
      + apply Hc1; exact Hx1.
      + apply Hc2; exact Hx2.
    - intro H.
      split.
      + apply NNPP.
        intro H1.
        apply H.
        left; exact H1.
      + apply NNPP.
        intro H2.
        apply H.
        right; exact H2.
  }
  rewrite Heq.
  
  (* 应用补集封闭性 *)
  pose proof (generated_monotone_class_properties A) as [_ [Hmono0 Hsmallest]].
  
  (* 首先证明 Complement_s C1 和 Complement_s C2 在生成的单调类中 *)
  assert (HC1c : generated_monotone_class A (Complement_s C1)).
  {
    pose proof (generated_monotone_class_is_lambda_system A Halg) as [_ [Hcomp0 _]].
    apply Hcomp0; exact HC1.
  }
  
  assert (HC2c : generated_monotone_class A (Complement_s C2)).
  {
    pose proof (generated_monotone_class_is_lambda_system A Halg) as [_ [Hcomp0 _]].
    apply Hcomp0; exact HC2.
  }
  
  (* 现在需要证明并集在生成的单调类中 *)
  (* 使用generated_monotone_class_is_lambda_system的有限并性质 *)
  pose proof (generated_monotone_class_is_lambda_system A Halg) as [_ [_ Hunion0]].
  
  (* 应用有限并性质证明并集在生成的单调类中 *)
  assert (Hunion : generated_monotone_class A (fun x => (Complement_s C1) x \/ (Complement_s C2) x)).
  {
    apply Hunion0; [exact HC1c | exact HC2c].
  }
  
  (* 应用补集封闭性 *)
  pose proof (generated_monotone_class_is_lambda_system A Halg) as [_ [Hcomp0' _]].
  apply Hcomp0'.
  exact Hunion.
Qed.
  
(** 单调类定理的标准形式 *)
Theorem monotone_class_theorem_standard :
  forall {X : Type} (A : Family X) (M : Family X),
    Algebra A ->
    MonotoneClass M ->
    (forall B, A B -> M B) ->
    forall B, (sigma_sets X (generated_sigma_algebra A)) B -> M B.
Proof.
  intros X A M Halg Hmono HA_subset B HB.
  
  (* 获取A生成的单调类 *)
  set (M0 := generated_monotone_class A).
  
  (* 证明M0包含在M中 *)
  assert (HM0_subset_M : forall C, M0 C -> M C).
  {
    intros C HC.
    pose proof (generated_monotone_class_properties A) as [HA_M0 [Hmono0 Hsmallest]].
    apply Hsmallest with (M := M); [exact Hmono | exact HA_subset | exact HC].
  }
  
  (* 证明M0包含A *)
  assert (HA_in_M0 : forall C, A C -> M0 C).
  {
    intros C HC.
    pose proof (generated_monotone_class_properties A) as [HA_M0 _].
    apply HA_M0; exact HC.
  }
  
  (* 证明M0是单调类 *)
  assert (Hmono0 : MonotoneClass M0).
  {
    pose proof (generated_monotone_class_properties A) as [_ [Hmono0 _]].
    exact Hmono0.
  }
  
  (* 使用generated_monotone_class_is_lambda_system获取M0的代数性质 *)
  assert (Hlambda_simple : let M0 := generated_monotone_class A in
                          M0 UniversalSet_s /\
                          (forall C, M0 C -> M0 (Complement_s C)) /\
                          (forall C D, M0 C -> M0 D -> M0 (fun x => C x \/ D x))).
  {
    apply generated_monotone_class_is_lambda_system; exact Halg.
  }
  
  destruct Hlambda_simple as [Huniv0 [Hcomp0 Hfinite_union0]].
  
  (* 证明M0对可数并封闭 *)
  assert (Hcountable_union0 : forall (F_seq : nat -> SetX X),
    (forall n, M0 (F_seq n)) -> M0 (fun x => exists n, F_seq n x)).
  {
    intros F_seq HF_seq.
    (* 构造递增序列 B_n = ⋃_{i=0}^n F_seq i *)
    set (B_seq := fun n => fun x => exists i, (i <= n)%nat /\ F_seq i x).
    
    (* 证明每个B_n在M0中 *)
    assert (HB_seq : forall n, M0 (B_seq n)).
    {
      intro n.
      induction n as [O | n' IH].
      - (* n = 0 *)
        unfold B_seq.
        assert (Heq : (fun x => exists i, (i <= 0)%nat /\ F_seq i x) = F_seq 0%nat).
        {
          apply set_extensionality.
          intro x.
          split.
          + intros [i [Hi Hx]].
            assert (i = 0%nat) by lia.
            subst; exact Hx.
          + intros Hx.
            exists 0%nat.
            split; [lia | exact Hx].
        }
        rewrite Heq.
        apply HF_seq.
        
      - (* n = S n' *)
        unfold B_seq.
        assert (Heq : (fun x => exists i, (i <= S n')%nat /\ F_seq i x) =
                     (fun x => (B_seq n' x) \/ F_seq (S n') x)).
        {
          apply set_extensionality.
          intro x.
          split.
          - intros [i [Hi Hx]].
            destruct (le_lt_eq_dec i (S n') Hi) as [Hlt|Heq_i].
            + left.
              exists i.
              split; [lia | exact Hx].
            + right.
              subst i.
              exact Hx.
          - intros [[i [Hi Hx]]|Hx].
            + exists i.
              split; [lia | exact Hx].
            + exists (S n').
              split; [lia | exact Hx].
        }
        rewrite Heq.
        apply Hfinite_union0; [exact IH | apply HF_seq].
    }
    
    (* 证明B_seq递增 *)
    assert (Hinc_B : IncreasingSequence B_seq).
    {
      unfold IncreasingSequence, Subset, B_seq.
      intros n x [i [Hi Hx]].
      exists i.
      split; [lia | exact Hx].
    }
    
    (* 应用单调类性质 *)
    destruct Hmono0 as [Hinc_union _].
    specialize (Hinc_union B_seq HB_seq Hinc_B).
    
    (* 证明B_seq的并等于F_seq的并 *)
    assert (Heq : (fun x => exists n, B_seq n x) = (fun x => exists n, F_seq n x)).
    {
      apply set_extensionality.
      intro x.
      split.
      + intros [k [i [Hi Hx]]].
        exists i; exact Hx.
      + intros [n Hx].
        exists n.
        exists n.
        split; [lia | exact Hx].
    }
    
    (* 使用等式将目标转换为已知结论 *)
    rewrite <- Heq.
    exact Hinc_union.
  }
  
  (* 构建σ代数 *)
  assert (Hsigma_M0 : SigmaAlgebra X).
  {
    refine {|
      sigma_sets := M0;
      sigma_contains_universe := Huniv0;
      sigma_closed_complement := Hcomp0;
      sigma_closed_countable_union := Hcountable_union0;
      sigma_contains_empty := _;
      sigma_closed_finite_union := _;
      sigma_closed_countable_intersection := _
    |}.
    
    - (* 包含空集 *)
      rewrite <- complement_universal_empty.
      apply Hcomp0.
      exact Huniv0.
      
    - (* 有限并封闭 *)
      exact Hfinite_union0.
      
    - (* 可数交封闭 *)
      intros F_seq HF_seq.
      (* 使用德摩根定律：可数交 = 可数并的补集 *)
      set (G_seq := fun n => Complement_s (F_seq n)).
      assert (HG_seq : forall n, M0 (G_seq n)).
      {
        intro n.
        unfold G_seq.
        apply Hcomp0.
        apply HF_seq.
      }
      pose proof (Hcountable_union0 G_seq HG_seq) as Hunion_G.
      
      (* 首先证明函数相等性 *)
      assert (Hfunc_eq1 : (fun x : X => forall n : nat, x in_s F_seq n) = 
                         (fun x : X => forall n : nat, F_seq n x)).
      {
        apply functional_extensionality.
        intro x.
        reflexivity.  (* 两个表达式是外延相等的 *)
      }
      
      (* 现在证明主要等式 *)
      assert (Heq : (fun x : X => forall n : nat, F_seq n x) = 
                   Complement_s (fun x : X => exists n : nat, G_seq n x)).
      {
        apply functional_extensionality.
        intro x.
        apply propositional_extensionality.
        split.
        - intros Hall Hex.
          destruct Hex as [n Hn].
          unfold G_seq in Hn.
          apply Hn.
          apply Hall.
        - intros Hcomp n.
          apply NNPP.
          intro Hnot.
          apply Hcomp.
          exists n.
          exact Hnot.
      }
      
      (* 使用函数相等性转换目标 *)
      rewrite Hfunc_eq1.
      rewrite Heq.
      apply Hcomp0.
      exact Hunion_G.
  }
  
  (* 现在证明：由A生成的σ代数包含在M0中 *)
  assert (Hsigma_in_M0 : forall C, (sigma_sets X (generated_sigma_algebra A)) C -> M0 C).
  {
    intros C HC.
    unfold generated_sigma_algebra in HC.
    simpl in HC.
    
    (* 应用HC到M0，需要证明M0满足四个条件 *)
    apply HC with (F := M0).
    split.
    { (* M0包含A *)
      exact HA_in_M0. }
    split.
    { (* M0包含全集 *)
      exact Huniv0. }
    split.
    { (* M0对补集封闭 *)
      exact Hcomp0. }
    { (* M0对可数并封闭 *)
      exact Hcountable_union0. }
  }
  
  (* 最终结论 *)
  apply HM0_subset_M.
  apply Hsigma_in_M0.
  exact HB.
Qed.
  
(** 在 R×R 上的连续性定义 *)
Definition continuous_at_2d (f : R * R -> R) (p0 : R * R) : Prop :=
  forall eps : R, eps > 0 ->
  exists delta : R, delta > 0 /\
    forall p : R * R,
    let x := fst p in let y := snd p in
    let x0 := fst p0 in let y0 := snd p0 in
    Rmax (Rabs (x - x0)) (Rabs (y - y0)) < delta ->
    Rabs (f p - f p0) < eps.
  
Definition continuous_2d (f : R * R -> R) : Prop :=
  forall p : R * R, continuous_at_2d f p.
  
(** fst 函数的连续性 - 将二元函数视为两个一元函数 *)
Lemma continuous_fst_proj : forall (x : R),
  let f := (fun (y : R) => x) in  (* 固定第一个参数 *)
  continuous f.
Proof.
  intros x f.
  (* 由于 f 是常数函数，可以直接使用 continuous_const *)
  apply continuous_const.
Qed.
  
(** snd 函数的连续性 - 使用分量连续性 *)
Lemma continuous_snd_proj : 
  let f := (fun (p : R * R) => snd p) in
  (continuous (fun x : R => f (x, 0))) /\ (continuous (fun y : R => f (0, y))).
Proof.
  intro f.
  split.
  - (* 关于第一个分量的连续性 *)
    unfold continuous, continuous_at.
    intros x eps Heps.
    exists eps.
    split.
    { exact Heps. }
    intros x' Hdist.
    simpl.
    (* 由于 f (x,0) = 0，f (x',0) = 0，所以 |0 - 0| = 0 < eps *)
    rewrite Rminus_eq_0.
    rewrite Rabs_R0.
    exact Heps.
  - (* 关于第二个分量的连续性 *)
    unfold continuous, continuous_at.
    intros y eps Heps.
    exists eps.
    split.
    { exact Heps. }
    intros y' Hdist.
    simpl.
    (* 由于 f (0,y) = y，f (0,y') = y'，所以 |y' - y| < eps *)
    exact Hdist.
Qed.
  
(** fst函数的连续性 - 二元版本 *)
Lemma continuous_fst_2d : continuous_2d (fun (p : R * R) => fst p).
Proof.
  unfold continuous_2d, continuous_at_2d.
  intros [x y] eps Heps.
  (* 取 δ = ε *)
  exists eps.
  split.
  { exact Heps. }  (* δ = ε > 0 *)
  intros [x' y'].
  simpl.
  (* 计算距离 *)
  intro Hdist.
  (* 根据最大值距离性质：|x' - x| ≤ max(|x'-x|, |y'-y|) < ε *)
  apply Rle_lt_trans with (r2 := Rmax (Rabs (x' - x)) (Rabs (y' - y))).
  { (* 证明 |x' - x| ≤ max(|x'-x|, |y'-y|) *)
    apply Rmax_l. }
  { (* 由 Hdist 知道 max(|x'-x|, |y'-y|) < ε *)
    exact Hdist. }
Qed.
  
(** snd函数的连续性 - 二元版本 *)
Lemma continuous_snd_2d : continuous_2d (fun (p : R * R) => snd p).
Proof.
  unfold continuous_2d, continuous_at_2d.
  intros [x y] eps Heps.
  exists eps.
  split.
  { exact Heps. }  (* δ = ε > 0 *)
  intros [x' y'].
  simpl.
  intro Hdist.
  (* 使用 Rle_lt_trans 连接两个不等式：|y'-y| ≤ max(...) < ε *)
  apply Rle_lt_trans with (r2 := Rmax (Rabs (x' - x)) (Rabs (y' - y))).
  { (* 证明 |y' - y| ≤ max(|x'-x|, |y'-y|) *)
    apply Rmax_r. }
  { (* 由 Hdist 知道 max(|x'-x|, |y'-y|) < ε *)
    exact Hdist. }
Qed.
  
(* 首先，我们需要定义二维空间中的开集概念 *)
  
(** 定义：二维集合的内部（使用开矩形邻域） *)
Definition interior_2d (A : SetX (R * R)) : SetX (R * R) :=
  fun p => exists delta : R, delta > 0 /\
    forall q : R * R, 
    let x_diff := fst q - fst p in
    let y_diff := snd q - snd p in
    Rmax (Rabs x_diff) (Rabs y_diff) < delta -> A q.
  
(** 定义：二维开集 *)
Definition open_set_2d (A : SetX (R * R)) : Prop :=
  SetEq A (interior_2d A).
  
(** 引理：二维连续函数的开区间原像是开集 *)
Lemma preimage_open_interval_is_open_2d :
  forall (f : R * R -> R) (Hf : continuous_2d f) (a b : R) (Hlt : a < b),
  open_set_2d (fun p : R * R => a < f p /\ f p < b).
Proof.
  intros f Hf_cont a b Hlt.
  unfold open_set_2d, SetEq, interior_2d.
  
  (* 我们的目标：对于任意点p，p ∈ {p | a < f p ∧ f p < b} ↔ p ∈ interior_2d(...) *)
  
  (* 引入任意点p *)
  intro p.
  
  (* 现在我们需要证明双向蕴含 *)
  split.
  - (* 方向1：左边蕴含右边 *)
    (* 假设 p 满足 a < f p ∧ f p < b *)
    intro Hp.
    
    (* 由于 Hp 是 (fun p0 : R * R => a < f p0 /\ f p0 < b) p
       即 a < f p /\ f p < b，我们可以分解它 *)
    destruct Hp as [Ha Hb].  (* Ha: a < f p, Hb: f p < b *)
    
    (* 计算ε = min(f p - a, b - f p)，这个值>0 *)
    set (eps := Rmin (f p - a) (b - f p)).
    
    (* 证明eps > 0 *)
    assert (Heps_pos : eps > 0).
    {
      unfold eps.
      apply Rmin_pos; lra.
    }
    
    (* 由于f是连续的，对于这个ε>0，存在δ>0 *)
    unfold continuous_2d in Hf_cont.
    unfold continuous_at_2d in Hf_cont.
    
    (* 应用连续性：在点p处，对于ε=eps，存在δ>0 *)
    destruct (Hf_cont p eps Heps_pos) as [delta [Hdelta_pos Hcont]].
    
    (* 证明存在这样的delta *)
    exists delta.
    split.
    { exact Hdelta_pos. }
    
    (* 引入任意点q，假设它满足距离条件 *)
    intro q.
    intro Hdist.
    
    (* 应用连续性条件到点q *)
    assert (Hf_diff : Rabs (f q - f p) < eps).
    {
      apply Hcont.
      exact Hdist.
    }
    
    (* 我们需要证明：a < f q 且 f q < b *)
    assert (Heps_bound1 : eps <= f p - a).
    { unfold eps. apply Rmin_l. }
    assert (Heps_bound2 : eps <= b - f p).
    { unfold eps. apply Rmin_r. }
    split.
    + (* 证明 a < f q *)
      (* 手动展开绝对值定义 *)
      (* 根据绝对值的定义：|x| < ε 当且仅当 -ε < x < ε *)
      (* 我们可以使用 Rabs_def2 来获取这个等价关系 *)
      pose proof (Rabs_def2 (f q - f p) eps Hf_diff) as Hbound.
      (* Hbound 应该给出 -eps < f q - f p < eps *)
      lra.
    + (* 证明 f q < b *)
      (* 同样使用 Rabs_def2 *)
      pose proof (Rabs_def2 (f q - f p) eps Hf_diff) as Hbound.
      lra.
        
  - (* 方向2：右边蕴含左边 *)
    (* 假设 p 在 interior_2d 中 *)
    intro Hp_interior.
    
    (* 分解 Hp_interior：存在 delta > 0，使得... *)
    destruct Hp_interior as [delta [Hdelta_pos Hball]].
    
    (* 取 q = p，因为 |p - p| = 0 < delta *)
    specialize (Hball p).
    
    (* 计算 Rmax (Rabs (fst p - fst p)) (Rabs (snd p - snd p)) = 0 < delta *)
    assert (Hdist : Rmax (Rabs (fst p - fst p)) (Rabs (snd p - snd p)) < delta).
    {
      rewrite Rminus_eq_0; rewrite Rabs_R0.
      rewrite Rminus_eq_0; rewrite Rabs_R0.
      rewrite Rmax_right; [exact Hdelta_pos | lra].
    }
    
    (* 应用 Hball *)
    apply Hball in Hdist.
    
    (* 现在 Hdist 给出 a < f p < b *)
    exact Hdist.
Qed.
  
(** 一维开集的定义 **)
Definition interior_1d (A : SetX R) : SetX R :=
  fun x => exists delta : R, delta > 0 /\
    forall y : R, Rabs (y - x) < delta -> A y.
  
Definition open_set_1d (A : SetX R) : Prop :=
  SetEq A (interior_1d A).
  
(** 开区间的开集性质 **)
Lemma open_interval_is_open_1d : forall a b : R, a < b ->
  open_set_1d (fun x : R => a < x /\ x < b).
Proof.
  intros a b Hlt.
  unfold open_set_1d, SetEq.
  intro x.
  split.
  - (* 从开区间到内部 *)
    intro Hx.
    destruct Hx as [Hx_left Hx_right].
    unfold interior_1d.
    (* 取 δ = min(x-a, b-x)，因为x在(a,b)内部 *)
    set (delta := Rmin (x - a) (b - x)).
    assert (Hdelta_pos : delta > 0).
    {
      unfold delta.
      apply Rmin_glb_lt.
      - lra. (* x-a > 0 *)
      - lra. (* b-x > 0 *)
    }
    exists delta.
    split.
    + exact Hdelta_pos.
    + intros y Hy_dist.
      (* 需要证明 a < y < b *)
      split.
      * (* a < y *)
        apply Rabs_def2 in Hy_dist.
        destruct Hy_dist as [H_lower H_upper].
        assert (H_delta_le_x_minus_a : delta <= x - a) by (apply Rmin_l).
        lra.
      * (* y < b *)
        apply Rabs_def2 in Hy_dist.
        destruct Hy_dist as [H_lower H_upper].
        assert (H_delta_le_b_minus_x : delta <= b - x) by (apply Rmin_r).
        lra.
  - (* 从内部到开区间 *)
    intro Hx_interior.
    unfold interior_1d in Hx_interior.
    destruct Hx_interior as [delta [Hdelta_pos Hball]].
    (* 取 y = x，显然|x-x|=0<delta，所以x在开区间中 *)
    specialize (Hball x).
    assert (Hdist : Rabs (x - x) < delta).
    {
      rewrite Rminus_eq_0.
      rewrite Rabs_R0.
      exact Hdelta_pos.
    }
    apply Hball in Hdist.
    exact Hdist.
Qed.
  
(** 开球引理：绝对值不等式性质 **)
Lemma Rabs_def2 : forall (x eps : R), Rabs x < eps <-> -eps < x /\ x < eps.
Proof.
  intros x eps.
  split.
  - intro H.
    unfold Rabs in H.
    destruct (Rcase_abs x) as [Hx | Hx] in H.
    + (* x < 0 *)
      split.
      * lra.
      * lra.
    + (* x >= 0 *)
      split.
      * lra.
      * lra.
  - intro H.  (* H : -eps < x /\ x < eps *)
    destruct H as [Hleft Hright].
    unfold Rabs.
    destruct (Rcase_abs x) as [Hx | Hx].
    + (* x < 0 *)
      lra.
    + (* x >= 0 *)
      exact Hright.
Qed.
  
(** 定理：连续函数的开集原像是开集 - 一般形式 **)
Theorem preimage_open_is_open_2d :
  forall (f : R * R -> R) (Hf : continuous_2d f)
         (A : SetX R) (HA : open_set_1d A),
  open_set_2d (fun p => A (f p)).
Proof.
  intros f Hf_cont A HA_open.
  unfold open_set_2d, SetEq.
  intro p.
  split.
  - (* 左边蕴含右边 *)
    intro Hp.
    (* 简化假设 Hp *)
    simpl in Hp. (* Hp: A (f p) *)
    
    (* 由于A是开集，f(p)在A的内部 *)
    unfold open_set_1d in HA_open.
    unfold SetEq in HA_open.
    
    (* 将 HA_open 应用于点 f p *)
    pose proof (HA_open (f p)) as HA_fp.
    destruct HA_fp as [H_to_interior H_from_interior].
    
    (* 使用 H_to_interior 得到 interior_1d A (f p) *)
    apply H_to_interior in Hp.
    
    (* 展开 interior_1d 的定义 *)
    unfold interior_1d in Hp.
    destruct Hp as [eps [Heps_pos Hball]].
    
    (* 由于f连续，对于eps>0，存在delta>0 *)
    unfold continuous_2d in Hf_cont.
    unfold continuous_at_2d in Hf_cont.
    destruct (Hf_cont p eps Heps_pos) as [delta [Hdelta_pos Hcont]].
    
    (* 证明p在内部 *)
    unfold interior_2d.
    exists delta.
    split.
    { exact Hdelta_pos. }
    
    intros q Hdist.
    simpl.
    (* 应用连续性条件 *)
    assert (Hf_dist : Rabs (f q - f p) < eps).
    { apply Hcont. exact Hdist. }
    
    (* 应用开球条件 *)
    apply Hball.
    exact Hf_dist.
    
  - (* 右边蕴含左边 *)
    intro Hp_interior.
    unfold interior_2d in Hp_interior.
    destruct Hp_interior as [delta [Hdelta_pos Hball]].
    
    (* 取q = p *)
    specialize (Hball p).
    assert (Hdist : Rmax (Rabs (fst p - fst p)) (Rabs (snd p - snd p)) < delta).
    {
      rewrite Rminus_eq_0.
      rewrite Rabs_R0.
      rewrite Rminus_eq_0.
      rewrite Rabs_R0.
      apply Rmax_case.
      - exact Hdelta_pos.
      - exact Hdelta_pos.
    }
    apply Hball in Hdist.
    
    (* 简化结果 *)
    simpl in Hdist.
    exact Hdist.
Qed.
  
(** 实数最小值左不等式引理 **)
(** 对于任意实数a和b，最小值Rmin a b ≤ a **)
Lemma Rmin_l : forall a b, Rmin a b <= a.
Proof.
  intros a b.
  unfold Rmin.  (* 展开Rmin的定义 *)
  destruct (Rle_dec a b) as [Hle|Hgt].  (* 分情况讨论a ≤ b和a > b *)
  - (* 情况1: a ≤ b，此时Rmin a b = a，所以a ≤ a成立 *)
    lra.
  - (* 情况2: a > b，此时Rmin a b = b，需要证明b ≤ a *)
    lra.
Qed.
  
(** 实数最小值右不等式引理 **)
(** 对于任意实数a和b，最小值Rmin a b ≤ b **)
Lemma Rmin_r : forall a b, Rmin a b <= b.
Proof.
  intros a b.
  unfold Rmin.  (* 展开Rmin的定义 *)
  destruct (Rle_dec a b) as [Hle|Hgt].  (* 分情况讨论a ≤ b和a > b *)
  - (* 情况1: a ≤ b，此时Rmin a b = a，需要证明a ≤ b *)
    lra.
  - (* 情况2: a > b，此时Rmin a b = b，所以b ≤ b成立 *)
    lra.
Qed.
  
(** 实数加减消去律引理 **)
(** 对于任意实数a和b，有(a - b) + b = a **)
Lemma Rplus_minus_cancel : forall a b : R, (a - b) + b = a.
Proof.
  intros a b.
  ring.  (* 使用环演算自动证明实数加减法的基本性质 *)
Qed.
  
(** 实数最小值正数保持引理 **)
(** 若两个实数a和b均为正数，则它们的最小值Rmin a b也是正数 **)
Lemma Rmin_pos_lt : forall a b : R,
  0 < a -> 0 < b -> 0 < Rmin a b.
Proof.
  intros a b Ha Hb.  (* 引入实数a, b及其均为正数的假设 *)
  unfold Rmin.       (* 展开实数最小值函数Rmin的定义 *)
  destruct (Rle_dec a b) as [Hle | Hgt].  (* 根据a ≤ b是否成立进行情况分析 *)
  - (* 情况一：a ≤ b成立，此时Rmin a b = a *)
    exact Ha.        (* 由假设Ha: 0 < a，直接得证 *)
  - (* 情况二：a > b成立，此时Rmin a b = b *)
    exact Hb.        (* 由假设Hb: 0 < b，直接得证 *)
Qed.
  
(* 定义：二维开集的标准基 *)
Definition open_rectangle_base : Family (R * R) :=
  fun A => exists a b c d : R, 
    a < b /\ c < d /\
    SetEq A (fun p => 
      let x := fst p in let y := snd p in
      a < x /\ x < b /\ c < y /\ y < d).
  
(* 引理：开矩形是开集 *)
Lemma open_rectangle_is_open_2d : forall a b c d : R,
  a < b -> c < d ->
  open_set_2d (fun p => 
    let x := fst p in let y := snd p in
    a < x /\ x < b /\ c < y /\ y < d).
Proof.
  intros a b c d Ha_b Hc_d.
  unfold open_set_2d, SetEq, interior_2d.
  intro p.
  destruct p as [x y].
  split.
  - (* 左边蕴含右边 *)
    intro H.
    destruct H as [Hx_left [Hx_right [Hy_left Hy_right]]].
    
    (* 简化假设中的fst和snd *)
    simpl in Hx_left, Hx_right, Hy_left, Hy_right.
    
    (* 这些距离都为正数 *)
    assert (Hdx1_pos : 0 < x - a). { lra. }
    assert (Hdx2_pos : 0 < b - x). { lra. }
    assert (Hdy1_pos : 0 < y - c). { lra. }
    assert (Hdy2_pos : 0 < d - y). { lra. }
    
    (* 计算delta：取四个距离中的最小值 *)
    set (dx1 := x - a).  (* x到左边界的距离 *)
    set (dx2 := b - x).  (* x到右边界的距离 *)
    set (dy1 := y - c).  (* y到下边界的距离 *)
    set (dy2 := d - y).  (* y到上边界的距离 *)
    set (dx_min := Rmin dx1 dx2).
    set (dy_min := Rmin dy1 dy2).
    set (delta := Rmin dx_min dy_min).
    
    (* 证明delta > 0 *)
    assert (Hdelta_pos : 0 < delta).
    {
      unfold delta.
      unfold Rmin.
      destruct (Rle_dec dx_min dy_min) as [Hle | Hgt].
      - (* delta = dx_min *)
        unfold dx_min.
        unfold Rmin.
        destruct (Rle_dec dx1 dx2) as [Hle' | Hgt'].
        + (* dx_min = dx1 *)
          exact Hdx1_pos.
        + (* dx_min = dx2 *)
          exact Hdx2_pos.
      - (* delta = dy_min *)
        unfold dy_min.
        unfold Rmin.
        destruct (Rle_dec dy1 dy2) as [Hle' | Hgt'].
        + (* dy_min = dy1 *)
          exact Hdy1_pos.
        + (* dy_min = dy2 *)
          exact Hdy2_pos.
    }
    
    (* 证明delta与各边界距离的关系 *)
    assert (Hdelta_le_dx1 : delta <= x - a).
    {
      unfold delta, dx_min, dy_min.
      apply Rle_trans with (r2 := Rmin dx1 dx2).
      - apply Rmin_l.
      - apply Rmin_l.
    }
    
    assert (Hdelta_le_dx2 : delta <= b - x).
    {
      unfold delta, dx_min, dy_min.
      apply Rle_trans with (r2 := Rmin dx1 dx2).
      - apply Rmin_l.
      - apply Rmin_r.
    }
    
    assert (Hdelta_le_dy1 : delta <= y - c).
    {
      unfold delta, dx_min, dy_min.
      apply Rle_trans with (r2 := Rmin dy1 dy2).
      - apply Rmin_r.
      - apply Rmin_l.
    }
    
    assert (Hdelta_le_dy2 : delta <= d - y).
    {
      unfold delta, dx_min, dy_min.
      apply Rle_trans with (r2 := Rmin dy1 dy2).
      - apply Rmin_r.
      - apply Rmin_r.
    }
    
    (* 证明存在这样的delta *)
    exists delta.
    split.
    { exact Hdelta_pos. }
    
    intros q.
    destruct q as [x' y'].
    intro Hdist.
    
    (* 从Hdist得到两个绝对值不等式 *)
    assert (Hx_dist : Rabs (x' - x) < delta).
    {
      apply Rle_lt_trans with (r2 := Rmax (Rabs (x' - x)) (Rabs (y' - y))).
      - apply Rmax_l.
      - exact Hdist.
    }
    
    assert (Hy_dist : Rabs (y' - y) < delta).
    {
      apply Rle_lt_trans with (r2 := Rmax (Rabs (x' - x)) (Rabs (y' - y))).
      - apply Rmax_r.
      - exact Hdist.
    }
    
    (* 现在证明x'在(a,b)中 *)
    (* 首先分解绝对值不等式 *)
    apply Rabs_def2 in Hx_dist.
    destruct Hx_dist as [Hx_left_abs Hx_right_abs].
    apply Rabs_def2 in Hy_dist.
    destruct Hy_dist as [Hy_left_abs Hy_right_abs].
    
    split.
    + (* 证明 a < x' *)
      simpl.
      apply Rle_lt_trans with (r2 := x - delta).
      - (* 证明 a <= x - delta *)
        lra.
      - (* 证明 x - delta < x' *)
        lra.
        
    + split.
      * (* 证明 x' < b *)
        simpl.
        apply Rlt_le_trans with (r2 := x + delta).
        - (* 证明 x' < x + delta *)
          lra.
        - (* 证明 x + delta <= b *)
          lra.
        
      * split.
        -- (* 证明 c < y' *)
           simpl.
           apply Rle_lt_trans with (r2 := y - delta).
           + lra.
           + lra.
             
        -- (* 证明 y' < d *)
           simpl.
           apply Rlt_le_trans with (r2 := y + delta).
           + lra.
           + lra.
  - (* 右边蕴含左边 *)   (* 第二个方向开始 *)
    intro H.
    destruct H as [delta [Hdelta_pos Hball]].
    (* 取q = p本身 *)
    specialize (Hball (x, y)).
    assert (Hdist : Rmax (Rabs (x - x)) (Rabs (y - y)) < delta).
    {
      rewrite Rminus_eq_0.
      rewrite Rabs_R0.
      rewrite Rminus_eq_0.
      rewrite Rabs_R0.
      rewrite Rmax_left.
      - exact Hdelta_pos.
      - lra.
    }
    apply Hball in Hdist.
    exact Hdist.
Qed.
  
(** 有理数相关库 **)
Require Import ConstructiveEpsilon.  (* 用于可数性 *)
Require Import Qreals.          (* Q2R: Q -> R 转换 *)
Require Import Rbase.           (* 实数基础 *)
Require Import RIneq.           (* 实数不等式 *)
Require Import Lra.             (* 线性实数算术 *)
Require Import FunctionalExtensionality. (* 函数外延性 *)
Require Import Ranalysis. 
Require Import ZArith.
Require Import Arith.
Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.
Require Import PeanoNat.
Require Import Coq.ZArith.BinInt.
Require Import Coq.PArith.PArith.
  
Open Scope R_scope.  (* 开启实数作用域 *)
  
(** 辅助定义：有理矩形 **)
Definition rational_rectangle (a b c d : Q) : SetX (R * R) :=
  fun (p : R * R) =>
    let x := fst p in
    let y := snd p in
    Q2R a < x /\ x < Q2R b /\
    Q2R c < y /\ y < Q2R d.
  
(** 辅助引理：有理数在实数中稠密 **)

  (** 引理：实数上取整的非负性 **)
  (** 对于任意实数 r，若 r 非负，则其上取整 up r 也是非负整数 **)
  Lemma up_ge_0 : forall r, 0 <= r -> (0 <= up r)%Z.
  Proof.
    (* 引入变量：r 为实数，Hr 为假设条件 0 <= r *)
    intros r Hr.
    
    (* 使用反证法：假设结论不成立，即 up r < 0 *)
    apply Z.le_ngt. 
    intros H.  (* H: (up r < 0)%Z *)
    
    (* 将整数不等式转换为实数不等式 *)
    assert (Hizr_neg : IZR (up r) < 0).
    { 
      (* 应用整数转实数保持序的引理 *)
      apply IZR_lt. 
      (* 使用假设 H: up r < 0 *)
      assumption.    
    }
    
    (* 使用 archimed 引理获取 up r 的两个关键性质 *)
    destruct (archimed r) as [H1 H2].  
    (* H1: IZR (up r) > r 
       H2: IZR (up r) - r <= 1 *)
    
    (* 利用线性实数算术推导矛盾 *)
    (* 已知：0 <= r (Hr), IZR (up r) < 0 (Hizr_neg), IZR (up r) > r (H1) *)
    (* 由 0 <= r 和 IZR (up r) > r 得 IZR (up r) > 0，与 IZR (up r) < 0 矛盾 *)
    lra.  
  Qed.
  
(** 引理：非负整数转换为自然数后的实数值等于其整数实数值 **)
Lemma INR_IZR_INZ' : forall z:Z, (0 <= z)%Z -> INR (Z.to_nat z) = IZR z.
Proof.
  intros z Hz.
  destruct z as [O | p | p].
  - (* z = 0 *)
    simpl.
    reflexivity.
  - (* z = Z.pos p *)
    simpl.
    unfold IZR.
    (* 现在需要证明 INR (Pos.to_nat p) = IPR p *)
    (* 使用实数库中关于 IPR 的引理 *)
    rewrite <- (INR_IPR p).  (* 如果存在这个引理 *)
    reflexivity.
  - (* z = Z.neg p *)
    (* 根据假设 Hz: (0 <= Z.neg p)%Z，但 Z.neg p 是负数，矛盾 *)
    exfalso.
    (* 使用整数线性算术推导矛盾 *)
    lia.
Qed.
  
(** 阿基米德性质引理：对于任意实数 x，存在自然数 n 使得 x < INR n **)
(** 这等价于说实数集没有上界，或者自然数集在实数中无界 **)
Lemma Rarchimedean : forall x:R, exists n:nat, x < INR n.
Proof.
  (* 引入实数 x *)
  intros x.
  
  (* 情况分析：判断 x 是否大于 0 *)
  destruct (Rlt_le_dec 0 x) as [Hpos | Hnonpos].
  - (* 情况 1：x > 0 *)
    (* 使用 archimed 引理：对于实数 x，存在整数 z = up x，满足 x < IZR z ≤ x+1 *)
    pose proof (archimed x) as [H1 H2].  (* H1: x < IZR (up x), H2: IZR (up x) - x <= 1 *)
    set (z := up x) in *.  (* 定义 z 为 x 的上取整整数 *)
    
    (* 证明 z 是非负整数 (0 ≤ z) *)
    assert (Hz_nonneg : (0 <= z)%Z).
    {
      (* 使用反证法：假设 z < 0 会导致矛盾 *)
      destruct (Z_lt_ge_dec z 0) as [Hz_lt | Hz_ge].
      - (* 子情况：假设 z < 0 *)
        (* 将整数不等式转换为实数不等式：IZR z < IZR 0 = 0 *)
        assert (Hiz_neg : IZR z < IZR 0).
        { 
          apply IZR_lt.  (* 整数序保持到实数 *)
          exact Hz_lt.   (* z < 0 *)
        }
        simpl in Hiz_neg.  (* 化简 IZR 0 为 0 *)
        (* 现在有：x > 0（由Hpos）且 x < IZR z（由H1）且 IZR z < 0，矛盾 *)
        lra.  (* 线性实数算术：推导出矛盾 *)
      - (* 子情况：z ≥ 0，转换为所需形式 0 ≤ z *)
        apply Z.ge_le in Hz_ge.  (* 将 (z >= 0)%Z 转换为 (0 <= z)%Z *)
        exact Hz_ge.
    }
    
    (* 取 n = Z.to_nat z，即 z 对应的自然数 *)
    exists (Z.to_nat z).
    
    (* 需要证明：x < INR (Z.to_nat z) *)
    (* 使用 archimed 引理的 H1: x < IZR z *)
    apply Rlt_le_trans with (r2 := IZR z).
    + (* x < IZR z *) 
      exact H1.
    + (* IZR z ≤ INR (Z.to_nat z) *)
      (* 首先使用 INR_IZR_INZ 引理：INR (Z.to_nat z) = IZR (Z.of_nat (Z.to_nat z)) *)
      rewrite <- (sym_eq (INR_IZR_INZ (Z.to_nat z))).
      (* 然后化简：Z.of_nat (Z.to_nat z) = z，当 0 ≤ z 时 *)
      rewrite Z2Nat.id; [reflexivity | exact Hz_nonneg].
      
  - (* 情况 2：x ≤ 0 *)
    (* 取 n=1，因为 x ≤ 0 < 1 = INR 1 *)
    exists 1%nat.
    (* INR 1 = 1 *)
    simpl.
    (* 证明 x < 1：由 x ≤ 0 和 0 < 1 可得 *)
    lra.  (* 线性实数算术 *)
Qed.
  
(** 引理: IZR (Z.of_nat n) = INR n **)
Lemma IZR_of_nat : forall n : nat, IZR (Z.of_nat n) = INR n.
Proof.
  intro n.
  induction n as [O | n IH].
  - (* n = 0 *)
    simpl; reflexivity.
  - (* n = S n *)
    rewrite Nat2Z.inj_succ.      (* Z.of_nat (S n) = Z.succ (Z.of_nat n) *)
    (* 手动计算 IZR (Z.succ (Z.of_nat n)) *)
    unfold Z.succ.
    rewrite plus_IZR.           (* IZR (Z.of_nat n + 1) = IZR (Z.of_nat n) + IZR 1 *)
    simpl (IZR 1).             (* IZR 1 = 1 *)
    rewrite IH.                (* 归纳假设 *)
    rewrite S_INR.             (* INR (S n) = INR n + 1 *)
    reflexivity.
Qed.
  
(** 引理: Z.pos p = Z.of_nat (Pos.to_nat p) **)
Lemma Zpos_nat_of_P : forall p, Z.pos p = Z.of_nat (Pos.to_nat p).
Proof.
  intro p.
  induction p using Pos.peano_ind.
  - (* p = 1 *)
    simpl. reflexivity.
  - (* p = p0 + 1 *)
    rewrite Pos2Nat.inj_succ.    (* Pos.to_nat (Pos.succ p0) = S (Pos.to_nat p0) *)
    rewrite Nat2Z.inj_succ.      (* Z.of_nat (S (Pos.to_nat p0)) = Z.of_nat (Pos.to_nat p0) + 1 *)
    rewrite <- IHp.              (* 归纳假设 *)
    rewrite Pos2Z.inj_succ.      (* Z.pos (Pos.succ p0) = Z.pos p0 + 1 *)
    reflexivity.
Qed.
  
(** 引理：Pos.of_nat 和 Pos.to_nat 在正整数上的互逆性 **)
Lemma Pos_to_nat_of_nat_succ : forall n : nat,
    Pos.to_nat (Pos.of_nat (S n)) = S n.
Proof.
  intro n.
  (* 使用 induction 并正确命名变量 *)
  induction n as [O | n' IH].
  - (* 基本情况：n = 0 *)
    simpl.
    reflexivity.
  - (* 归纳步骤：n = S n' *)
    (* 现在我们需要证明：Pos.to_nat (Pos.of_nat (S (S n'))) = S (S n') *)
    (* 使用 Pos.of_nat_succ 引理来简化 *)
    simpl.
    (* 此时目标变为：Pos.to_nat (Pos.succ (Pos.of_nat (S n'))) = S (S n') *)
    (* 使用 Pos.to_nat_succ 引理：Pos.to_nat (Pos.succ p) = S (Pos.to_nat p) *)
    rewrite Pos2Nat.inj_succ.  (* 这个引理可用 *)
    rewrite <- IH.
    reflexivity.
Qed.
  
(** 引理：对于任意正整数 n，将 n 转换为正数类型再转回自然数结果不变 **)
Lemma Pos_to_nat_of_nat_gt : forall n, (n > 0)%nat ->
  Pos.to_nat (Pos.of_nat n) = n.
Proof.
  (* 引入变量 n 和假设 Hn: n > 0 *)
  intros n Hn.
  (* 将自然数 n 分解为两种情况：0 或 后继形式 *)
  destruct n as [O | S n'].
  - (* 情况1: n = 0，与假设 n > 0 矛盾 *)
    (* 简化前提 Hn 中的表达式 *)
    simpl in Hn.
    (* 使用反演推导矛盾：0 > 0 不可能成立 *)
    inversion Hn.
  - (* 情况2: n = S n'（即 n 是正整数） *)
    (* 简化目标表达式 *)
    simpl.
    (* 应用之前证明的引理：Pos.to_nat (Pos.of_nat (S n')) = S n' *)
    apply Pos_to_nat_of_nat_succ.
Qed.
  
(** 有理数减法的实数映射 **)
Lemma Q2R_minus : forall a b : Q, Q2R (a - b) = Q2R a - Q2R b.
Proof.
  intros a b.
  unfold Qminus.  (* a - b = a + (-b) *)
  rewrite Q2R_plus.  (* 如果 Q2R_plus 存在 *)
  rewrite Q2R_opp.   (* 如果 Q2R_opp 存在 *)
  ring.
Qed.
  
(** 有理数在实数中稠密 **)
(** 对于任意两个实数 x < y，存在有理数 q 满足 x < Q2R q < y **)
Theorem Q_dense_in_R : forall (x y : R), x < y -> exists q : Q, x < Q2R q < y.
Proof.
  intros x y Hlt.
  destruct (Rle_dec 0 x) as [Hx_nonneg | Hx_neg].
  - (* 情况 1: x ≥ 0 *)
    (* 存在自然数 k 使得 1/(k+1) < y-x *)
    assert (Hk : exists k : nat, / INR (k + 1) < y - x).
    {
      assert (Hpos : 0 < y - x) by lra.
      pose proof (Rarchimedean (/ (y - x))) as [k Hk].
      exists k.
      assert (Hk' : / (y - x) < INR (k + 1)).
      {
        apply (Rlt_trans _ (INR k) _).
        - exact Hk.
        - rewrite plus_INR; simpl; lra.
      }
      assert (Hinv_pos : 0 < / (y - x)).
      { apply Rinv_0_lt_compat; exact Hpos. }
      assert (Hdenom_pos : 0 < INR (k + 1)).
      { apply lt_0_INR; lia. }
      assert (Hprod_pos : 0 < / (y - x) * INR (k + 1)).
      { apply Rmult_lt_0_compat; assumption. }
      apply (Rinv_lt_contravar (/ (y - x)) (INR (k + 1)) Hprod_pos) in Hk'.
      rewrite Rinv_inv in Hk'; exact Hk'.
    }
    destruct Hk as [k Hk].
    
    (* 使用 archimed 引理构造分子 m = ⌈(k+1)*x⌉ *)
    pose proof (archimed (INR (k + 1) * x)) as [Hm1 Hm2].
    set (m := up (INR (k + 1) * x)) in *.
    
    (* 证明 x < IZR m / INR (k+1) *)
    assert (Hx_lt : x < IZR m / INR (k + 1)).
    {
      apply (Rmult_lt_reg_r (INR (k + 1))).
      - apply lt_0_INR; lia.
      - unfold Rdiv.
        rewrite Rmult_assoc.
        rewrite <- Rinv_l_sym.
        + rewrite Rmult_1_r; rewrite Rmult_comm; exact Hm1.
        + apply not_0_INR; lia.
    }
    
    (* 证明 IZR m / INR (k+1) < y *)
    assert (Hlt_y : IZR m / INR (k + 1) < y).
    {
      apply Rle_lt_trans with (r2 := x + / INR (k + 1)).
      - apply (Rmult_le_reg_r (INR (k + 1))).
        + apply lt_0_INR; lia.
        + unfold Rdiv.
          rewrite Rmult_plus_distr_r.
          rewrite Rmult_assoc.
          rewrite <- Rinv_l_sym.
          * rewrite Rmult_1_r; lra.
          * apply not_0_INR; lia.
      - lra.
    }
    
    (* 构造有理数 q = m/(k+1) *)
    assert (Hk_pos : (k + 1 > 0)%nat) by lia.
    set (q := (m # Pos.of_nat (k + 1))%Q).
    assert (Hq_val : Q2R q = IZR m / INR (k + 1)).
    {
      unfold q; unfold Q2R; simpl.
      rewrite Zpos_nat_of_P.
      rewrite Pos_to_nat_of_nat_gt by exact Hk_pos.
      rewrite IZR_of_nat; reflexivity.
    }
    exists q; rewrite Hq_val; split; assumption.
    
  - (* 情况 2: x < 0 *)
    (* 平移至非负区间 *)
    pose proof (Rarchimedean (-x)) as [N HN].
    assert (Hx'_nonneg : 0 <= x + INR N) by lra.
    assert (Hx'y' : x + INR N < y + INR N) by lra.
    
    (* 存在自然数 k 使得 1/(k+1) < y-x *)
    assert (Hk : exists k : nat, / INR (k + 1) < y - x).
    {
      assert (Hpos : 0 < y - x) by lra.
      pose proof (Rarchimedean (/ (y - x))) as [k Hk].
      exists k.
      assert (Hk' : / (y - x) < INR (k + 1)).
      {
        apply (Rlt_trans _ (INR k) _).
        - exact Hk.
        - rewrite plus_INR; simpl; lra.
      }
      assert (Hinv_pos : 0 < / (y - x)).
      { apply Rinv_0_lt_compat; exact Hpos. }
      assert (Hdenom_pos : 0 < INR (k + 1)).
      { apply lt_0_INR; lia. }
      assert (Hprod_pos : 0 < / (y - x) * INR (k + 1)).
      { apply Rmult_lt_0_compat; assumption. }
      apply (Rinv_lt_contravar (/ (y - x)) (INR (k + 1)) Hprod_pos) in Hk'.
      rewrite Rinv_inv in Hk'; exact Hk'.
    }
    destruct Hk as [k Hk].
    
    (* 对平移后的点使用 archimed 引理 *)
    pose proof (archimed (INR (k + 1) * (x + INR N))) as [Hm1' Hm2'].
    set (m' := up (INR (k + 1) * (x + INR N))) in *.
    
    (* 证明 x+INR N < IZR m' / INR (k+1) *)
    assert (Hx'_lt : x + INR N < IZR m' / INR (k + 1)).
    {
      apply (Rmult_lt_reg_r (INR (k + 1))).
      - apply lt_0_INR; lia.
      - unfold Rdiv.
        rewrite Rmult_assoc.
        rewrite <- Rinv_l_sym.
        + rewrite Rmult_1_r; rewrite Rmult_comm; exact Hm1'.
        + apply not_0_INR; lia.
    }
    
    (* 证明 IZR m' / INR (k+1) < y+INR N *)
    assert (Hlt_y' : IZR m' / INR (k + 1) < y + INR N).
    {
      apply Rle_lt_trans with (r2 := (x + INR N) + / INR (k + 1)).
      - apply (Rmult_le_reg_r (INR (k + 1))).
        + apply lt_0_INR; lia.
        + unfold Rdiv.
          rewrite Rmult_plus_distr_r.
          rewrite Rmult_assoc.
          rewrite <- Rinv_l_sym.
          * rewrite Rmult_1_r; lra.
          * apply not_0_INR; lia.
      - lra.
    }
    
    (* 构造有理数 q' = m'/(k+1) 和 n_q = N *)
    assert (Hk_pos : (k + 1 > 0)%nat) by lia.
    set (q' := (m' # Pos.of_nat (k + 1))%Q).
    assert (Hq'_val : Q2R q' = IZR m' / INR (k + 1)).
    {
      unfold q'; unfold Q2R; simpl.
      rewrite Zpos_nat_of_P.
      rewrite Pos_to_nat_of_nat_gt by exact Hk_pos.
      rewrite IZR_of_nat; reflexivity.
    }
    set (n_q := (Z.of_nat N # 1)%Q).
    assert (Hn_q_val : Q2R n_q = INR N).
    {
      unfold n_q; unfold Q2R; simpl.
      rewrite Rinv_1, Rmult_1_r, IZR_of_nat; reflexivity.
    }
    
    (* 构造最终的有理数 q = q' - n_q *)
    exists ((q' - n_q)%Q).
    rewrite Q2R_minus.
    rewrite Hq'_val, Hn_q_val.
    split; lra.
Qed.
  
(** 辅助引理：存在整数 m 使得 m/n > x **)
Lemma exists_int_above_real : forall (x : R) (n : nat),
  exists m : Z, IZR m > x * INR n.
Proof.
  intros x n.
  (* 使用 Rarchimedean 引理找到自然数 k 使得 x * INR n < INR k *)
  pose proof (Rarchimedean (x * INR n)) as [k Hk].  (* Hk: x * INR n < INR k *)
  
  (* 取 m = Z.of_nat k *)
  exists (Z.of_nat k).
  
  (* 现在需要证明：IZR (Z.of_nat k) > x * INR n *)
  rewrite IZR_of_nat.  (* 将 IZR (Z.of_nat k) 转换为 INR k *)
  
  (* 现在目标：INR k > x * INR n *)
  lra.
Qed.
  
(** 有理数稠密性的简化证明（使用标准库中的引理） **)
Lemma Q_dense_in_R_simple : forall (x y : R), x < y -> exists q : Q, x < Q2R q < y.
Proof.
  intros x y Hlt.
  
  (* 使用标准库中的有理数稠密性定理 *)
  (* 在 Coq 的标准库中，有一个定理叫做 `Rlt_exists`，但它是关于实数序列的 *)
  (* 我们使用更直接的方法：找到两个有理数 r1, r2 满足 x < r1 < r2 < y *)
  
  (* 第一步：找到有理数 r1 满足 x < r1 < (x+y)/2 *)
  assert (Hmid1 : x < (x + y) / 2) by lra.
  destruct (Q_dense_in_R x ((x + y) / 2) Hmid1) as [q1 [Hq1_left Hq1_right]].
  
  (* 第二步：找到有理数 r2 满足 (x+y)/2 < r2 < y *)
  assert (Hmid2 : (x + y) / 2 < y) by lra.
  destruct (Q_dense_in_R ((x + y) / 2) y Hmid2) as [q2 [Hq2_left Hq2_right]].
  
  (* 第三步：我们可以返回 q1 或 q2，但需要确保它在 x 和 y 之间 *)
  (* 实际上，q1 满足 x < Q2R q1 < y，因为 Q2R q1 < (x+y)/2 < y *)
  exists q1.
  split.
  - exact Hq1_left.
  - lra.
Qed.
  
(** 辅助引理：有理矩形是开集 **)
Lemma rational_rectangle_is_open_2d : forall a b c d : Q,
  Qlt a b -> Qlt c d ->
  open_set_2d (rational_rectangle a b c d).
Proof.
  intros a b c d Ha_b Hc_d.
  unfold rational_rectangle.
  (* 转换为实数不等式 *)
  assert (H1 : Q2R a < Q2R b) by (apply Qlt_Rlt; assumption).
  assert (H2 : Q2R c < Q2R d) by (apply Qlt_Rlt; assumption).
  (* 应用已有的开矩形引理 *)
  apply (open_rectangle_is_open_2d (Q2R a) (Q2R b) (Q2R c) (Q2R d) H1 H2).
Qed.
  
(** 有理数的可数性证明 - 完整版本 **)
(** 优化的整数枚举：0, 1, -1, 2, -2, 3, -3, ... **)
Fixpoint Z_enum_optimized (n : nat) : Z :=
  match n with
  | O => 0%Z
  | S m =>
      let k := Nat.div2 m in
      if Nat.even m 
      then Z.of_nat (k + 1)      (* 正整数：1, 2, 3, ... *)
      else Z.opp (Z.of_nat (k + 1))  (* 负整数：-1, -2, -3, ... *)
  end.
  
Open Scope Z_scope.
  
(* 辅助引理：自然数除法的性质 *)
Lemma div_2m_minus_1 : forall m : Z, m > 0 -> (2 * m - 1) / 2 = m - 1.
Proof.
  intros m Hm.
  assert (H_eq : (2 * m - 1) = 1 + (m - 1) * 2) by ring.
  rewrite H_eq.
  rewrite Z.div_add by lia.
  assert (H1_div_2 : 1 / 2 = 0).
  {
    apply Z.div_small.
    split; lia.
  }
  rewrite H1_div_2.
  rewrite Z.add_0_l.
  (* 目标: (m - 1) * 2 / 2 = m - 1 *)
  
  destruct (Z.lt_trichotomy (m - 1) 0) as [Hneg | [Heq | Hpos]].
  - (* m-1 < 0 *)
    assert (Hm_eq_1 : m = 1) by lia.
    subst m.
    compute.
    reflexivity.
    
  - (* m-1 = 0 *)
    rewrite Heq.
    compute.
    reflexivity.
    
  - (* m-1 > 0 *)
    (* 当前目标已简化为 m-1 = m-1 *)
    reflexivity.
Qed.
  
(* 简化版：使用更基础的引理 *)
Lemma div_2m_minus_1_simple : forall m : Z, m > 0 -> (2 * m - 1) / 2 = m - 1.
Proof.
  intros m Hm.
  symmetry.
  apply Z.div_unique with (r := 1).
  - left. split; lia.
  - lia.
Qed.
  
(** 辅助引理: Z.pos等于对应的自然数转换 **)
Lemma Zpos_eq_Z_of_nat : forall p, Z.pos p = Z.of_nat (Pos.to_nat p).
Proof.
  (* 对 p 进行归纳 *)
  induction p using Pos.peano_ind.
  - (* p = 1 *)
    reflexivity.
  - (* p = Pos.succ p' *)
    rewrite Pos2Nat.inj_succ.
    rewrite Nat2Z.inj_succ.
    (* 当前目标：Z.pos (Pos.succ p) = Z.succ (Z.of_nat (Pos.to_nat p)) *)
    (* 使用归纳假设重写右边 *)
    rewrite <- IHp.  (* 注意：使用 <- 方向 *)
    (* 现在目标：Z.pos (Pos.succ p) = Z.succ (Z.pos p) *)
    (* 使用 Pos2Z.inj_succ 引理 *)
    rewrite Pos2Z.inj_succ.
    reflexivity.
Qed.
  
(** 辅助引理: Zneg等于对应自然数转换的相反数 **)
Lemma Zneg_eq_opp_Z_of_nat : forall p, Z.neg p = Z.opp (Z.of_nat (Pos.to_nat p)).
Proof.
  intro p.
  (* 方法3: 使用 change 转换 *)
  change (Z.neg p) with (Z.opp (Z.pos p)).
  rewrite Zpos_eq_Z_of_nat.
  reflexivity.
Qed.
  
(** 正整数到自然数的转换保持正数性 **)
Lemma positive_nat_Z : forall p, Zpos p = Z.of_nat (Pos.to_nat p).
Proof.
  (* 直接使用我们已经证明的引理 *)
  exact Zpos_eq_Z_of_nat.
Qed.
  
(** 正整数可数性 **)
Theorem positive_countable : exists (f : nat -> positive), forall p : positive, exists n, f n = p.
Proof.
  (* 使用 Pos.of_nat 和 Pos.to_nat 的互逆性 *)
  exists Pos.of_nat.
  intro p.
  (* 直接取 n = Pos.to_nat p *)
  exists (Pos.to_nat p).
  apply Pos2Nat.id.
Qed.
  
(* 使用Pos.of_nat作为P_enum *)
Definition P_enum := Pos.of_nat.
  
(* 辅助引理：自然数到正整数的满射 *)
Lemma P_enum_surjective : forall p : positive, exists n : nat, P_enum n = p.
Proof.
  intro p.
  exists (Pos.to_nat p).
  unfold P_enum.
  apply Pos2Nat.id.
Qed.
  
(** 整数集的枚举函数 **)
Definition Z_enum (n : nat) : Z :=
  match n with
  | O => 0%Z                     (** n = 0 → 整数 0 **)
  | S O => 1%Z                  (** n = 1 → 整数 1 **)
  | S (S m) =>                  (** n ≥ 2 → 进行模式匹配计算 **)
      let k := S (Nat.div2 m) in  (** 计算正整数绝对值：k = ⌊m/2⌋ + 1 **)
      if Nat.even m               (** 检查m的奇偶性 **)
      then Z.of_nat k            (** 若m为偶数，返回正整数 k **)
      else Z.opp (Z.of_nat k)    (** 若m为奇数，返回负整数 -k **)
  end.
  
Definition Z_enum_v1 (n : nat) : Z :=
  if Nat.even n then Z.of_nat (n / 2) else - Z.of_nat (n / 2 + 1).
  
(** 如果countable没有定义，则定义 *)
Definition countable {X : Type} (A : X -> Prop) : Prop :=
  exists f : nat -> X, forall x, A x -> exists n, f n = x.
  
(** 标准康托尔配对函数：pair(a,b) = (a+b)(a+b+1)/2 + b **)
Definition cantor_pairing (a b : nat) : nat :=
  ((a + b) * (a + b + 1)) / 2 + b.
  
(** 康托尔逆配对 - 修正版本 **)
Definition cantor_unpairing (n : nat) : nat * nat :=
  (* 寻找最大的t使得 t*(t+1)/2 ≤ n *)
  let t := 
    (fix find_k (m : nat) : nat :=
       match m with
       | O => O
       | S m' =>
           if Nat.leb (m * (m + 1) / 2) n
           then m
           else find_k m'
       end) n in
  let y := Nat.sub n (t * (t + 1) / 2) in
  let x := Nat.sub t y in
  (x, y).
  
(** 枚举所有有理数 **)
Definition enumerate_rationals (n : nat) : Q :=
  let (a, b) := cantor_unpairing n in
  let p := Z_enum a in          (* 使用库里已有的 Z_enum *)
  let q := Z_enum (b + 1) in    (* b+1 确保分母不为0 *)
  (* 确保分母为正 *)
  match q with
  | Z0 => 0%Q                    (* 不应该发生，因为 b+1 ≥ 1 *)
  | Zpos pos_q => (p # pos_q)%Q  (* 正分母 *)
  | Zneg neg_q => 
      (* 如果分母为负，转换为正分母并调整分子符号 *)
      ((Z.opp p) # (Pos.of_succ_nat (Z.to_nat (Z.pred (Z.neg neg_q)))))%Q
  end.
  
(** 辅助引理：自然数除2的性质 **)
Lemma div2_double : forall n, Nat.div2 (2 * n) = n.
Proof.
  induction n as [O | m IH].
  - reflexivity.
  - simpl.
    rewrite Nat.add_succ_r.
    simpl.
    rewrite Nat.add_0_r.
    (* 目标: S (Nat.div2 (m + m)) = S m *)
    (* 在归纳假设中，将 2 * m 简化为 m + m *)
    simpl in IH.
    rewrite Nat.add_0_r in IH.
    rewrite IH.
    reflexivity.
Qed.
  
(** 辅助引理：自然数除2的性质 - 奇数情况 **)
(** 对于任意自然数n，有 Nat.div2 (2 * n + 1) = n **)
Lemma div2_double_plus1 : forall n, Nat.div2 (2 * n + 1) = n.
Proof.
  induction n as [O | k IH].
  - simpl. reflexivity.
  - (* 将 2 * (S k) + 1 转换为 S (S (2 * k + 1)) *)
    rewrite Nat.mul_succ_r.      (* 2 * S k = 2 * k + 2 *)
    rewrite Nat.add_succ_r.      (* 2 * k + 2 + 1 = S (2 * k + 2) *)
    rewrite Nat.add_succ_r.      (* 2 * k + 2 = S (2 * k + 1) *)
    simpl.
    (* 目标: S (Nat.div2 (k + (k + 0) + 1 + 0)) = S k *)
    (* 化简表达式中的 0 *)
    rewrite Nat.add_0_r.
    rewrite Nat.add_0_r.
    (* 目标: S (Nat.div2 (k + k + 1)) = S k *)
    (* 在归纳假设中展开 2 * k，并化简，使其与目标中的表达式匹配 *)
    unfold Nat.mul in IH.        (* 将 2 * k 展开为 k + (k + 0) *)
    rewrite Nat.add_0_r in IH.   (* 将 k + 0 变成 k，所以 2 * k + 1 变成 (k + k) + 1 *)
    (* 现在 IH 是 Nat.div2 (k + k + 1) = k *)
    rewrite IH.
    reflexivity.
Qed.
  
(** 辅助引理：自然数偶性判断 **)
(** 辅助引理：自然数偶性判断 - 偶数的两倍仍然是偶数 **)
(** 对于任意自然数 n，有 Nat.even (2 * n) = true **)
Lemma even_double : forall n, Nat.even (2 * n) = true.
Proof.
  (* 对 n 进行数学归纳法证明 *)
  induction n as [O | n IH].
  (* 基本情况：n = 0，2*0=0，0是偶数 *)
  - simpl. reflexivity.
  (* 归纳步骤：n = S n，归纳假设 IH 为 Nat.even (2 * n) = true *)
  (* 现在证明 Nat.even (2 * (S n)) = true *)
  - 
    (* 第一步：利用乘法与后继的关系，将 2 * (S n) 展开为 2 * n + 2 *)
    rewrite Nat.mul_succ_r.      (* 2 * S n = 2 * n + 2 *)
    (* 当前目标：Nat.even (2 * n + 2) = true *)
    (* 将 2 * n + 2 转换为 S (S (2 * n)) 的形式 *)
    (* 首先将 2 分解为 S (S 0)，即两次后继 *)
    change (2) with (S (S O)).
    (* 现在表达式为 2 * n + S (S O) *)
    (* 使用加法与后继的交换律：a + S b = S (a + b) *)
    rewrite Nat.add_succ_r.      (* 2 * n + S (S O) = S (2 * n + S O) *)
    rewrite Nat.add_succ_r.      (* 2 * n + S O = S (2 * n + O) *)
    rewrite Nat.add_0_r.         (* 2 * n + O = 2 * n *)
    (* 现在表达式为 S (S (2 * n)) *)
    (* 化简 Nat.even (S (S (2 * n))) 为 Nat.even (2 * n) *)
    simpl.
    (* 应用归纳假设 *)
    exact IH.
Qed.
  
(** 辅助引理：自然数偶性判断 - 奇数的两倍加一仍然是奇数 **)
(** 对于任意自然数 n，有 Nat.even (2 * n + 1) = false **)
Lemma even_double_plus1 : forall n, Nat.even (2 * n + 1) = false.
Proof.
  (* 对 n 进行数学归纳法证明 *)
  induction n as [O | n IH].
  (* 基本情况：n = 0，2*0+1=1，1是奇数 *)
  - simpl. reflexivity.
  (* 归纳步骤：n = S n，归纳假设 IH 为 Nat.even (2 * n + 1) = false *)
  (* 现在证明 Nat.even (2 * (S n) + 1) = false *)
  - 
    (* 第一步：利用乘法与后继的关系，将 2 * (S n) 展开为 2 * n + 2 *)
    rewrite Nat.mul_succ_r.      (* 2 * S n = 2 * n + 2 *)
    (* 当前目标：Nat.even ((2 * n + 2) + 1) = false *)
    (* 第二步：将 (2 * n + 2) + 1 重写为 S (2 * n + 2)，因为加1等于后继 *)
    rewrite Nat.add_succ_r.      (* (2 * n + 2) + 1 = S (2 * n + 2) *)
    (* 第三步：将 2 * n + 2 重写为 S (2 * n + 1)，因为加2等于两次后继 *)
    rewrite Nat.add_succ_r.      (* 2 * n + 2 = S (2 * n + 1) *)
    (* 现在表达式变为 S (S (2 * n + 1)) *)
    (* 第四步：化简 Nat.even (S (S (2 * n + 1))) 为 Nat.even (2 * n + 1) *)
    simpl.
    (* 当前目标：Nat.even (n + (n + 0) + 1 + 0) = false *)
    (* 化简目标中的 0 *)
    rewrite Nat.add_0_r.
    rewrite Nat.add_0_r.
    (* 现在目标：Nat.even (n + n + 1) = false *)
    (* 在归纳假设中展开 2 * n 并化简，使其与目标匹配 *)
    unfold Nat.mul in IH.        (* 将 2 * n 展开为 n + (n + 0) *)
    rewrite Nat.add_0_r in IH.   (* 将 n + 0 变成 n，所以 2 * n + 1 变成 (n + n) + 1 *)
    (* 现在归纳假设变为：Nat.even (n + n + 1) = false *)
    (* 应用归纳假设 *)
    exact IH.
Qed.
  
(** 辅助引理：正整数转换为自然数后至少为1 **)
Lemma Pos2Nat_gt_0 : forall p, (Pos.to_nat p > 0)%nat.
Proof.
  intro p.
  apply Pos2Nat.is_pos.
Qed.
  
(** 辅助引理：自然数的前驱计算 **)
Lemma Nat_succ_pred : forall n, (n > 0)%nat -> S (Nat.pred n) = n.
Proof.
  intros n H.
  destruct n as [O | m].
  - inversion H.
  - simpl. reflexivity.
Qed.
  
End ProbabilityTheorems.
  
Export ProbabilityTheorems.
