(**********************************************************************)
(*  This is part of AST_AC, it is distributed under the terms of the  *)
(*          GNU Lesser General Public License version 3               *)
(*             (see file LICENSE for more details)                    *)
(*                                                                    *)
(*                     Copyright 2023-2026                            *)
(*    Dakai Guo, Si Chen, Guowei Dou, Shukun Leng and Wensheng Yu     *)
(**********************************************************************)

(** mk_structure *)

(* Pre_Logic *)

Notation "∀ x .. y , P" := (forall x, .. (forall y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' ∀ x .. y ']' , P") : type_scope.

Notation "∃ x .. y , P" := (exists x, .. (exists y, P) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' ∃ x .. y ']' , P") : type_scope.

Notation "'λ' x .. y , t" := (fun x => .. (fun y => t) ..)
  (at level 200, x binder, y binder, right associativity,
  format "'[ ' 'λ' x .. y ']' , t").

Axiom classic : ∀ P, P \/ ~P.

Proposition peirce : ∀ P, (~P -> P) -> P.
Proof.
  intros; destruct (classic P); auto.
Qed.

Proposition NNPP : ∀ P, ~~P <-> P.
Proof.
  split; intros; destruct (classic P); tauto.
Qed.

Proposition notandor : ∀ P Q,
  (~(P /\ Q) <-> (~P) \/ (~Q)) /\ (~(P \/ Q) <-> (~P) /\ (~Q)).
Proof.
  intros; destruct (classic P); tauto.
Qed.

Proposition inp : ∀ {P Q: Prop}, (P -> Q) -> (~Q) -> (~P).
Proof.
  intros; intro; auto.
Qed.

(* Structure *)

Class mk_structure := {
  Class : Type;
  In : Class -> Class -> Prop;
  Classifier : (Class -> Prop) -> Class
  }.

Parameter MKS: mk_structure.

Notation "x ∈ y" := (@ In MKS x y) (at level 70).

Notation "\{ P \}" := (@ Classifier MKS P) (at level 0).

(* Definitions *)

Definition Ensemble x := ∃ y, x ∈ y.

Global Hint Unfold Ensemble : core.

(* 并 x∪y = {z:z∈x或者z∈y} *)
Definition Union x y := \{ λ z, z ∈ x \/ z ∈ y \}.

Notation "x ∪ y" := (Union x y) (at level 65, right associativity).

(* 定义3  交 x∩y = {z:z∈x同时z∈y} *)
Definition Intersection x y := \{ λ z, z ∈ x /\ z ∈ y \}.

Notation "x ∩ y" := (Intersection x y) (at level 60, right associativity).

(* 定义9  x∉y当且仅当x∈y不真 *)
Definition NotIn x y := ~ (x ∈ y).

Notation "x ∉ y" := (NotIn x y) (at level 10).

(* 定义10  ¬x={y：y∉x} *)
Definition Complement x := \{λ y, y ∉ x \}.

Notation "¬ x" := (Complement x) (at level 5, right associativity).

(* 定义13  x~y=x∩(¬ y) *)
Definition Setminus x y := x ∩ (¬ y).

Notation "x ~ y" := (Setminus x y) (at level 50, left associativity).

(* 定义85  x≠y 当且仅当 x=y 不真 *)
Notation "x ≠ y" := (~ (x = y)) (at level 70).

(* 定义15  Φ={x:x≠x} *)
Definition Φ := \{λ x, x ≠ x \}.

(* 定义18  全域 μ={x:x=x} *)
Definition μ := \{ λ x, x = x \}.

(* 定义22  ∩x={z:对于每个y，如果y∈x，则z∈y} *) 
Definition Element_I x := \{ λ z, ∀ y, y ∈ x -> z ∈ y \}.

Notation "∩ x" := (Element_I x) (at level 66).

(* 定义23  ∪x={z:对于某个y，z∈y同时y∈x} *)
Definition Element_U x := \{ λ z, ∃ y, z ∈ y /\ y ∈ x \}.

Notation "∪ x" := (Element_U x) (at level 66).

(* 定义25  x⊂y 当且仅当对于每个z，如果z∈x，则z∈y *)
Definition Included x y := ∀ z, z ∈ x -> z ∈ y.

Notation "x ⊂ y" := (Included x y) (at level 70).

(* 定义36  pow(x)={y:y⊂x} *)
Definition PowerClass x := \{ λ y, y ⊂ x \}.

Notation "pow( x )" := (PowerClass x)
  (at level 0, right associativity).

(* 定义40  [x]={z:如果x∈μ，则z=x} *)
Definition Singleton x := \{ λ z, x ∈ μ -> z = x \}.

Notation "[ x ]" := (Singleton x) (at level 0, right associativity).

(* 定义45  [x|y]=[x]∪[y] *)
Definition Unordered x y := [x] ∪ [y].

Notation "[ x | y ]" := (Unordered x y) (at level 0).

(* 定义48  [x,y] = [[x]|[x|y]] *)
Definition Ordered x y := [ [x] | [x|y]].

Notation "[ x , y ]" := (Ordered x y) (at level 0).

(* 定义51  z的1st坐标=∩∩z *)
Definition First z := ∩∩z.

(* 定义52  z的2nd坐标=(∩∪z)∪(∪∪z)~(∪∩z) *)
Definition Second z := (∩∪z)∪(∪∪z) ~ (∪∩z).

(* 定义56  r是一个关系当且仅当对于r的每个元z存在x与y使得z=[x,y]; 一个关系是一个类，它的元为序偶 *)
Definition Relation r := ∀ z, z ∈ r -> ∃ x y, z = [x,y].

(* { (x,y) : ... } *)
Notation "\{\ P \}\" :=
  (\{ λ z, ∃ x y, z = [x,y] /\ P x y \}) (at level 0).

(* 定义57 r∘s={u:对于某个x，某个y及某个z,u=[x,z],[x,y]∈s同时[y,z]∈r},类r∘s是r与s的合成 *)
Definition Composition r s :=
  \{\ λ x z, ∃ y, [x,y] ∈ s /\ [y,z] ∈ r \}\.

Notation "r ∘ s" := (Composition r s) (at level 50).

(* 定义60  r ⁻¹={[x,y]:[y,x]∈r} *)
Definition Inverse r := \{\ λ x y, [y,x] ∈ r \}\.

Notation "r ⁻¹" := (Inverse r) (at level 5).

(* 定义63 f是一个函数当且仅当f是一个关系同时对每个x，每个y，每个z，如果 [x,y]∈f 且
   [x，z]∈f，则 y=z。*)
Definition Function f  :=
  Relation f /\ (∀ x y z, [x,y] ∈ f -> [x,z] ∈ f -> y = z).

(* 定义65 f的定义域={x：对于某个y，[x，y]∈f} *)
Definition Domain f := \{ λ x, ∃ y, [x,y] ∈ f \}.

Notation "dom( f )" := (Domain f)(at level 5).

(* 定义66 f的值域={y：对于某个x，[x，y]∈f} *)
Definition Range f := \{ λ y, ∃ x, [x,y] ∈ f \}.

Notation "ran( f )" := (Range f)(at level 5).

(* 定义68 f(x)=∩{y:[x,y]∈f} *)
Definition Value f x := ∩(\{ λ y, [x,y] ∈ f \}).

Notation "f [ x ]" := (Value f x)(at level 5).

(* 定义72 x × y={[u,v]:u∈x/\v∈y} *)
Definition Cartesian x y := \{\ λ u v, u ∈ x /\ v ∈ y \}\.

Notation "x × y" := (Cartesian x y) (at level 2, right associativity).

(* 定义76 Exponent y x = {f:f是一个函数，f的定义域=x同时f的值域⊂ y} *)
Definition Exponent y x :=
  \{ λ f, Function f /\ dom( f ) = x /\ ran( f ) ⊂ y \}.

(* 定义78 f在x上，当且仅当f为一函数同时x=f的定义域 *)
Definition On f x := Function f /\ dom(f) = x.

(* 定义79 f到y，当且仅当f是一个函数同时f的值域⊂y *)
Definition To f y := Function f /\ ran(f) ⊂ y.

(* 定义80 f到y上，当且仅当f是一个函数同时f的值域=y *)
Definition Onto f y := Function f /\ ran(f) = y.

(* 定义81 *)
Definition Rrelation x r y := [x,y] ∈ r.

(* 定义82 *)
Definition Connect r x := ∀ u v, u ∈ x -> v ∈ x
  -> (Rrelation u r v) \/ (Rrelation v r u) \/ (u = v).

(* 定义83 *)
Definition Transitive r x := ∀ u v w, u ∈ x -> v ∈ x -> w ∈ x
  -> Rrelation u r v -> Rrelation v r w -> Rrelation u r w.

(* 定义84 *)
Definition Asymmetric r x := ∀ u v, u ∈ x -> v ∈ x
  -> Rrelation u r v -> ~ Rrelation v r u.

(* 定义86 *)
Definition FirstMember z r x :=
  z ∈ x /\ (∀ y, y ∈ x -> ~ Rrelation y r z).

(* 定义87 *)
Definition WellOrdered r x :=
  Connect r x /\ (∀ y, y ⊂ x -> y ≠ Φ -> ∃ z, FirstMember z r y).

(* 定义89 *)
Definition rSection y r x := y ⊂ x /\ WellOrdered r x
  /\ (∀ u v, u ∈ x -> v ∈ y -> Rrelation u r v -> u ∈ y).

(* 定义93 *)
Definition Order_Pr f r s := Function f
  /\ WellOrdered r dom(f) /\ WellOrdered s ran(f)
  /\ (∀ u v, u ∈ dom(f) -> v ∈ dom(f) -> Rrelation u r v
    -> Rrelation f[u] s f[v]).

(* 定义95 *)
Definition Function1_1 f := Function f /\ Function (f⁻¹).

(* 定义98 *)
Definition Order_PXY f x y r s := WellOrdered r x /\ WellOrdered s y
  /\ Order_Pr f r s /\ rSection dom(f) r x /\ rSection ran(f) s y.

(* 定义103 *)
Definition E := \{\ λ x y, x ∈ y \}\.

(* 定义105 *)
Definition Full x := ∀ m, m ∈ x -> m ⊂ x.

(* 定义106 *)
Definition Ordinal x := Connect E x /\ Full x.

(* 定义112 *)
Definition R := \{ λ x, Ordinal x \}.

(* 定义115 *)
Definition Ordinal_Number x := x ∈ R.

(* 定义116 *)
Definition Less x y := x ∈ y.

Notation "x ≺ y" := (Less x y) (at level 67, left associativity).

(* 定义117 *)
Definition LessEqual (x y: Class) := x ∈ y \/ x = y.

Notation "x ≼ y" := (LessEqual x y) (at level 67, left associativity).

(* 定义122 *)
Definition PlusOne x := x ∪ [x].

(* 定义125 *)
Definition Restriction f x := f ∩ (x × μ).

Notation "f | ( x )" := (Restriction f x) (at level 30).

(* 定义129 *)
Definition Integer x := Ordinal x /\ WellOrdered (E⁻¹) x.

(* 定义130 *)
Definition LastMember x E y := FirstMember x (E⁻¹) y.

(* 定义131 *)
Definition ω := \{ λ x, Integer x \}.

(* 选择函数 *)
Definition ChoiceFunction c :=
  Function c /\ (∀ x, x ∈ dom(c) -> c[x] ∈ x).

(* 定义141 *)
Definition Nest n := ∀ x y, x ∈ n -> y ∈ n -> x ⊂ y \/ y ⊂ x.

(* 定义144 x≈y当且仅当存在一个1-1函数f，f的定义域=x而f的值域=y *)
Definition Equivalent x y :=
  ∃ f, Function1_1 f /\ dom(f) = x /\ ran(f) = y.

Notation "x ≈ y" := (Equivalent x y) (at level 70).

(* 定义148 x是一个基数就是说x是一个序数，并且如果y∈R和y≺x，则x≈y不真 *)
Definition Cardinal_Number x  :=
  Ordinal_Number x /\ (∀ y, y ∈ R -> y ≺ x -> ~ (x ≈ y)).

(* 定义149 C = { x : x 是基数 } *)
Definition C := \{ λ x, Cardinal_Number x \}.

(* 定义151 P = { (x,y) : x ≈ y 且 y ∈ C } *)
Definition P := \{\ λ x y, x ≈ y /\ y ∈ C \}\.

(* 定义166 x是有限的当且仅当P[x]∈w *)
Definition Finite x := P[x] ∈ ω.

Definition Max x y := x ∪ y.

Definition LessLess := \{\ λ a b, ∃ u v x y, a = [u,v]
  /\ b = [x,y] /\ [u,v] ∈ (R × R) /\ [x,y] ∈ (R × R)
  /\ ((Max u v ≺ Max x y) \/ (Max u v = Max x y /\ u ≺ x)
    \/ (Max u v = Max x y /\ u = x /\ v ≺ y)) \}\.

Notation "≪" := (LessLess)(at level 0, no associativity).

(* Axioms *)

Class MK_Axioms := {
  AI : ∀ x y, x = y <-> (∀ z, z ∈ x <-> z ∈ y);
  AII : ∀ b P, b ∈ \{ P \} <-> Ensemble b /\ (P b);
  AIII : ∀ {x}, Ensemble x
    -> ∃ y, Ensemble y /\ (∀ z, z ⊂ x -> z ∈ y);
  AIV : ∀ {x y}, Ensemble x -> Ensemble y -> Ensemble (x ∪ y);
  AV : ∀ {f}, Function f -> Ensemble dom(f) -> Ensemble ran(f);
  AVI : ∀ x, Ensemble x -> Ensemble (∪x);
  AVII : ∀ x, x ≠ Φ -> ∃ y, y ∈ x /\ x ∩ y = Φ;
  AVIII : ∃ y, Ensemble y /\ Φ ∈ y
    /\ (∀ x, x ∈ y -> (x ∪ [x]) ∈ y);
  AIX : exists c, ChoiceFunction c /\ dom(c) = μ ~ [Φ]
  }.

Parameter MK_Axiom : MK_Axioms.

Notation AxiomI := (@ AI MK_Axiom).
Notation AxiomII := (@ AII MK_Axiom).
Notation AxiomIII := (@ AIII MK_Axiom).
Notation AxiomIV := (@ AIV MK_Axiom).
Notation AxiomV := (@ AV MK_Axiom).
Notation AxiomVI := (@ AVI MK_Axiom).
Notation AxiomVII := (@ AVII MK_Axiom).
Notation AxiomVIII := (@ AVIII MK_Axiom).
Notation AxiomIX := (@ AIX MK_Axiom).

Ltac New H := pose proof H.

Ltac TF P := destruct (classic P).

Ltac Absurd := apply peirce; intros.

(* 批处理条件或目标中"与"和"或"策略 *)

Ltac deand :=
  match goal with
   | H: ?a /\ ?b |- _ => destruct H; deand
   | _ => idtac
  end.

Ltac deor :=
  match goal with
   | H: ?a \/ ?b |- _ => destruct H; deor
   | _ => idtac 
  end.

Ltac deandG :=
  match goal with
    |- ?a /\ ?b => split; deandG
    | _ => idtac
  end.

Ltac eqext := apply AxiomI; split; intros.

Ltac appA2G := apply AxiomII; split; eauto.

Ltac appA2H H := apply AxiomII in H as [].


(* ================================================================ *)
(* 核心引理：如果 z ∈ x，则 Ensemble z                                  *)
(* ================================================================ *)

Lemma in_ensemble : ∀ z x, z ∈ x -> Ensemble z.
Proof.
  intros. unfold Ensemble. exists x. assumption.
Qed.

(* ================================================================ *)
(* MKT4: z ∈ x ∨ z ∈ y ↔ z ∈ (x ∪ y)                                 *)
(* ================================================================ *)

Theorem MKT4 : ∀ x y z, z ∈ x \/ z ∈ y <-> z ∈ (x ∪ y).
Proof.
  intros x y z. unfold Union. split.
  - intros [H|H].
    + apply AxiomII. split.
      * apply in_ensemble with x. assumption.
      * left. assumption.
    + apply AxiomII. split.
      * apply in_ensemble with y. assumption.
      * right. assumption.
  - intros H. apply AxiomII in H as [_ H]. assumption.
Qed.

(* ================================================================ *)
(* MKT4': z ∈ x ∧ z ∈ y ↔ z ∈ (x ∩ y)                                 *)
(* ================================================================ *)

Theorem MKT4' : ∀ x y z, z ∈ x /\ z ∈ y <-> z ∈ (x ∩ y).
Proof.
  intros x y z. unfold Intersection. split.
  - intros [H1 H2]. apply AxiomII. split.
    + apply in_ensemble with x. assumption.
    + split; assumption.
  - intros H. apply AxiomII in H as [_ [H1 H2]]. split; assumption.
Qed.

(* ================================================================ *)
(* MKT5: x ∪ x = x                                                   *)
(* ================================================================ *)

Theorem MKT5 : ∀ x, x ∪ x = x.
Proof.
  intros x. apply AxiomI; intro z; split; intro H.
  - apply MKT4 in H. destruct H; assumption.
  - apply MKT4. left. assumption.
Qed.

(* ================================================================ *)
(* MKT5': x ∩ x = x                                                   *)
(* ================================================================ *)

Theorem MKT5' : ∀ x, x ∩ x = x.
Proof.
  intros x. apply AxiomI; intro z; split; intro H.
  - apply MKT4' in H. destruct H. assumption.
  - apply MKT4'. split; assumption.
Qed.

(* ================================================================ *)
(* MKT6: x ∪ y = y ∪ x                                                *)
(* ================================================================ *)

Theorem MKT6 : ∀ x y, x ∪ y = y ∪ x.
Proof.
  intros x y. apply AxiomI; intro z; split; intro H.
  - apply MKT4 in H. apply MKT4. destruct H; [right|left]; assumption.
  - apply MKT4 in H. apply MKT4. destruct H; [right|left]; assumption.
Qed.

(* ================================================================ *)
(* MKT6': x ∩ y = y ∩ x                                                *)
(* ================================================================ *)

Theorem MKT6' : ∀ x y, x ∩ y = y ∩ x.
Proof.
  intros x y. apply AxiomI; intro z; split; intro H.
  - apply MKT4' in H. destruct H as [H1 H2]. apply MKT4'. split; assumption.
  - apply MKT4' in H. destruct H as [H1 H2]. apply MKT4'. split; assumption.
Qed.

(* ================================================================ *)
(* MKT7: (x ∪ y) ∪ z = x ∪ (y ∪ z)                                   *)
(* ================================================================ *)

Theorem MKT7 : ∀ x y z, (x ∪ y) ∪ z = x ∪ (y ∪ z).
Proof.
  intros x y z. apply AxiomI; intro u; split; intro H.
  - apply MKT4 in H. destruct H.
    + apply MKT4 in H. destruct H.
      * apply MKT4. left. assumption.
      * apply MKT4. right. apply MKT4. left. assumption.
    + apply MKT4. right. apply MKT4. right. assumption.
  - apply MKT4 in H. destruct H.
    + apply MKT4. left. apply MKT4. left. assumption.
    + apply MKT4 in H. destruct H.
      * apply MKT4. left. apply MKT4. right. assumption.
      * apply MKT4. right. assumption.
Qed.

(* ================================================================ *)
(* MKT7': (x ∩ y) ∩ z = x ∩ (y ∩ z)                                   *)
(* ================================================================ *)

Theorem MKT7' : ∀ x y z, (x ∩ y) ∩ z = x ∩ (y ∩ z).
Proof.
  intros x y z. apply AxiomI; intro u; split; intro H.
  - apply MKT4' in H. destruct H as [Hxy Hz].
    apply MKT4' in Hxy. destruct Hxy as [Hx Hy].
    apply MKT4'. split. assumption.
    apply MKT4'. split; assumption.
  - apply MKT4' in H. destruct H as [Hx Hyz].
    apply MKT4' in Hyz. destruct Hyz as [Hy Hz].
    apply MKT4'. split.
    apply MKT4'. split; assumption.
    assumption.
Qed.

(* ================================================================ *)
(* MKT8: x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z)                             *)
(* ================================================================ *)

Theorem MKT8 : ∀ x y z, x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z).
Proof.
  intros x y z. apply AxiomI; intro u; split; intro H.
  - apply MKT4' in H. destruct H as [Hx Hyz].
    apply MKT4 in Hyz. destruct Hyz as [Hy|Hz].
    + apply MKT4. left. apply MKT4'. split; assumption.
    + apply MKT4. right. apply MKT4'. split; assumption.
  - apply MKT4 in H. destruct H as [Hxy|Hxz].
    + apply MKT4' in Hxy. destruct Hxy as [Hx Hy].
      apply MKT4'. split. assumption.
      apply MKT4. left. assumption.
    + apply MKT4' in Hxz. destruct Hxz as [Hx Hz].
      apply MKT4'. split. assumption.
      apply MKT4. right. assumption.
Qed.

(* ================================================================ *)
(* MKT8': x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z)                             *)
(* ================================================================ *)

Theorem MKT8' : ∀ x y z, x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z).
Proof.
  intros x y z. apply AxiomI; intro u; split; intro H.
  - apply MKT4 in H. destruct H as [Hx|Hyz].
    + apply MKT4'. split; apply MKT4; left; assumption.
    + apply MKT4' in Hyz. destruct Hyz as [Hy Hz].
      apply MKT4'. split; apply MKT4; right; assumption.
  - apply MKT4' in H. destruct H as [Hxy Hxz].
    apply MKT4 in Hxy. apply MKT4 in Hxz.
    destruct Hxy as [Hx|Hy].
    + apply MKT4. left. assumption.
    + destruct Hxz as [Hx'|Hz].
      * apply MKT4. left. assumption.
      * apply MKT4. right. apply MKT4'. split; assumption.
Qed.

(* ================================================================ *)
(* MKT11: ¬ (¬ x) = x                                                  *)
(* ================================================================ *)

Theorem MKT11: ∀ x, ¬ (¬ x) = x.
Proof.
  intros x. apply AxiomI; intro z; split; intro H.
  - unfold Complement in H. apply AxiomII in H as [Hens H].
    unfold NotIn in H.
    apply NNPP. intro Hnot.
    apply H. unfold Complement. apply AxiomII. split.
    + assumption.
    + unfold NotIn. assumption.
  - unfold Complement. apply AxiomII. split.
    + apply in_ensemble with x. assumption.
    + unfold NotIn. intro Hnot.
      unfold Complement in Hnot. apply AxiomII in Hnot as [_ Hnot'].
      unfold NotIn in Hnot'. apply Hnot'. assumption.
Qed.

(* ================================================================ *)
(* MKT12: ¬(x ∪ y) = (¬ x) ∩ (¬ y)                                   *)
(* ================================================================ *)

Theorem MKT12 : ∀ x y, ¬ (x ∪ y) = (¬ x) ∩ (¬ y).
Proof.
  intros x y. apply AxiomI; intro z; split; intro H.
  - unfold Complement in H. apply AxiomII in H as [Hens H].
    apply MKT4'. split.
    + unfold Complement. apply AxiomII. split.
      * assumption.
      * unfold NotIn. intro Hzx. apply H. apply MKT4. left. assumption.
    + unfold Complement. apply AxiomII. split.
      * assumption.
      * unfold NotIn. intro Hzy. apply H. apply MKT4. right. assumption.
  - apply MKT4' in H. destruct H as [Hnx Hny].
    unfold Complement in Hnx. apply AxiomII in Hnx as [Hens Hn1].
    unfold Complement in Hny. apply AxiomII in Hny as [_ Hn2].
    unfold Complement. apply AxiomII. split.
    + assumption.
    + unfold NotIn. intro Hu. apply MKT4 in Hu. destruct Hu.
      * apply Hn1. assumption.
      * apply Hn2. assumption.
Qed.

(* ================================================================ *)
(* MKT12': ¬(x ∩ y) = (¬ x) ∪ (¬ y)                                   *)
(* ================================================================ *)

Theorem MKT12' : ∀ x y, ¬ (x ∩ y) = (¬ x) ∪ (¬ y).
Proof.
  intros x y. apply AxiomI; intro z; split; intro H.
  - unfold Complement in H. apply AxiomII in H as [Hens H].
    destruct (classic (z ∈ x)).
    + destruct (classic (z ∈ y)).
      * exfalso. apply H. apply MKT4'. split; assumption.
      * apply MKT4. right. unfold Complement. apply AxiomII. split.
        -- exact Hens.
        -- unfold NotIn. assumption.
    + apply MKT4. left. unfold Complement. apply AxiomII. split.
      * exact Hens.
      * unfold NotIn. assumption.
  - apply MKT4 in H. destruct H as [Hnx|Hny].
    + unfold Complement in Hnx. apply AxiomII in Hnx as [Hens Hnx].
      unfold NotIn in Hnx.
      unfold Complement. apply AxiomII. split.
      * exact Hens.
      * unfold NotIn. intro Hzy.
        apply MKT4' in Hzy. destruct Hzy as [Hzx _].
        apply Hnx. assumption.
    + unfold Complement in Hny. apply AxiomII in Hny as [Hens Hny].
      unfold NotIn in Hny.
      unfold Complement. apply AxiomII. split.
      * exact Hens.
      * unfold NotIn. intro Hzy.
        apply MKT4' in Hzy. destruct Hzy as [_ Hzy'].
        apply Hny. assumption.
Qed.

(* ================================================================ *)
(* MKT14: x ∩ (y ~ z) = (x ∩ y) ~ z                                   *)
(* ================================================================ *)

Theorem MKT14 : ∀ x y z, x ∩ (y ~ z) = (x ∩ y) ~ z.
Proof.
  intros x y z. unfold Setminus.
  symmetry. apply MKT7'.
Qed.

(* ================================================================ *)
(* MKT16: x ∉ Φ                                                        *)
(* ================================================================ *)

Theorem MKT16 : ∀ {x}, x ∉ Φ.
Proof.
  intros x. unfold NotIn, Φ. intro H.
  apply AxiomII in H as [_ H].
  unfold "≠" in H. apply H. reflexivity.
Qed.

(* ================================================================ *)
(* MKT17: Φ ∪ x = x                                                    *)
(* ================================================================ *)

Theorem MKT17 : ∀ x, Φ ∪ x = x.
Proof.
  intros x. apply AxiomI; intro z; split; intro H.
  - apply MKT4 in H. destruct H.
    + exfalso. apply (MKT16 (x:=z)). assumption.
    + assumption.
  - apply MKT4. right. assumption.
Qed.

(* ================================================================ *)
(* MKT17': Φ ∩ x = Φ                                                   *)
(* ================================================================ *)

Theorem MKT17' : ∀ x, Φ ∩ x = Φ.
Proof.
  intros x. apply AxiomI; intro z; split; intro H.
  - apply MKT4' in H. destruct H. exfalso. apply (MKT16 (x:=z)). assumption.
  - exfalso. apply (MKT16 (x:=z)). assumption.
Qed.

(* ================================================================ *)
(* MKT19: x ∈ μ ↔ Ensemble x                                          *)
(* ================================================================ *)

Theorem MKT19 : ∀ x, x ∈ μ <-> Ensemble x.
Proof.
  intros x. unfold μ. split.
  - intro H. apply AxiomII in H as [Hens _]. assumption.
  - intro H. apply AxiomII. split. assumption. reflexivity.
Qed.

(* ================================================================ *)
(* MKT19a: x ∈ μ -> Ensemble x                                        *)
(* ================================================================ *)

Theorem MKT19a : ∀ x, x ∈ μ -> Ensemble x.
Proof.
  intros x H. apply MKT19. assumption.
Qed.

(* ================================================================ *)
(* MKT19b: Ensemble x -> x ∈ μ                                        *)
(* ================================================================ *)

Theorem MKT19b : ∀ x, Ensemble x -> x ∈ μ.
Proof.
  intros x H. apply MKT19. assumption.
Qed.

(* ================================================================ *)
(* MKT20: x ∪ μ = μ                                                    *)
(* ================================================================ *)

Theorem MKT20 : ∀ x, x ∪ μ = μ.
Proof.
  intros x. apply AxiomI; intro z; split; intro H.
  - apply MKT4 in H. destruct H.
    + apply MKT19. apply in_ensemble with x. assumption.
    + assumption.
  - apply MKT19 in H as Hens.
    apply MKT4. right. apply MKT19. assumption.
Qed.

(* ================================================================ *)
(* MKT20': x ∩ μ = x                                                   *)
(* ================================================================ *)

Theorem MKT20' : ∀ x, x ∩ μ = x.
Proof.
  intros x. apply AxiomI; intro z; split; intro H.
  - apply MKT4' in H. destruct H. assumption.
  - apply MKT4'. split. assumption.
    apply MKT19. apply in_ensemble with x. assumption.
Qed.

(* ================================================================ *)
(* MKT21: ¬Φ = μ  （空集的补集是全集）                                  *)
(* ================================================================ *)

Theorem MKT21 : ¬ Φ = μ.
Proof.
  apply AxiomI; intro z; split; intro H.
  - unfold Complement in H. apply AxiomII in H as [Hens _].
    apply MKT19b. exact Hens.
  - apply MKT19 in H as Hens.
    unfold Complement. apply AxiomII. split.
    + exact Hens.
    + unfold NotIn. apply MKT16.
Qed.

(* ================================================================ *)
(* MKT21': ¬μ = Φ  （全集的补集是空集）                                 *)
(* ================================================================ *)

Theorem MKT21' : ¬ μ = Φ.
Proof.
  apply AxiomI; intro z; split; intro H.
  - unfold Complement in H. apply AxiomII in H as [Hens Hnot].
    apply MKT19b in Hens.
    exfalso. apply Hnot. exact Hens.
  - exfalso. apply (MKT16 (x:=z)). exact H.
Qed.

(* ================================================================ *)
(* MKT24: ∩Φ = μ                                                      *)
(* ================================================================ *)

Theorem MKT24 : ∩Φ = μ.
Proof.
  apply AxiomI; intro z; split; intro H.
  - apply AxiomII in H as [Hens _].
    apply MKT19b. exact Hens.
  - apply MKT19 in H as Hens.
    apply AxiomII. split.
    + exact Hens.
    + intros y Hy. exfalso. apply (MKT16 (x:=y)). exact Hy.
Qed.

(* ================================================================ *)
(* MKT24': ∪Φ = Φ                                                     *)
(* ================================================================ *)

Theorem MKT24' : ∪Φ = Φ.
Proof.
  apply AxiomI; intro z; split; intro H.
  - apply AxiomII in H as [_ [y [Hzy HyΦ]]].
    exfalso. apply (MKT16 (x:=y)). exact HyΦ.
  - exfalso. apply (MKT16 (x:=z)). exact H.
Qed.

(* ================================================================ *)
(* MKT26: ∀ x, Φ ⊂ x                                                  *)
(* ================================================================ *)

Theorem MKT26 : ∀ x, Φ ⊂ x.
Proof.
  intros x. unfold Included. intros z Hz.
  exfalso. apply (MKT16 (x:=z)). exact Hz.
Qed.

(* ================================================================ *)
(* MKT26': ∀ x, x ⊂ μ                                                 *)
(* ================================================================ *)

Theorem MKT26' : ∀ x, x ⊂ μ.
Proof.
  intros x. unfold Included. intros z Hz.
  apply MKT19b. apply in_ensemble with x. exact Hz.
Qed.

(* ================================================================ *)
(* MKT26a: ∀ x, x ⊂ x                                                 *)
(* ================================================================ *)

Theorem MKT26a : ∀ x, x ⊂ x.
Proof.
  intro x. unfold Included. auto.
Qed.

(* ================================================================ *)
(* MKT27: ∀ x y, (x ⊂ y /\ y ⊂ x) <-> x = y                           *)
(* ================================================================ *)

Theorem MKT27 : ∀ x y, (x ⊂ y /\ y ⊂ x) <-> x = y.
Proof.
  intros x y. split.
  - intros [H1 H2]. apply AxiomI. intro z. split.
    + apply H1.
    + apply H2.
  - intros H. subst. split; apply MKT26a.
Qed.

(* ================================================================ *)
(* MKT28: ∀ {x y z}, x ⊂ y -> y ⊂ z -> x ⊂ z                          *)
(* ================================================================ *)

Theorem MKT28 : ∀ {x y z}, x ⊂ y -> y ⊂ z -> x ⊂ z.
Proof.
  intros x y z H1 H2. unfold Included.
  intros u Hu. apply H2, H1, Hu.
Qed.

(* ================================================================ *)
(* MKT29: ∀ x y, x ∪ y = y <-> x ⊂ y                                  *)
(* ================================================================ *)

Theorem MKT29 : ∀ x y, x ∪ y = y <-> x ⊂ y.
Proof.
  intros x y. split.
  - intros H. unfold Included. intros z Hz.
    assert (Hz_union : z ∈ x ∪ y) by (apply MKT4; left; exact Hz).
    rewrite H in Hz_union. exact Hz_union.
  - intros H. apply AxiomI. intro z. split.
    + intro Hz. apply MKT4 in Hz. destruct Hz.
      * apply H. exact H0.
      * exact H0.
    + intro Hz. apply MKT4. right. exact Hz.
Qed.

(* ================================================================ *)
(* MKT30: ∀ x y, x ∩ y = x <-> x ⊂ y                                  *)
(* ================================================================ *)

Theorem MKT30 : ∀ x y, x ∩ y = x <-> x ⊂ y.
Proof.
  intros x y. split.
  - intros H. unfold Included. intros z Hz.
    rewrite <- H in Hz.
    apply MKT4' in Hz. destruct Hz. exact H1.
  - intros H. apply AxiomI. intro z. split.
    + intro Hz. apply MKT4' in Hz. destruct Hz. exact H0.
    + intro Hz. apply MKT4'. split. exact Hz. apply H. exact Hz.
Qed.

(* ================================================================ *)
(* MKT31: ∀ x y, x ⊂ y -> (∪x ⊂ ∪y) /\ (∩y ⊂ ∩x)                      *)
(* ================================================================ *)

Theorem MKT31 : ∀ x y, x ⊂ y -> (∪x ⊂ ∪y) /\ (∩y ⊂ ∩x).
Proof.
  intros x y H. split.
  - unfold Included. intros z Hz.
    apply AxiomII in Hz as [Hens [w [Hzw Hwx]]].
    apply AxiomII. split.
    + exact Hens.
    + exists w. split. exact Hzw. apply H. exact Hwx.
  - unfold Included. intros z Hz.
    apply AxiomII in Hz as [Hens Hzy].
    apply AxiomII. split.
    + exact Hens.
    + intros w Hwx. apply Hzy. apply H. exact Hwx.
Qed.

(* ================================================================ *)
(* MKT32: ∀ x y, x ∈ y -> (x ⊂ ∪y) /\ (∩y ⊂ x)                        *)
(* ================================================================ *)

Theorem MKT32 : ∀ x y, x ∈ y -> (x ⊂ ∪y) /\ (∩y ⊂ x).
Proof.
  intros x y H. split.
  - unfold Included. intros z Hz.
    apply AxiomII. split.
    + apply in_ensemble with x. exact Hz.
    + exists x. split. exact Hz. exact H.
  - unfold Included. intros z Hz.
    apply AxiomII in Hz as [_ Hzy].
    apply Hzy. exact H.
Qed.

(* ================================================================ *)
(* MKT33: 如果 x 是集合，且 z ⊂ x，则 z 也是集合                       *)
(* ================================================================ *)

Theorem MKT33 : ∀ x z, Ensemble x -> z ⊂ x -> Ensemble z.
Proof.
  intros x z Hx Hsub.
  apply AxiomIII in Hx as [y [Hens_y Hy]].
  unfold Ensemble. exists y. apply Hy. exact Hsub.
Qed.

(* ================================================================ *)
(* MKT34: Φ = ∩μ                                                      *)
(* ================================================================ *)

Theorem MKT34 : Φ = ∩μ.
Proof.
  apply AxiomI; intro z; split; intro Hz.
  - exfalso. apply (MKT16 (x:=z)). exact Hz.
  - apply AxiomII in Hz as [Hens Hforall].
    destruct AxiomVIII as [w [Hens_w [HΦ_w _]]].
    assert (H_ens_Φ : Ensemble Φ) by (apply (in_ensemble Φ w); exact HΦ_w).
    assert (H_Φ_in_μ : Φ ∈ μ) by (apply MKT19b; exact H_ens_Φ).
    apply Hforall in H_Φ_in_μ.
    exfalso. apply (MKT16 (x:=z)). exact H_Φ_in_μ.
Qed.

(* ================================================================ *)
(* MKT34': μ = ∪μ                                                     *)
(* ================================================================ *)

Theorem MKT34' : μ = ∪μ.
Proof.
  apply AxiomI; intro z; split; intro Hz.
  - assert (H_ens_z : Ensemble z) by (apply MKT19a; exact Hz).
    apply AxiomIII in H_ens_z as [p [Hens_p Hp]].
    apply AxiomII. split.
    + apply MKT19a. exact Hz.
    + exists p. split.
      * apply Hp. apply MKT26a.
      * apply MKT19b. exact Hens_p.
  - apply AxiomII in Hz as [Hens [y [Hzy Hyμ]]].
    apply MKT19. exact Hens.
Qed.

(* ================================================================ *)
(* MKT35: 非空类的广义交是集合                                         *)
(* ================================================================ *)

Theorem MKT35 : ∀ x, x ≠ Φ -> Ensemble (∩x).
Proof.
  intros x Hneq.
  assert (H_exists : ∃ y, y ∈ x). {
    destruct (classic (∃ y, y ∈ x)); [assumption|].
    exfalso. apply Hneq. apply AxiomI. intro z. split.
    - intro Hz_in. exfalso. apply H. exists z. exact Hz_in.
    - intro Hz_in. exfalso. apply (MKT16 (x:=z)). exact Hz_in.
  }
  destruct H_exists as [y Hy].
  assert (H_ens_y : Ensemble y) by (apply in_ensemble with x; exact Hy).
  assert (H_sub : ∩x ⊂ y). {
    unfold Included. intros z Hz.
    apply AxiomII in Hz as [_ Hforall].
    apply Hforall. exact Hy.
  }
  apply (MKT33 y (∩x) H_ens_y H_sub).
Qed.

(* ================================================================ *)
(* MKT37: μ = pow(μ)                                                  *)
(* ================================================================ *)

Theorem MKT37 : μ = pow(μ).
Proof.
  apply AxiomI; intro z; split; intro Hz.
  - apply MKT19 in Hz as Hens.
    apply AxiomII. split.
    + exact Hens.
    + apply MKT26'.
  - apply AxiomII in Hz as [Hens Hsub].
    apply MKT19b. exact Hens.
Qed.

(* ================================================================ *)
(* MKT38a: 如果 x 是集合，则 pow(x) 是集合                             *)
(* ================================================================ *)

Theorem MKT38a : ∀ {x}, Ensemble x -> Ensemble pow(x).
Proof.
  intros x Hx.
  apply AxiomIII in Hx as [y [Hens_y Hy]].
  apply AxiomIII in Hens_y as [v [Hens_v Hv]].
  assert (H_pow_sub : pow(x) ⊂ y). {
    unfold Included. intros z Hz.
    apply AxiomII in Hz as [_ Hz_sub].
    apply Hy. exact Hz_sub.
  }
  unfold Ensemble. exists v. apply Hv. exact H_pow_sub.
Qed.

(* ================================================================ *)
(* MKT38b: pow(x) 的成员等价于 x 的子集                               *)
(* ================================================================ *)

Theorem MKT38b : ∀ {x}, Ensemble x -> (∀ y, y ⊂ x <-> y ∈ pow(x)).
Proof.
  intros x Hx y. split.
  - intros Hsub. apply AxiomII. split.
    + apply (MKT33 x y Hx Hsub).
    + exact Hsub.
  - intros Hy. apply AxiomII in Hy as [_ Hsub]. exact Hsub.
Qed.

(* ================================================================ *)
(* MKT39: μ 不是集合（Russell 悖论）                                   *)
(* ================================================================ *)

Theorem MKT39 : ~ Ensemble μ.
Proof.
  intro H.
  pose (Russ := \{ λ x, x ∉ x \}).
  assert (H_Rsub : Russ ⊂ μ). {
    unfold Included. intros z Hz.
    unfold Russ in Hz. apply AxiomII in Hz as [Hens _].
    apply MKT19b. exact Hens.
  }
  assert (H_ens_Russ : Ensemble Russ). {
    apply (MKT33 μ Russ H H_Rsub).
  }
  assert (H_Russell: Russ ∈ Russ <-> ~ (Russ ∈ Russ)). {
    unfold Russ. split.
    - intro HR. apply AxiomII in HR as [_ Hnot]. unfold NotIn in Hnot. exact Hnot.
    - intro Hnot. apply AxiomII. split. exact H_ens_Russ. unfold NotIn. exact Hnot.
  }
  tauto.
Qed.
