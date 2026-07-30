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


Theorem MKT4 : ∀ x y z, z ∈ x \/ z ∈ y <-> z ∈ (x ∪ y).
Proof.
  split; intros; [destruct H; appA2G|appA2H H]; auto.
Qed.

Theorem MKT4' : ∀ x y z, z ∈ x /\ z ∈ y <-> z ∈ (x ∩ y).
Proof.
  split; intros; [destruct H; appA2G|appA2H H]; auto.
Qed.

Ltac deHun :=
  match goal with
   | H:  ?c ∈ ?a∪?b
     |- _ => apply MKT4 in H as [] ; deHun
   | _ => idtac
  end.

Ltac deGun :=
  match goal with
    | |-  ?c ∈ ?a∪?b => apply MKT4 ; deGun
    | _ => idtac
  end.

Ltac deHin :=
  match goal with
   | H:  ?c ∈ ?a∩?b
     |- _ => apply MKT4' in H as []; deHin
   | _ => idtac  
  end.

Ltac deGin :=
  match goal with
    | |- ?c ∈ ?a∩?b => apply MKT4'; split; deGin
    | _ => idtac
  end.

(* 定理5  x∪x=x同时x∩x=x *)
Theorem MKT5 : ∀ x, x ∪ x = x.
Proof.
  intros; eqext; deGun; deHun; auto.
Qed.

Theorem MKT5' : ∀ x, x ∩ x = x.
Proof.
  intros; eqext; deHin; deGin; auto.
Qed.

(* 定理6  x∪y=y∪x同时x∩y=y∩x *)
Theorem MKT6 : ∀ x y, x ∪ y = y ∪ x.
Proof.
  intros; eqext; deHun; deGun; auto.
Qed.

Theorem MKT6' : ∀ x y, x ∩ y = y ∩ x.
Proof.
  intros; eqext; deHin; deGin; auto.
Qed.

(* 定理7  (x∪y)∪z=x∪(y∪z)同时(x∩y)∩z=x∩(y∩z) *)
Theorem MKT7 : ∀ x y z, (x ∪ y) ∪ z = x ∪ (y ∪ z).
Proof.
  intros; eqext; deHun; deGun; auto;
  [right|right|left|left]; deGun; auto.
Qed.

Theorem MKT7' : ∀ x y z, (x ∩ y) ∩ z = x ∩ (y ∩ z).
Proof.
  intros; eqext; deGin; deHin; auto.
Qed.

(* 定理8  x∩(y∪z)=(x∩y)∪(x∩z)同时x∪(y∩z)=(x∪y)∩(x∪z) *)
Theorem MKT8 : ∀ x y z, x ∩ (y ∪ z) = (x ∩ y) ∪ (x ∩ z).
Proof.
  intros; eqext; deHin; deHun; deGun; deGin; [left|right|..];
  deHin; deHun; deGun; deGin; auto.
Qed.

Theorem MKT8' : ∀ x y z, x ∪ (y ∩ z) = (x ∪ y) ∩ (x ∪ z).
Proof.
  intros; eqext; deHin; deHun; deGin; repeat deGun; deHin; auto.
  right; deGin; auto.
Qed.

(* 定理11  ¬ (¬ x) = x *)
Theorem MKT11: ∀ x, ¬ (¬ x) = x.
Proof.
  intros; eqext.
  - appA2H H. Absurd. elim H0. appA2G.
  - appA2G. intro. appA2H H0; auto.
Qed.

(* 定理12  De Morgan   ¬(x∪y)=(¬x)∩(¬y)同时¬(x∩y)=(¬x)∪(¬y) *)
Theorem MKT12 : ∀ x y, ¬ (x ∪ y) = (¬ x) ∩ (¬ y).
Proof.
  intros; eqext.
  - appA2H H; deGin; appA2G; intro; apply H0; deGun; auto.
  - deHin. appA2H H; appA2H H0. appA2G. intro. deHun; auto.
Qed.

Theorem MKT12' : ∀ x y, ¬ (x ∩ y) = (¬ x) ∪ (¬ y).
Proof.
  intros. rewrite <-(MKT11 x),<-(MKT11 y),<-MKT12.
  repeat rewrite MKT11; auto.
Qed.

Fact setminP : ∀ z x y, z ∈ x -> ~ z ∈ y -> z ∈ (x ~ y).
Proof.
  intros. appA2G. split; auto. appA2G.
Qed.

Global Hint Resolve setminP : core.

Fact setminp : ∀ z x y, z ∈ (x ~ y) -> z ∈ x /\ ~ z ∈ y.
Proof.
  intros. appA2H H. destruct H0. appA2H H1; auto.
Qed.

(* 定理14  x∩(y ~ z)=(x∩y) ~ z *)
Theorem MKT14 : ∀ x y z, x ∩ (y ~ z) = (x ∩ y) ~ z.
Proof.
  intros; unfold Setminus; rewrite MKT7'; auto.
Qed.

(* 定理16  x∉Φ *)
Theorem MKT16 : ∀ {x}, x ∉ Φ.
Proof.
  intros; intro. apply AxiomII in H; destruct H; auto.
Qed.

Ltac emf :=
  match goal with
    H:  ?a ∈ Φ
    |- _ => destruct (MKT16 H)
  end.

Ltac eqE := eqext; try emf; auto.

Ltac feine z := destruct (@ MKT16 z).

(* 定理17  Φ∪x=x同时Φ∩x=Φ *)
Theorem MKT17 : ∀ x, Φ ∪ x = x.
Proof.
  intros; eqext; deHun; deGun; auto; emf.
Qed.

Theorem MKT17' : ∀ x, Φ ∩ x = Φ.
Proof.
  intros. eqE. deHin; auto.
Qed.

(* 定理19  x∈μ当且仅当x是一个集  *)
Theorem MKT19 : ∀ x, x ∈ μ <-> Ensemble x.
Proof.
  split; intros; eauto. appA2G.
Qed.

Theorem MKT19a : ∀ x, x ∈ μ -> Ensemble x.
Proof.
  intros. apply MKT19; auto.
Qed.

Theorem MKT19b : ∀ x, Ensemble x -> x ∈ μ.
Proof.
  intros. apply MKT19; auto.
Qed.

Global Hint Resolve MKT19a MKT19b : core.

(* 定理20  x∪μ=μ同时x∩μ=x *)
Theorem MKT20 : ∀ x, x ∪ μ = μ.
Proof.
  intros; eqext; deHun; deGun; eauto.
Qed.

Theorem MKT20' : ∀ x, x ∩ μ = x.
Proof.
  intros; eqext; deHin; deGin; eauto.
Qed.

(* 定理21  ¬Φ=μ同时¬μ=Φ *)
Theorem MKT21 : ¬ Φ = μ.
Proof.
  eqext; appA2G. apply MKT16.
Qed.

Theorem MKT21' : ¬ μ = Φ.
Proof.
  rewrite <-MKT11,MKT21; auto.
Qed.

Ltac deHex1 :=
  match goal with
    H: ∃ x, ?P 
    |- _ => destruct H as []
  end.

Ltac rdeHex := repeat deHex1; deand.

(* 定理24  ∩Φ=μ同时∪Φ=Φ *)
Theorem MKT24 : ∩Φ = μ.
Proof.
  eqext; appA2G; intros; emf.
Qed.

Theorem MKT24' : ∪Φ = Φ.
Proof.
  eqE. appA2H H. rdeHex. emf.
Qed.

(* 定理26  Φ⊂x同时x⊂μ *)
Theorem MKT26 : ∀ x, Φ ⊂ x.
Proof.
  unfold Included; intros; emf.
Qed.

Theorem MKT26' : ∀ x, x ⊂ μ.
Proof.
  unfold Included; intros; eauto.
Qed.

Theorem MKT26a : ∀ x, x ⊂ x.
Proof.
  unfold Included; intros; auto.
Qed.

Global Hint Resolve MKT26 MKT26' MKT26a : core.

Fact ssubs : ∀ {a b z}, z ⊂ (a ~ b) -> z ⊂ a.
Proof.
  unfold Included; intros. apply H in H0. appA2H H0; tauto.
Qed.

Global Hint Immediate ssubs : core.

Fact esube : ∀ {z}, z ⊂ Φ -> z = Φ.
Proof. intros. eqE. Qed.

(* 定理27  x=y当且仅当x⊂y同时y⊂x *)
Theorem MKT27 : ∀ x y, (x ⊂ y /\ y ⊂ x) <-> x = y.
Proof.
  split; intros; subst; [destruct H; eqext|split]; auto.
Qed.

(* 定理28  如果x⊂y且y⊂z，则x⊂z *)
Theorem MKT28 : ∀ {x y z}, x ⊂ y -> y ⊂ z -> x ⊂ z.
Proof.
  unfold Included; intros; auto.
Qed.

(* 定理29  x⊂y当且仅当x∪y=y *)
Theorem MKT29 : ∀ x y, x ∪ y = y <-> x ⊂ y.
Proof.
  split; unfold Included; intros;
  [rewrite <-H; deGun|eqext; deGun; deHun]; auto.
Qed.

(* 定理30  x⊂y当且仅当x∩y=x *)
Theorem MKT30 : ∀ x y, x ∩ y = x <-> x ⊂ y.
Proof.
  split; unfold Included; intros;
  [rewrite <-H in H0; deHin|eqext; deGin; deHin]; auto.
Qed.

(* 定理31  如果x⊂y,则∪x⊂∪y同时∩y⊂∩x *)
Theorem MKT31 : ∀ x y, x ⊂ y -> (∪x ⊂ ∪y) /\ (∩y ⊂ ∩x).
Proof.
  split; red; intros; appA2H H0; rdeHex; appA2G.
Qed.

(* 定理32  如果x∈y,则x⊂∪y同时∩y⊂x *)
Theorem MKT32 : ∀ x y, x ∈ y -> (x ⊂ ∪y) /\ (∩y ⊂ x).
Proof.
  split; red; intros; [appA2G|appA2H H0; auto].
Qed.

(*A.4 集的存在性 *)

(* 定理33  如果x是一个集同时z⊂x，则z是一个集 *)
Theorem MKT33 : ∀ x z, Ensemble x -> z ⊂ x -> Ensemble z.
Proof.
  intros. destruct (AxiomIII H) as [y []]; eauto.
Qed.

(* 定理34  0=∩μ同时∪μ =μ *)
Theorem MKT34 : Φ = ∩μ.
Proof.
  eqE. appA2H H. apply H0. appA2G. eapply MKT33; eauto.
Qed.

Theorem MKT34' : μ = ∪μ.
Proof.
  eqext; eauto. destruct (@ AxiomIII z) as [y []]; eauto. appA2G.
Qed.

(* 定理35  如果x≠0，则∩x是一个集 *)
Lemma NEexE : ∀ x, x ≠ Φ <-> ∃ z, z∈x.
Proof.
  split; intros.
  - Absurd. elim H; eqext; try emf. elim H0; eauto.
  - intro; subst. destruct H. emf.
Qed.

Ltac NEele H := apply NEexE in H as [].

Theorem MKT35 : ∀ x, x ≠ Φ -> Ensemble (∩x).
Proof.
  intros. NEele H. eapply MKT33; eauto. apply MKT32; auto.
Qed.

(* 定理37  u=pow(u) *)
Theorem MKT37 : μ = pow(μ).
Proof.
  eqext; appA2G; eauto.
Qed.

(* 定理38  如果x是一个集,则pow(x)是一个集*)
Theorem MKT38a : ∀ {x}, Ensemble x -> Ensemble pow(x).
Proof.
  intros. New (AxiomIII H). rdeHex. eapply MKT33; eauto.
  red; intros. appA2H H2; auto.
Qed.

Theorem MKT38b : ∀ {x}, Ensemble x -> (∀ y, y ⊂ x <-> y ∈ pow(x)).
Proof.
  split; intros; [appA2G; eapply MKT33; eauto|appA2H H0; auto].
Qed.

(* 定理39  μ不是一个集 *)

(* 一个不是集的类 *)
Lemma Lemma_N : ~ Ensemble \{ λ x, x ∉ x \}.
Proof.
  TF (\{ λ x, x ∉ x \} ∈ \{ λ x, x ∉ x \}).
  - New H. appA2H H; auto.
  - intro. apply H,AxiomII; auto.
Qed.

Theorem MKT39 : ~ Ensemble μ.
Proof.
  intro. apply Lemma_N. eapply MKT33; eauto.
Qed.

Fact singlex : ∀ x, Ensemble x -> x ∈ [x].
Proof.
  intros. appA2G.
Qed.

Global Hint Resolve singlex : core.

(* 定理41  如果x是一个集，则对于每个y，y∈[x]当且仅当y=x *)
Theorem MKT41 : ∀ x, Ensemble x -> (∀ y, y ∈ [x] <-> y = x).
Proof.
  split; intros; [appA2H H0; auto|subst; appA2G].
Qed.

Ltac eins H := apply MKT41 in H; subst; eauto.

(* 定理42  如果x是一个集，则[x]是一个集 *)
Theorem MKT42 : ∀ x, Ensemble x -> Ensemble ([x]).
Proof.
  intros. New (MKT38a H). eapply MKT33; eauto.
  red; intros. eins H1. appA2G.
Qed.

Global Hint Resolve MKT42 : core.

(* 定理43  [x]=μ当且仅当x不是一个集*)
Theorem MKT43 : ∀ x, [x] = μ <-> ~ Ensemble x.
Proof.
  split; intros.
  - intro. apply MKT39. rewrite <-H; auto.
  - eqext; eauto. appA2G; intro; elim H; auto.
Qed.

(* 定理42'  如果[x]是一个集，则x是一个集 *)
Theorem MKT42' : ∀ x, Ensemble ([x]) -> Ensemble x.
Proof.
  intros. Absurd. apply MKT43 in H0.
  elim MKT39. rewrite <-H0; auto.
Qed.

(* 定理44  如果x是一个集，则∩[x]=x同时∪[x]=x；如果x不是一个集，则∩[x]=0同时∪[x]=u *)
Theorem MKT44 : ∀ {x}, Ensemble x -> ∩[x] = x /\ ∪[x] = x.
Proof.
  split; intros; eqext; try appA2G.
  - appA2H H0. apply H1; auto.
  - intros. eins H1.
  - appA2H H0. rdeHex. eins H2; subst; auto.
Qed.

Theorem MKT44' : ∀ x, ~ Ensemble x -> ∩[x] = Φ /\ ∪[x] = μ.
Proof.
  intros. apply MKT43 in H.
  rewrite H; split; symmetry; [apply MKT34|apply MKT34'].
Qed.

Corollary AxiomIV': ∀ x y, Ensemble (x ∪ y)
  -> Ensemble x /\ Ensemble y.
Proof.
  split; intros; eapply MKT33; eauto; red; intros; deGun; auto.
Qed.

(* 定理46  如果x是一个集同时y是一个集，则[x|y]是一个集，同时z∈[x|y] 当且仅当 z=x或者z=y;
          [x|y]=μ 当且仅当 x不是一个集或者y不是一个集 *)
Theorem MKT46a : ∀ {x y}, Ensemble x -> Ensemble y
  -> Ensemble ([x|y]).
Proof.
  intros; apply AxiomIV; apply MKT42; auto.
Qed.

Global Hint Resolve MKT46a : core.

Theorem MKT46b : ∀ {x y}, Ensemble x -> Ensemble y
  -> (∀ z, z ∈ [x|y] <-> (z = x \/ z = y)).
Proof.
  split; unfold Unordered; intros.
  - deHun; eins H1.
  - deGun. destruct H1; subst; auto.
Qed.

Theorem MKT46' : ∀ x y, [x|y] = μ <-> ~ Ensemble x \/ ~ Ensemble y.
Proof.
  split; intros.
  - Absurd. apply notandor in H0 as []. elim MKT39.
    rewrite <-H. apply MKT46a; apply NNPP; auto.
  - unfold Unordered; destruct H; apply MKT43 in H;
    rewrite H; [rewrite MKT6|]; apply MKT20.
Qed.

(* 定理47  如果x与y是两个集，则∩[x|y]=x∩y同时∪[x|y]=x∪y; 如果x或者y不是一个集，则∩[x|y]=0同时∪[x|y]=u *)
Theorem MKT47a : ∀ x y, Ensemble x -> Ensemble y -> ∩[x|y] = x ∩ y.
Proof.
  intros; unfold Unordered; eqext; appA2H H1; appA2G.
  - split; apply H2; deGun; auto.
  - destruct H2; intros. deHun; eins H4.
Qed.

Theorem MKT47b : ∀ x y, Ensemble x -> Ensemble y
  -> ∪[x|y] = x ∪ y.
Proof.
  intros; unfold Unordered; eqext; appA2H H1; appA2G.
  - rdeHex. deHun; eins H3.
  - destruct H2; [exists x|exists y]; split; auto;
    apply MKT46b; auto. 
Qed.

Theorem MKT47' : ∀ x y, ~ Ensemble x \/ ~ Ensemble y
  -> (∩[x|y] = Φ) /\ (∪[x|y] = μ).
Proof.
  intros. apply MKT46' in H. rewrite H; split; symmetry;
  [apply MKT34|apply MKT34'].
Qed.

(* A.5 序偶：关系 *)

Theorem MKT49a : ∀ {x y}, Ensemble x -> Ensemble y
  -> Ensemble ([x,y]).
Proof.
  intros; unfold Ordered, Unordered.
  apply AxiomIV; [|apply MKT42,AxiomIV]; auto.
Qed.

Global Hint Resolve MKT49a : core.

Theorem MKT49b : ∀ x y, Ensemble ([x,y]) -> Ensemble x /\ Ensemble y.
Proof.
  intros. apply AxiomIV' in H as []. apply MKT42',
  AxiomIV' in H0 as []. split; apply MKT42'; auto.
Qed.

Theorem MKT49c1 : ∀ {x y}, Ensemble ([x,y]) -> Ensemble x.
Proof.
  intros. apply MKT49b in H; tauto.
Qed.

Theorem MKT49c2 : ∀ {x y}, Ensemble ([x,y]) -> Ensemble y.
Proof.
  intros. apply MKT49b in H; tauto.
Qed.

Ltac ope1 :=
  match goal with
    H: Ensemble ([?x,?y])
    |- Ensemble ?x => eapply MKT49c1; eauto
  end.

Ltac ope2 :=
  match goal with
    H: Ensemble ([?x,?y])
    |- Ensemble ?y => eapply MKT49c2; eauto
  end.

Ltac ope3 :=
  match goal with
    H: [?x,?y] ∈ ?z
    |- Ensemble ?x => eapply MKT49c1; eauto
  end.

Ltac ope4 :=
  match goal with
    H: [?x,?y] ∈ ?z
    |- Ensemble ?y => eapply MKT49c2; eauto
  end.

Ltac ope := try ope1; try ope2; try ope3; try ope4.

Theorem MKT49' : ∀ x y, ~ Ensemble ([x,y]) -> [x,y] = μ.
Proof.
  intros. apply MKT46'. apply notandor; intros [].
  apply H,AxiomIV; apply MKT42; auto.
Qed.

Fact subcp1 : ∀ x y, x ⊂ (x ∪ y).
Proof.
  unfold Included; intros. deGun; auto.
Qed.

Global Hint Resolve subcp1 : core.

(* 定理50  如果x与y均为集,则∪[x,y]=[x|y],∩[x,y]=[x],∪∩[x,y]=x,∩∩[x,y]=x,∪∪[x,y]=x∪y,∩∪[x,y]=x∩y如果x或者y不是一个集,则∪∩[x,y]=Φ,∩∩[x,y]=Φ,∪∪[x,y]=Φ,∩∪[x,y]=Φ *)
Lemma Lemma50a : ∀ x y, Ensemble x -> Ensemble y -> ∪[x,y] = [x|y].
Proof.
  intros; unfold Ordered. rewrite MKT47b; auto.
  apply MKT29; unfold Unordered; auto.
Qed.

Lemma Lemma50b : ∀ x y, Ensemble x -> Ensemble y -> ∩[x,y] = [x].
Proof.
  intros; unfold Ordered. rewrite MKT47a; auto.
  apply MKT30; unfold Unordered; auto.
Qed.

Theorem MKT50 : ∀ {x y}, Ensemble x -> Ensemble y
  -> (∪[x,y] = [x|y]) /\ (∩[x,y] = [x]) /\ (∪(∩[x,y]) = x)
    /\ (∩(∩[x,y]) = x) /\ (∪(∪[x,y]) = x∪y) /\ (∩(∪[x,y]) = x∩y).
Proof.
  repeat split; intros; repeat rewrite Lemma50a;
  repeat rewrite Lemma50b; auto; 
  [apply MKT44|apply MKT44|apply MKT47b|apply MKT47a]; auto.
Qed.

Lemma Lemma50' : ∀ (x y: Class), ~ Ensemble x \/ ~ Ensemble y
  -> ~ Ensemble ([x]) \/ ~ Ensemble ([x | y]).
Proof.
  intros. elim H; intros.
  - left; apply MKT43 in H0; auto. rewrite H0; apply MKT39; auto.
  - right; apply MKT46' in H; auto. rewrite H; apply MKT39; auto.
Qed.

Theorem MKT50' : ∀ {x y}, ~ Ensemble x \/ ~ Ensemble y
  -> (∪(∩[x,y]) = Φ) /\ (∩(∩[x,y]) = μ) /\ (∪(∪[x,y]) = μ)
    /\ (∩(∪[x,y]) = Φ).
Proof.
  intros. apply Lemma50',MKT47' in H as [].
  unfold Ordered. repeat rewrite H; repeat rewrite H0; repeat split;
  [apply MKT24'|apply MKT24|rewrite <-MKT34'|rewrite MKT34]; auto.
Qed.

(* 定义51  z的1st坐标=∩∩z *)
(* Definition First z := ∩(∩z). *)

(* 定义52  z的2nd坐标=(∩∪z)∪(∪∪z) ~ (∪∩z) *)
(* Definition Second z := (∩ ∪ z) ∪ ((∪(∪z)) ~ (∪(∩z))). *)

(* 定理53  μ的2nd坐标=μ *)
Theorem MKT53 : Second μ = μ.
Proof.
  intros; unfold Second, Setminus.
  repeat rewrite <-MKT34'; repeat rewrite <-MKT34.
  rewrite MKT24',MKT17,MKT21,MKT5'; auto.
Qed.

(* 定理54  如果x与y均为集,[x,y]的1st坐标=x同时[x,y]的2nd坐标=y
          如果x或者y不是一个集，则[x,y]的1st坐标=μ,同时[x,y]的2nd坐标=μ *)
Theorem MKT54a : ∀ x y, Ensemble x -> Ensemble y
  -> First ([x,y]) = x.
Proof.
  intros; unfold First. apply MKT50; auto.
Qed.

Theorem MKT54b : ∀ x y, Ensemble x -> Ensemble y
  -> Second ([x,y]) = y.
Proof.
  intros; unfold Second. New (MKT50 H H0). deand.
  rewrite H6,H5,H3. eqext.
  - appA2H H7. deor; [appA2H H8; tauto|].
    apply setminp in H8 as []. appA2H H8; tauto.
  - appA2G. TF (z ∈ x); [left; appA2G|].
    right. apply setminP; auto. appA2G.
Qed.

Theorem MKT54' : ∀ x y, ~ Ensemble x \/ ~ Ensemble y
  -> First ([x,y]) = μ /\ Second ([x,y]) = μ.
Proof.
  intros. New (MKT50' H). deand. unfold First, Second; split; auto.
  rewrite H3,H2,H0,MKT17. unfold Setminus.
  rewrite MKT6',MKT20'. apply MKT21.
Qed.

(* 定理55  如果x与y均为集,同时[x,y]=[u,v],则z=x同时y=v *)
Theorem MKT55 : ∀ x y u v, Ensemble x -> Ensemble y
  -> ([x,y] = [u,v] <-> x = u /\ y = v).
Proof.
  split; intros; [|destruct H1; subst; auto].
  assert (Ensemble ([x,y])); auto. rewrite H1 in H2.
  apply MKT49b in H2 as []. rewrite <-(MKT54a x y),H1,
  <-(MKT54b x y),H1,MKT54a,MKT54b; auto.
Qed.

Fact Pins : ∀ a b c d, Ensemble c -> Ensemble d
  -> [a,b] ∈ [[c,d]] -> a = c /\ b = d.
Proof.
  intros. eins H1. symmetry in H1. apply MKT55 in H1 as []; auto.
Qed.

Ltac pins H := apply Pins in H as []; subst; eauto.

Fact Pinfus : ∀ a b f x y, Ensemble x -> Ensemble y
  -> [a,b] ∈ (f ∪ [[x,y]]) -> [a,b] ∈ f \/ (a = x /\ b = y).
Proof.
  intros. deHun; auto. pins H1. 
Qed.

Ltac pinfus H := apply Pinfus in H as [?|[]]; subst; eauto.

Ltac eincus H := apply AxiomII in H as [_ [H|H]]; try eins H; auto.

Ltac PP H a b := apply AxiomII in H as [? [a [b []]]]; subst.

Fact AxiomII' : ∀ a b P,
  [a,b] ∈ \{\ P \}\ <-> Ensemble ([a,b]) /\ (P a b).
Proof.
  split; intros.
  - PP H x y. apply MKT55 in H0 as []; subst; auto; ope.
  - destruct H. appA2G.
Qed.

Ltac appoA2G := apply AxiomII'; split; eauto.

Ltac appoA2H H := apply AxiomII' in H as [].

(* 定理58  (r∘s)∘t=r∘(s∘t) *)
Theorem MKT58 : ∀ r s t, (r ∘ s) ∘ t = r ∘ (s ∘ t).
Proof.
  intros; eqext.
  - PP H a b. rdeHex. appoA2H H1. rdeHex.
    appoA2G. exists x0; split; auto. appoA2G. apply MKT49a; ope.
  - PP H a b. rdeHex. appoA2H H0. rdeHex.
    appoA2G. exists x0; split; auto. appoA2G. apply MKT49a; ope.
Qed.

(* 定理59  r∘(s∪t)=r∘s∪r∘t,同时r∘(s∩t)⊂r∩s∘r∩t *)
Theorem MKT59 : ∀ r s t, Relation r -> Relation s
  -> r ∘ (s ∪ t) = (r ∘ s) ∪ (r ∘ t)
    /\ r ∘ (s ∩ t) ⊂ (r ∘ s) ∩ (r ∘ t).
Proof.
  split; try red; intros; try eqext.
  - PP H1 a b. rdeHex. deHun; deGun; [left|right]; appoA2G.
  - deHun; PP H1 a b; rdeHex; appoA2G; 
    exists x; split; auto; deGun; auto.
  - PP H1 a b. rdeHex. deHin. deGin; appoA2G.
Qed.

Fact invp1 : ∀ a b f, [b,a] ∈ f⁻¹ <-> [a,b] ∈ f.
Proof.
  split; intros; [appoA2H H; tauto|appoA2G; apply MKT49a; ope].
Qed.

Fact uiv : ∀ a b, (a ∪ b)⁻¹ = a⁻¹ ∪ b⁻¹.
Proof.
  intros. eqext.
  - PP H x y. deHun; apply invp1 in H0; deGun; auto.
  - deHun; PP H x y; appoA2G; deGun; auto.
Qed.

Fact iiv : ∀ a b, (a ∩ b)⁻¹ = a⁻¹ ∩ b⁻¹.
Proof.
  intros. eqext.
  - PP H x y. deHin; deGin; apply invp1; auto.
  - deHin; PP H x y. apply invp1; deGin; [|apply invp1]; auto.
Qed.

Fact siv : ∀ a b, Ensemble a -> Ensemble b -> [[a,b]]⁻¹ = [[b,a]].
Proof.
  intros. eqext.
  - PP H1 x y. pins H3.
  - eins H1. appoA2G.
Qed.

(* 定理61  (r ⁻¹)⁻¹=r *)
Theorem MKT61 : ∀ r, Relation r -> (r⁻¹)⁻¹ = r.
Proof.
  intros; eqext.
  - PP H0 a b. appoA2H H2; auto.
  - New H0. apply H in H0 as [? [?]]; subst.
    appoA2G. apply invp1; auto.
Qed.

(* 定理62  (r∘s)⁻¹=(s⁻¹)∘(r⁻¹) *)
Theorem MKT62 : ∀ r s, (r ∘ s)⁻¹ = (s⁻¹) ∘ (r⁻¹).
Proof.
  intros; eqext.
  - PP H a b. appoA2H H1. rdeHex.
    appoA2G. exists x. split; appoA2G; apply MKT49a; ope.
  - PP H a b. rdeHex. appoA2H H0. appoA2H H1.
    apply invp1. appoA2G. apply MKT49a; ope.
Qed.

(* A.6 函数 *)

Fact opisf : ∀ a b, Ensemble a -> Ensemble b -> Function ([[a,b]]).
Proof.
  split; [red|]; intros; [eins H1|pins H1; pins H2].
Qed.

(* 定理64 如果f是一个函数同时g是一个函数，则 f∘g 也是一个函数 *)
Fact PisRel : ∀ P, Relation \{\ P \}\.
Proof.
  unfold Relation; intros. PP H a b; eauto.
Qed.

Global Hint Resolve PisRel : core.

Theorem MKT64 : ∀ f g, Function f -> Function g -> Function (f ∘ g).
Proof.
  split; intros; unfold Composition; auto.
  appoA2H H1. appoA2H H2. rdeHex. destruct H0.
  apply H with x0; auto. rewrite (H7 x x0 x1); auto.
Qed.

Corollary Property_dom : ∀ {x y f}, [x,y] ∈ f -> x ∈ dom(f).
Proof.
  intros. appA2G. ope.
Qed.

Corollary Property_ran : ∀ {x y f}, [x,y] ∈ f -> y ∈ ran(f).
Proof.
  intros. appA2G. ope.
Qed.

Fact deqri : ∀ f, dom(f) = ran(f⁻¹).
Proof.
  intros; eqext; appA2H H; rdeHex;
  [apply invp1 in H0|apply ->invp1 in H0]; appA2G.
Qed.

Fact reqdi : ∀ f, ran(f) = dom(f⁻¹).
Proof.
  intros; eqext; appA2H H; rdeHex; 
  [apply invp1 in H0|apply ->invp1 in H0]; appA2G.
Qed.

Fact subdom : ∀ {x y}, x ⊂ y -> dom(x) ⊂ dom(y).
Proof.
  unfold Included; intros. appA2H H0. rdeHex. appA2G.
Qed.

Fact undom : ∀ f g, dom(f ∪ g) = dom(f) ∪ dom(g).
Proof.
  intros; eqext.
  - appA2H H. rdeHex. deHun; deGun; [left|right]; appA2G.
  - deHun; appA2H H; rdeHex;
    appA2G; exists x; deGun; auto.
Qed.

Fact unran : ∀ f g, ran(f ∪ g) = ran(f) ∪ ran(g).
Proof.
  intros; eqext.
  - appA2H H. rdeHex. deHun; deGun; [left|right]; appA2G.
  - deHun; apply AxiomII in H as [? []];
    appA2G; exists x; deGun; auto.
Qed.

Fact domor : ∀ u v, Ensemble u -> Ensemble v -> dom([[u,v]]) = [u].
Proof.
  intros; eqext.
  - appA2H H1. rdeHex. pins H2.
  - eins H1. appA2G.
Qed.

Fact ranor : ∀ u v, Ensemble u -> Ensemble v -> ran([[u,v]]) = [v].
Proof.
  intros; eqext.
  - appA2H H1. rdeHex. pins H2.
  - eins H1. appA2G.
Qed.

Fact fupf : ∀ f x y, Function f -> Ensemble x -> Ensemble y
  -> ~ x ∈ dom(f) -> Function (f ∪ [[x,y]]).
Proof.
  repeat split; try red; intros.
  - destruct H. deHun; auto. eins H3.
  - pinfus H3; pinfus H4; [eapply H; eauto|..];
    elim H2; eapply Property_dom; eauto.
Qed.

Fact dos1 : ∀ {f x} y, Function f -> [x,y] ∈ f
  -> dom(f ~ [[x,y]]) = dom(f) ~ [x].
Proof.
  intros. eqext; appA2H H1; destruct H2.
  - apply setminp in H2 as []. New H2. apply Property_dom in H2.
    apply setminP; auto. intro. eins H5; ope.
    eapply H in H0; eauto. subst. elim H3; eauto.
  - appA2H H2. appA2H H3. destruct H4. appA2G. exists x0.
    apply setminP; auto. intro. pins H6; ope. 
Qed.

Fact ros1 : ∀ {f x y}, Function f⁻¹ -> [x,y] ∈ f
  -> ran(f ~ [[x,y]]) = ran(f) ~ [y].
Proof.
  intros. eqext; appA2H H1; destruct H2.
  - apply setminp in H2 as []. New H2. apply Property_ran in H2.
    apply setminP; auto. intro. eins H5; ope.
    New H0. apply invp1 in H0. apply invp1 in H4.
    eapply H in H0; eauto. subst. elim H3; eauto.
  - appA2H H2. appA2H H3. destruct H4. appA2G. exists x0.
    apply setminP; auto. intro. pins H6; ope. 
Qed.

(* 定理67 μ的定义域=μ同时μ的值域=μ *)
Theorem MKT67a: dom(μ) = μ.
Proof.
  eqext; eauto. appA2G. exists z. appA2G.
Qed.

Theorem MKT67b: ran(μ) = μ.
Proof.
  eqext; eauto. appA2G. exists z. appA2G.
Qed.

Theorem MKT69a : ∀ {x f}, x ∉ dom(f) -> f[x] = μ.
Proof.
  intros. unfold Value. rewrite <-MKT24. f_equal.
  eqext; try emf. appA2H H0. elim H. eapply Property_dom; eauto.
Qed.

Theorem MKT69b : ∀ {x f}, x ∈ dom(f) -> f[x] ∈ μ.
Proof.
  intros. appA2H H. destruct H0. apply MKT19,MKT35,NEexE.
  exists x0. appA2G. ope.
Qed.

Theorem MKT69a' : ∀ {x f}, f[x] = μ -> x ∉ dom(f).
Proof.
  intros. intro. elim MKT39. New (MKT69b H0). rewrite <-H ; eauto.
Qed.

Theorem MKT69b' : ∀ {x f}, f[x] ∈ μ -> x ∈ dom(f).
Proof.
  intros. Absurd. apply MKT69a in H0. rewrite H0 in H.
  elim MKT39; eauto.
Qed.

Corollary Property_Fun : ∀ y f x, Function f
  -> [x,y] ∈ f -> y = f[x].
Proof.
  intros; destruct H. eqext.
  - appA2G; intros. appA2H H3. rewrite (H1 _ _ _ H4 H0); auto.
  - appA2H H2. apply H3. appA2G. ope.
Qed.

Lemma uvinf : ∀ z a b f, ~ a ∈ dom(f) -> Ensemble a -> Ensemble b
  -> (z ∈ dom(f) -> (f ∪ [[a,b]])[z] = f[z]).
Proof.
  intros; eqext; appA2H H3; appA2G; intros.
  - apply H4. appA2H H5. appA2G. deGun; auto.
  - apply H4; appA2H H5. appA2G. pinfus H6. tauto.
Qed.

Lemma uvinp : ∀ a b f, ~ a ∈ dom(f) -> Ensemble a -> Ensemble b
  -> (f ∪ [[a,b]])[a] = b.
Proof.
  intros; apply AxiomI; split; intros.
  - appA2H H2. apply H3. appA2G. deGun; auto.
  - appA2G; intros. appA2H H3. pinfus H4. elim H.
    eapply Property_dom; eauto.
Qed.

Fact Einr : ∀ {f z}, Function f -> z ∈ ran(f)
  -> ∃ x, x ∈ dom(f) /\ z = f[x].
Proof.
  intros. appA2H H0. destruct H1. New H1. apply Property_dom in H1.
  apply Property_Fun in H2; eauto.
Qed.

Ltac einr H := New H; apply Einr in H as [? []]; subst; auto.

(* 定理70 如果f是一个函数，则f={[x,y]:y=f[x]} *)
Theorem MKT70 : ∀ f, Function f -> f = \{\ λ x y, y = f[x] \}\.
Proof.
  intros; eqext.
  - New H0. apply H in H0 as [? [?]]. subst. appoA2G.
    apply Property_Fun; auto.
  - PP H0 a b. apply MKT49b in H0 as [].
    apply MKT19,MKT69b' in H1. appA2H H1. destruct H2.
    rewrite <-(Property_Fun x); auto.
Qed.

(* 值的性质 一 *)
Corollary Property_Value : ∀ {f x}, Function f -> x ∈ dom(f)
  -> [x,f[x]] ∈ f.
Proof.
  intros. rewrite MKT70; auto. New (MKT69b H0). appoA2G.
Qed.

Fact subval : ∀ {f g}, f ⊂ g -> Function f -> Function g
  -> ∀ u, u ∈ dom(f) -> f[u] = g[u].
Proof.
  intros. apply Property_Fun,H,Property_Value; auto.
Qed.

(* 值的性质 二 *)
Corollary Property_Value' : ∀ f x, Function f -> f[x] ∈ ran(f)
  -> [x,f[x]] ∈ f.
Proof.
  intros. rewrite MKT70; auto. appoA2G. apply MKT49a; eauto.
  exists dom(f). apply MKT69b', MKT19; eauto.
Qed.

Corollary Property_dm : ∀ {f x}, Function f -> x ∈ dom(f)
  -> f[x] ∈ ran(f).
Proof.
  intros. apply Property_Value in H0; auto. appA2G. ope. 
Qed.

(* 定理71 如果f和g都是函数，则f=g的充要条件是对于每个x，f[x]=g[x] *)
Theorem MKT71 : ∀ f g, Function f -> Function g
  -> (f = g <-> ∀ x, f[x] = g[x]).
Proof.
  split; intros; subst; auto.
  rewrite (MKT70 f),(MKT70 g); auto. eqext; PP H2 a b; appoA2G.
Qed.

Ltac xo :=
  match goal with
    |- Ensemble ([?a, ?b]) => try apply MKT49a
  end.

Ltac rxo := eauto; repeat xo; eauto.

(* 定理73 如果u与y均为集，则[u]×y也是集*)
Lemma Ex_Lemma73 : ∀ {u y}, Ensemble u -> Ensemble y
  -> let f:= \{\ λ w z, w ∈ y /\ z = [u,w] \}\ in
    Function f /\ dom(f) = y /\ ran(f) = [u] × y.
Proof.
  repeat split; intros; auto.
  - appoA2H H1; appoA2H H2. deand. subst. auto.
  - eqext.
    + appA2H H1. rdeHex. appoA2H H2; tauto.
    + appA2G. exists [u,z]. appoA2G; rxo.
  - eqext.
    + appA2H H1. rdeHex. appoA2H H2. deand. subst. appoA2G.
    + appA2G. PP H1 a b. deand. eins H2. exists b. appoA2G.
Qed.

Theorem MKT73 : ∀ u y, Ensemble u -> Ensemble y
  -> Ensemble ([u] × y).
Proof.
  intros. New (Ex_Lemma73 H H0). destruct H1,H2.
  rewrite <-H2 in H0. rewrite <-H3. apply AxiomV; auto.
Qed.

(* 定理74 如果x与y均为集，则 x×y 也是集 *)
Lemma Ex_Lemma74 : ∀ {x y}, Ensemble x -> Ensemble y
  -> let f := \{\ λ u z, u ∈ x /\ z = [u] × y \}\ in
    Function f /\ dom(f) = x
    /\ ran(f) = \{ λ z, ∃ u, u ∈ x /\ z = [u] × y \}.
Proof.
  repeat split; intros; auto.
  - appoA2H H1; appoA2H H2. deand. subst. auto.
  - eqext.
    + appA2H H1. rdeHex. appoA2H H2; tauto.
    + appA2G. exists ([z] × y). appoA2G; rxo. apply MKT73; eauto.
  - eqext.
    + appA2H H1. rdeHex. appoA2H H2. deand. subst. appA2G.
    + appA2G. appA2H H1. rdeHex. exists x0. appoA2G.
Qed.

Lemma Lemma74 : ∀ {x y}, Ensemble x -> Ensemble y
  -> ∪(\{ λ z, ∃ u, u ∈ x /\ z = [u] × y \}) = x × y.
Proof.
  intros; eqext.
  - appA2H H1. rdeHex. appA2H H3. rdeHex. subst.
    PP H2 a b. deand. eins H5. subst. appoA2G.
  - PP H1 a b. deand. appA2G. exists [a] × y. split; try appoA2G.
    appA2G; rxo. apply MKT73; eauto.
Qed.

Theorem MKT74 : ∀ {x y}, Ensemble x -> Ensemble y
  -> Ensemble (x × y).
Proof.
  intros. New (Ex_Lemma74 H H0). destruct H1,H2.
  rewrite <-Lemma74,<-H3; auto. rewrite <-H2 in H.
  apply AxiomVI,AxiomV; auto.
Qed.

(* 定理75 如果f是一个函数同时f的定义域是一个集，则f是一个集 *)
Theorem MKT75 : ∀ f, Function f -> Ensemble dom(f) -> Ensemble f.
Proof.
  intros. New (MKT74 H0 (AxiomV H H0)). eapply MKT33; eauto.
  red; intros. New H2. apply H in H2 as [? []]. subst.
  appoA2G; split; [eapply Property_dom|eapply Property_ran]; eauto.
Qed.

Fact fdme : ∀ {f}, Function f -> Ensemble f -> Ensemble dom(f).
Proof.
  intros. set (g := \{\ λ u v, u ∈ f /\ v = First u \}\).
  assert (Function g).
  { unfold g; split; intros; auto.
    appoA2H H1. appoA2H H2. deand; subst; auto. }
  assert (dom(g) = f).
  { eqext.
    - appA2H H2. rdeHex. appoA2H H3; tauto.
    - appA2G. exists (First z). appA2G. rxo. New H2.
      apply H in H2 as [? []]. subst. rewrite MKT54a; ope. }
  assert (ran(g) = dom(f)).
  { eqext.
    - appA2H H3. rdeHex. appoA2H H4. deand. subst z.
      New H5. apply H in H5 as [? []]. subst x.
      rewrite MKT54a; ope. eapply Property_dom; eauto.
    - appA2H H3. rdeHex. appA2G. exists [z,x]. appoA2G.
      split; auto. rewrite MKT54a; ope; auto. }
  rewrite <-H3. rewrite <-H2 in H0. apply AxiomV; auto.
Qed.

Fact frne : ∀ {f}, Function f -> Ensemble f -> Ensemble ran(f).
Proof.
  intros. apply AxiomV; [|apply fdme]; auto. 
Qed.

(* 定理77 如果x与y均为集，则 Exponent y x 也是集*)
Theorem MKT77 : ∀ x y, Ensemble x -> Ensemble y
  -> Ensemble (Exponent y x).
Proof.
  intros. apply MKT33 with (x := (pow(x × y))).
  - apply MKT38a,MKT74; auto.
  - red; intros. apply MKT38b; [apply MKT74; auto|].
    red; intros. appA2H H1. deand. New H2. apply H3 in H2 as [? []].
    subst. New (Property_dom H6). New (Property_ran H6). appoA2G.
Qed.

(* A.7 良序 *)

Fact Property_Asy : ∀ {r x u}, Asymmetric r x -> u ∈ x
  -> ~ Rrelation u r u.
Proof.
  intros; intro; eapply H; eauto.
Qed.

Corollary wosub : ∀ x r y, WellOrdered r x -> y ⊂ x
  -> WellOrdered r y.
Proof.
  unfold WellOrdered, Connect; intros; destruct H; split; intros.
  - apply H; auto.
  - apply (H1 _ (MKT28 H2 H0) H3).
Qed.

(* 定理88 *)
Theorem MKT88a : ∀ {r x}, WellOrdered r x -> Asymmetric r x.
Proof.
  intros * []. red; intros; intro.
  assert ([u | v] ⊂ x).
  { red; intros. apply MKT46b in H5 as []; subst; eauto. }
  assert ([u | v] ≠ Φ).
  { apply NEexE; exists u. apply MKT46b; eauto. }
  destruct (H0 _ H5 H6) as [z []].
  apply MKT46b in H7 as []; subst; eauto;
  [apply (H8 v)|apply (H8 u)]; auto; apply MKT46b; eauto. 
Qed.

Theorem MKT88b : ∀ r x, WellOrdered r x -> Transitive r x.
Proof.
  intros. New (MKT88a H). destruct H. red; intros.
  destruct (H _ _ H2 H4) as [?|[?|?]]; auto.
  - assert ([u] ∪ [v] ∪ [w] ⊂ x). { red; intros. deHun; eins H8. }
    assert ([u] ∪ [v] ∪ [w] ≠ Φ).
    { apply NEexE; exists u. deGun. eauto. }
    destruct (H1 _ H8 H9) as [z []]. deHun; eins H10; 
    [destruct (H11 w)|destruct (H11 u)|destruct (H11 v)]; auto.
    + deGun. right. deGun. eauto.
    + deGun. eauto.
    + deGun. right. deGun. eauto.
  - subst; destruct (H0 _ _ H2 H3); auto.
Qed.

(* 定理90 *)
Theorem MKT90 : ∀ n x r, n ≠ Φ -> (∀ y, y ∈ n -> rSection y r x)
  -> rSection (∩n) r x /\ rSection (∪n) r x.
Proof.
  intros. NEele H. New H. apply H0 in H as [? []].
  split; split; try split; auto; try red; intros.
  - appA2H H4; auto.
  - appA2G; intros. New H7. appA2H H5. apply H9 in H8.
    destruct (H0 _ H7) as [? []]. eapply H12; eauto.
  - appA2H H4. rdeHex. apply (H0 _ H6); auto.
  - appA2H H5. rdeHex. destruct (H0 _ H8) as [? []]. appA2G.
Qed.

(* 定理91 *)
Theorem MKT91 : ∀ {x y r}, rSection y r x ->  y <> x
  -> (∃ v, v ∈ x /\ y = \{ λ u, u ∈ x /\ Rrelation u r v \}).
Proof.
  intros. assert (∃ v, FirstMember v r (x ~ y)).
  { apply H.
    - red; intros. apply MKT4' in H1; tauto.
    - intro. apply H0. destruct H. apply MKT27; split; auto.
      red; intros. Absurd. feine z. rewrite <-H1; auto. }
  destruct H1 as [v []]. apply setminp in H1 as [].
  exists v; split; auto. destruct H as [? []]. eqext.
  - appA2G. split; auto. destruct H4.
    New (H4 _ _ H1 (H _ H6)). deor; auto.
    + elim H3. eapply H5; eauto.
    + subst. elim H3; auto.
  - appA2H H6. deand. Absurd. destruct (H2 z); auto.
Qed.

(* 定理92 *)
Theorem MKT92 : ∀ {x y z r}, rSection x r z -> rSection y r z
  -> x ⊂ y \/ y ⊂ x.
Proof.
  intros. TF (x ⊂ y); auto.
  right; red; intros. destruct H,H0,H3,H4.
  assert (∃ z1,z1 ∈ x /\ ~ (z1 ∈ y)).
  { Absurd. elim H1. red; intros. Absurd. elim H7; eauto. }
  rdeHex. apply H5 with x0; auto. destruct H3.
  New (H3 _ _ (H0 _ H2) (H _ H7)). deor; auto.
  - elim H8. eapply H6; eauto.
  - subst. elim H8; auto.
Qed.

(* 定理94 *)
Theorem MKT94 : ∀ {x r y f}, rSection x r y -> Order_Pr f r r
  -> On f x -> To f y -> (∀ u, u ∈ x -> ~ Rrelation f[u] r u).
Proof.
  intros; intro. destruct H,H5,H5,H0,H8,H9,H1,H2 as [_].
  assert (u ∈ \{ λ u, u ∈ x /\ Rrelation f[u] r u \} ). { appA2G. }
  assert (∃ z, FirstMember z r \{ λ u, u ∈ x
    /\ Rrelation f[u] r u \}).
  { apply H7; [|apply NEexE; eauto].
    red; intros. appA2H H13. deand. auto. }
  destruct H13 as [v []]. appA2H H13. deand. subst x.
  assert (f[v] ∈ y). { apply H2, Property_dm; auto. }
  New (H6 _ _ H11 H15 H16). New (H10 _ _ H17 H15 H16).
  apply H14 with f[v]; auto. appA2G.
Qed.

Lemma f11vi : ∀ f u, Function f -> Function f⁻¹ -> u ∈ ran(f)
  -> f[(f⁻¹)[u]] = u.
Proof.
  intros. rewrite reqdi in H1. apply Property_Value in H1; auto.
  apply ->invp1 in H1; auto. apply Property_Fun in H1; auto.
Qed.

Lemma f11inj : ∀ f a b, Function f -> Function f⁻¹
  -> a ∈ dom(f) -> b ∈ dom(f) -> f[a] = f[b] -> a = b.
Proof.
  intros. destruct H0. eapply H4 with f[a]; apply invp1;
  [|rewrite H3]; apply Property_Value; auto.
Qed.

Lemma f11iv : ∀ f u, Function f -> Function f⁻¹ -> u ∈ dom(f)
  -> (f⁻¹)[f[u]] = u.
Proof.
  intros. apply Property_Value,invp1,Property_Fun in H1; auto.
Qed.

Fact f11pa : ∀ {f x y}, Function1_1 f -> [x,y] ∈ f
  -> Function1_1 (f ~ [[x,y]]).
Proof.
  intros * [] ?. repeat split; try red; intros.
  - appA2H H2. apply H; tauto.
  - apply setminp in H2. apply setminp in H3. deand.
    eapply H; eauto.
  - PP H2 a b; eauto.
  - appoA2H H2. appoA2H H3. apply setminp in H4.
    apply setminp in H5. deand. eapply H0; apply invp1; eauto.
Qed.

Fact f11pb : ∀ f x y, Function1_1 f -> Ensemble x -> Ensemble y
  -> ~ x ∈ dom(f) -> ~ y ∈ ran(f) -> Function1_1 (f ∪ [[x,y]]).
Proof.
  intros. destruct H. split.
  - apply fupf; auto.
  - rewrite reqdi in H3. rewrite uiv.
    rewrite siv; auto. apply fupf; auto.
Qed.

(* 定理96 *)
Theorem MKT96a : ∀ {f r s}, Order_Pr f r s -> Function1_1 f.
Proof.
  intros. destruct H as [? [? []]].
  split; auto; split; try red; intros.
  - PP H3 a b. eauto.
  - apply ->invp1 in H3. apply ->invp1 in H4. New H3. New H4.
    apply Property_Fun in H3; apply Property_Fun in H4; subst; auto.
    New (Property_dom H5). New (Property_dom H6).
    New (Property_ran H6). destruct H0.
    New (H0 _ _ H3 H7). deor; auto.
    + New (H2 _ _ H3 H7 H10). rewrite <-H4 in H11.
      destruct (MKT88a H1 _ _ H8 H8 H11); auto.
    + New (H2 _ _ H7 H3 H10). rewrite <-H4 in H11.
      destruct (MKT88a H1 _ _ H8 H8 H11); auto.
Qed.

Theorem MKT96b : ∀ {f r s}, Order_Pr f r s -> Order_Pr (f⁻¹) s r.
Proof.
  intros. destruct (MKT96a H) as [_]. red in H. deand.
  red. rewrite <-deqri,<-reqdi. deandG; auto. intros.
  New H4. New H5. destruct H1. einr H7. einr H8.
  rewrite f11iv,f11iv; auto. apply MKT88a in H2.
  New (H1 _ _ H7 H8). deor; subst; auto.
  - New (H3 _ _ H8 H7 H12). destruct (H2 f[x] f[x0]); auto.
  - destruct (H2 f[x0] f[x0]); auto.
Qed.

Theorem MKT96 : ∀ f r s, Order_Pr f r s
  -> Function1_1 f /\ Order_Pr (f⁻¹) s r.
Proof.
  split; intros; [eapply MKT96a|apply MKT96b]; eauto.
Qed.

(* 定理97 *)
Lemma lem97a :  ∀ f g u r s x y, Order_Pr f r s -> Order_Pr g r s
  -> rSection dom(f) r x -> rSection dom(g) r x
  -> rSection ran(f) s y -> rSection ran(g) s y
  -> FirstMember u r (\{ λ a, a ∈ (dom(f) ∩ dom(g))
    /\ f [a] <> g [a] \}) -> Rrelation f[u] s g[u] -> False.
Proof.
  intros. New H0. apply MKT96b in H as G.
  destruct H as [H _],H0 as [H0],H8,H9,H3,H11,H4,H5,H13.
  appA2H H5. deand. deHin. New H16; New H18.
  apply Property_dm in H16; apply Property_dm in H18; auto.
  New (H15 _ _ (H3 _ H16) H18 H6). apply AxiomII in H21 as [_ [v]].
  New (Property_dom H21). apply Property_Fun in H21; auto.
  rewrite H21 in H6. assert (Rrelation v r u).
  { apply MKT96b in H7 as [? [_ [_ ?]]]. New H22.
    apply Property_dm in H22; auto. rewrite reqdi in H22,H18.
    New (H23 _ _ H22 H18 H6). do 2 rewrite f11iv in H25; auto. }
  destruct H1 as [? []],H2 as [? []].
  New (H25 _ _ (H2 _ H22) H19 H23). apply (H14 v); auto.
  appA2G. split; deGin; auto. intro. rewrite <-H21 in H29.
  destruct G as [? _]. eapply f11inj in H29; eauto. subst.
  eapply Property_Asy; eauto. apply MKT88a; auto.
Qed.

Lemma le97 : ∀ f g, Function f -> Function g
  -> (∀ a, a ∈ (dom(f) ∩ dom(g)) -> f[a] = g[a])
  -> dom(f) ⊂ dom(g) -> f ⊂ g.
Proof.
  intros. apply MKT30 in H2. rewrite H2 in H1. red; intros.
  New H3. rewrite MKT70 in H3; auto. PP H3 a b.
  apply Property_dom in H4. rewrite H1 in *; auto.
  rewrite MKT70; auto. appoA2G.
Qed.

Theorem MKT97 :  ∀ {f g r s x y}, Order_Pr f r s -> Order_Pr g r s
  -> rSection dom(f) r x -> rSection dom(g) r x
  -> rSection ran(f) s y -> rSection ran(g) s y -> f ⊂ g \/ g ⊂ f.
Proof.
  intros f g r s x y Hf Hg Hdomf Hdomg Hranf Hrang.
  (* Keep copies of the original hypotheses before destructing *)
  pose proof Hf as Hf_ord.
  pose proof Hg as Hg_ord.
  pose proof Hranf as Hranf_ord.
  pose proof Hrang as Hrang_ord.
  destruct Hf as [HfFunc [HfWOr [HsWOf HfOP]]].
  destruct Hg as [HgFunc [HgWOr [HsWOg HgOP]]].
  destruct (MKT92 Hdomf Hdomg) as [Hd|Hd].
  - (* dom(f) ⊂ dom(g) *)
    left. apply le97 with (f := f) (g := g); auto.
    intros a Ha.
    apply MKT4' in Ha. destruct Ha as [Ha_f Ha_g].
    TF (f[a] = g[a]); auto. exfalso.
    rename H into Hneq.
    set (S := \{ λ a, a ∈ (dom(f) ∩ dom(g)) /\ f[a] <> g[a] \}).
    assert (HS_sub : S ⊂ dom(f)).
    { unfold S, Included; intros z Hz.
      apply AxiomII in Hz as [_ [Hz_in _]].
      apply MKT4' in Hz_in. tauto. }
    assert (HS_ne : S ≠ Φ).
    { apply NEexE. exists a. unfold S.
      apply AxiomII; split.
      - apply AxiomII in Ha_f. tauto.
      - split.
        + apply MKT4'; split; auto.
        + auto. }
    destruct HfWOr as [_ HfWO'].
    destruct (HfWO' S HS_sub HS_ne) as [u Hu].
    destruct Hu as [HuS HuFirst].
    apply AxiomII in HuS as [Hens_u [Hu_in Huneq]].
    apply MKT4' in Hu_in. destruct Hu_in as [Hu_f Hu_g].
    destruct Hranf as [Hranf_sub [HsWO _]].
    destruct HsWO as [HsConn _].
    assert (Hfu_y : f[u] ∈ y).
    { apply Hranf_sub. apply Property_dm; auto. }
    assert (Hgu_y : g[u] ∈ y).
    { destruct Hrang as [Hrang_sub _].
      apply Hrang_sub. apply Property_dm; auto. }
    destruct (HsConn f[u] g[u] Hfu_y Hgu_y) as [Hrel|[Hrel|Heq]].
    + eapply (lem97a f g u r s x y Hf_ord Hg_ord Hdomf Hdomg
        Hranf_ord Hrang_ord).
      * split; [|exact HuFirst].
        apply AxiomII; split; auto.
        split; [apply MKT4'; split|]; auto.
      * exact Hrel.
    + (* Rrelation g[u] s f[u] — symmetric case, need FirstMember for swapped set *)
      assert (HuS_sym : u ∈ (\{ λ a, a ∈ (dom(g) ∩ dom(f)) /\ g[a] <> f[a] \})).
      { apply AxiomII; split; auto.
        split; [apply MKT4'; split; auto|].
        intro H; apply Huneq; symmetry; auto. }
      assert (HuFirst_sym : ∀ y0, y0 ∈ (\{ λ a, a ∈ (dom(g) ∩ dom(f)) /\ g[a] <> f[a] \}) -> ~ Rrelation y0 r u).
      { intros y0 Hy0. apply AxiomII in Hy0 as [Hens_y [Hy0_in Hneq']].
        apply MKT4' in Hy0_in. destruct Hy0_in as [Hy0_g Hy0_f].
        apply HuFirst. apply AxiomII; split; auto.
        split; [apply MKT4'; split; auto|].
        intro H; apply Hneq'; symmetry; auto. }
      eapply (lem97a g f u r s x y Hg_ord Hf_ord Hdomg Hdomf
        Hrang_ord Hranf_ord).
      * split; [exact HuS_sym|exact HuFirst_sym].
      * exact Hrel.
    + apply Huneq; auto.
  - (* dom(g) ⊂ dom(f) *)
    right. apply le97 with (f := g) (g := f); auto.
    intros a Ha.
    apply MKT4' in Ha. destruct Ha as [Ha_g Ha_f].
    TF (g[a] = f[a]); auto. exfalso.
    rename H into Hneq.
    set (S := \{ λ a, a ∈ (dom(g) ∩ dom(f)) /\ g[a] <> f[a] \}).
    assert (HS_sub : S ⊂ dom(g)).
    { unfold S, Included; intros z Hz.
      apply AxiomII in Hz as [_ [Hz_in _]].
      apply MKT4' in Hz_in. tauto. }
    assert (HS_ne : S ≠ Φ).
    { apply NEexE. exists a. unfold S.
      apply AxiomII; split.
      - apply AxiomII in Ha_g. tauto.
      - split.
        + apply MKT4'; split; auto.
        + auto. }
    destruct HgWOr as [_ HgWO'].
    destruct (HgWO' S HS_sub HS_ne) as [u Hu].
    destruct Hu as [HuS HuFirst].
    apply AxiomII in HuS as [Hens_u [Hu_in Huneq]].
    apply MKT4' in Hu_in. destruct Hu_in as [Hu_g Hu_f].
    destruct Hrang as [Hrang_sub [HsWO _]].
    destruct HsWO as [HsConn _].
    assert (Hgu_y : g[u] ∈ y).
    { apply Hrang_sub. apply Property_dm; auto. }
    assert (Hfu_y : f[u] ∈ y).
    { destruct Hranf as [Hranf_sub _].
      apply Hranf_sub. apply Property_dm; auto. }
    destruct (HsConn g[u] f[u] Hgu_y Hfu_y) as [Hrel|[Hrel|Heq]].
    + eapply (lem97a g f u r s x y Hg_ord Hf_ord Hdomg Hdomf
        Hrang_ord Hranf_ord).
      * split; [|exact HuFirst].
        apply AxiomII; split; auto.
        split; [apply MKT4'; split|]; auto.
      * exact Hrel.
    + (* Rrelation f[u] s g[u] — symmetric case *)
      assert (HuS_sym : u ∈ (\{ λ a, a ∈ (dom(f) ∩ dom(g)) /\ f[a] <> g[a] \})).
      { apply AxiomII; split; auto.
        split; [apply MKT4'; split; auto|].
        intro H; apply Huneq; symmetry; auto. }
      assert (HuFirst_sym : ∀ y0, y0 ∈ (\{ λ a, a ∈ (dom(f) ∩ dom(g)) /\ f[a] <> g[a] \}) -> ~ Rrelation y0 r u).
      { intros y0 Hy0. apply AxiomII in Hy0 as [Hens_y [Hy0_in Hneq']].
        apply MKT4' in Hy0_in. destruct Hy0_in as [Hy0_f Hy0_g].
        apply HuFirst. apply AxiomII; split; auto.
        split; [apply MKT4'; split; auto|].
        intro H; apply Hneq'; symmetry; auto. }
      eapply (lem97a f g u r s x y Hf_ord Hg_ord Hdomf Hdomg
        Hranf_ord Hrang_ord).
      * split; [exact HuS_sym|exact HuFirst_sym].
      * exact Hrel.
    + apply Huneq; auto.
Qed.
