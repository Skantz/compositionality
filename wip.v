(* Compositionality proof by @Skantz - August 2021 *)

(* MSets appear to be the most powerful implementation of sets in Coq.
   Under the hood, MSetAVL let's us define sets of sets, which
   is not possible using MSetLists. *)

Require Import Coq.Logic.FunctionalExtensionality.

Require Import Coq.MSets.MSetList.
Require Import Coq.MSets.MSetFacts.
Require Import Coq.MSets.MSetProperties.

Require Import Coq.FSets.FMapPositive.
Require Import Coq.FSets.FMapFacts.
Require Import Coq.PArith.BinPos.
Require Import Coq.MSets.MSetAVL.


Require Import List.
Open Scope list_scope.

Import ListNotations. (* Let's us write e.g. [vb ; ib ; l]. *)

(* Enables definitions with implicit arguments given by curly brackets { } *)
Set Implicit Arguments.

Require Import Coq.Arith.Compare_dec.

(* Importing some tactics allowing for automation over MSets *)
Require Import Coq.MSets.MSetRBT.
Require Import Coq.MSets.MSetProperties.
Require Import Coq.Structures.OrdersEx.
Require Import Coq.rtauto.Rtauto.

(* Encoding variables and behaviors as modules over natural numbers.
   This gives us stricly more properties than we asked for,
   but serves as a useful off-the-shelf set with equality to make MSetAVLs. 
 *)

Module VSet := MSetAVL.Make Nat_as_DT. (* Variables *)
Module BSet := MSetAVL.Make Nat_as_DT. (* Behaviors *)
Module BSet2 := MSetAVL.Make BSet.
Module BSet3 := MSetAVL.Make BSet2.

(* The following modules contain many helpful lemmas for reasoning over sets. *)

Module VSetFacts := MSetFacts.Facts VSet.
Module VSetProps := MSetProperties.Properties VSet.

Module BSetFacts := MSetFacts.Facts BSet.
Module BSetProps := MSetProperties.Properties BSet.

Module BSet2Facts := MSetFacts.Facts BSet2.
Module BSet2Props := MSetProperties.Properties BSet2.


(* Importing decision procedures over MSets - defining the module over BSet2
   gave slightly better automation. *)
Module D := MSetDecide.WDecide BSet2.
Import D.MSetLogicalFacts.


Parameter Val : Type.
Parameter V : Set.

Require Import List.
Open Scope list_scope.


(** Our base types - Components and Specifications.
    Components are sets of behaviors (represented as natural numbers),
    or tuples of sets of behaviors.

    Specifications are sets of components.*)
Definition C := BSet.t.

Definition Composition (c1 c2 : BSet.t) := (BSet.inter c1 c2).

(* Powersets of specifications - used for filtering specifications *)

Definition B3add (e : BSet2.elt) (s : BSet3.t) : BSet3.t :=
  BSet3.fold (fun s' accu => BSet3.add (BSet2.add e s') accu) s s.

Definition B3powerset (s : BSet2.t) : BSet3.t :=
  BSet2.fold B3add s BSet3.empty.

Definition B3filter (f : BSet3.elt -> bool) (candidates : BSet2.t ) : BSet3.t.
Proof.
  exact (BSet3.fold (fun s acc =>
                         match (f s) with
                         | true => BSet3.add s acc
                         | false => acc
                      end )  (B3powerset candidates)  BSet3.empty).
Defined.

Definition B2add (e : BSet.elt) (b : BSet2.t) : BSet2.t :=
  BSet2.fold (fun b' accu => BSet2.add (BSet.add e b') accu) b b.

Definition B2powerset (b : BSet.t) : BSet2.t :=
  BSet.fold B2add b BSet2.empty.

Require Import Coq.ssr.ssrbool.

Definition B2filter (f : BSet2.elt -> bool) (candidates : BSet.t ) : BSet2.t.
Proof.
  exact (BSet2.fold (fun s acc =>
                         match (f s) with
                         | true => BSet2.add s acc
                         | false => acc
                      end )  (B2powerset candidates)  BSet2.empty).
Defined.

Variable UniverseB : BSet.t.
Axiom uniaxB : forall (bset : BSet.t), BSet.Subset bset UniverseB.

Variable UniverseB2 : BSet2.t.
Axiom uniaxB2 : forall (bset : BSet2.t), BSet2.Subset bset UniverseB2.

Definition S' := BSet2.t.

Definition Conjunction (s1 s2 : S') := (BSet2.inter s1 s2).
Definition Parallel (s1 s2 : S') :=
  B2filter (fun (x : BSet.t)  => andb (BSet2.mem x s1) (BSet2.mem x s2)) UniverseB.

(* Slightly convoluted way of defining contracts in terms of rudimentary
   lambda functions, encoding implication as or (neg premise, conclusion) *)
Definition Contract (s1 s2 : S') :=
  B2filter ( (let s1' := s1 in let s2' := s2 in
    fun (x : BSet.t) =>  orb (negb (BSet2.mem x s1'))
        (BSet2.mem x (BSet2.inter  s1' s2' )))) UniverseB.

Notation "A × B" := (Composition A B)  (at level 50) : type_scope.
Notation "A ⊓ B" := (Conjunction A B)  (at level 50) : type_scope.
Notation "A |||| B" := (Parallel A B)  (at level 50) :  type_scope.
Notation "A ,, B" := (Contract A B) (at level 50) : type_scope.

Definition Copyright : S' :=
  B2filter (fun (x : BSet.t) =>  negb (BSet.equal x BSet.empty)) UniverseB.
Notation "©" := Copyright.

Parameter I : VSet.t -> S'.

Definition Implements (c : C) (s : S') := BSet2.In c s.
Notation "A <| B"  := (Implements A B) (at level 50) : type_scope.

Notation  "c1 ∩ c2" := (Composition c1 c2)  (at level  50) : type_scope.
Notation  "s1 ∩ s2" := (Conjunction s1 s2)  (at level  50) : type_scope.

Definition Refines (s1 s2 : S') := BSet2.Subset s1 s2.
Notation "A ⊑ B" := (Refines A B) (at level 50) : type_scope.

Axiom Prop7 : forall (a1 a2 g1 g2 : S'),
  Refines a2 a1 ->
  Refines g1 g2 ->
  Refines (a1 ,, g1) (a2 ,, g2).

Parameter InExpr : S' -> VSet.t -> Prop.

Notation "S ∈ vset " := (InExpr S vset) (at level 50) : type_scope.

Parameter Assertional  : S' -> Prop.
Axiom AssertionalEx : forall (x1 x2 : C) (s : S') (p : Assertional s),
  Implements x1 s -> Implements (Composition x1 x2) s.

Variable Receptiveness : VSet.t -> S'.
Notation R vset := (Receptiveness vset).

(* This one is slightly tricky and unsatisfying - ideally we would like to enforce at
   Module level that all elements of a set are restricted by some generator.
   As our off-the-shelf solution is using all natural numbers to represent our
   universe, we have to introduce an axiom stating that some collection of variables
   is the universe. That however gives poor generalizability, as this axiom will only be
   valid for a given composition - see an example of a proof of a composition later in this document. *)

(* Thus, a universe is a set V of type X, and a proof that all other sets of type X are subsets of V. *)

Definition IsUniverseV (uu : VSet.t) :=
  forall v : (VSet.t),  VSet.Subset v uu.

Definition MkUniverseV (vset : VSet.t) (p : IsUniverseV vset) : (sig IsUniverseV).
Proof.
  intros.
  exact ((exist _ vset p)).
Defined.

Definition VComplement {universe : (sig IsUniverseV)} (x : VSet.t) := VSet.diff (proj1_sig universe) x.

Axiom ImplementRefines : forall (c : C) (s1 s2 : S'),
  Implements c s1 -> Refines s1 s2 -> Implements c s2.

Axiom ImplementsComposable1 : forall (c1 c2 : C) (s : S'),
    Implements (Composition c1 c2) s ->
    Implements c1 s.

Axiom ImplementsComposable2: forall (c1 c2 : C) (s : S') (p : Assertional s),
    Implements c1 s ->
    Implements (Composition c1 c2) s.

Axiom ContractIntro: forall (q0 c : C) (s1 s2 : S'),
    (forall (q1 : C), (q1 <| s1) -> Composition q1 c <| s2 ) -> c <| (s1 ,, s2).

Axiom ContractElim: forall (c1 c2 : C) (s1 s2 : S'),
    Implements c1 s1 -> Implements c2 (s1 ,, s2) -> Implements (Composition c1 c2) s2.

(* Demonstration a proof strategy for this family of axioms, by which also the rest could
   be proven. *)
Lemma CompComm : forall (c1 c2 : C), BSet.Equal (Composition c1 c2) (Composition c2 c1).
Proof.
  intros.
  unfold Composition.
  rewrite <- BSetProps.inter_sym.
  rewrite BSetFacts.equal_iff.
  rewrite <- BSetFacts.equal_iff.
  apply BSetProps.equal_refl.
Defined.

Lemma CompAssoc :  forall (c1 c2 c3 : C),
    BSet.Equal (Composition (Composition c1 c2) c3)
               (Composition c1 (Composition c2 c3)).
Proof.
  intros.
  rewrite BSetProps.inter_assoc.
  apply BSetProps.equal_refl.
Defined.

Axiom ConjunctionIntro : forall (c : C) (s1 s2 : S'),
    Implements c s1 -> Implements c s2 -> Implements c (Conjunction s1 s2).

(* This is an example from the Isola paper.
   Originally proven by @hedengran, re-proven in Coq. *)
Lemma PaperExample :
  forall (a a1 a2 g1 g2 g: S')
         (c1 c2 : C),
    Assertional a
 -> Refines a a1
 -> Refines (Conjunction a g1) (a2)
 -> Refines g2 g
 -> Implements c1 (Contract a1 g1)
 -> Implements c2 (Contract a2 g2)
 -> Implements (Composition c1 c2) (Contract a g).
Proof.
  intros.
  assert (sg : forall (q0 : C),
    Implements q0 a -> (Implements (Composition (Composition q0 c1) c2)) g).
  { intros.
    apply (@ImplementsComposable2 q0 c1 a) in H5. 2 : {assumption. }
    remember H5 as H5'. clear HeqH5'.
    apply (@ImplementRefines (Composition q0 c1) a a1) in H5. 2 : {assumption. }
    apply (@ImplementsComposable1 q0 c1 a1) in H5.
    apply (@ContractElim q0 c1 a1 g1) in H5. 2 : {assumption. }
    assert(H6: (q0 × c1) <| (a ⊓ g1)).
    { apply (@ConjunctionIntro  (Composition q0 c1) a g1  H5' H5). }
    apply (@ImplementRefines
             (Composition q0 c1) (Conjunction a g1) a2 ) in H6. 2 : {assumption. }
    apply (@ContractElim (Composition q0 c1) c2  a2 g2 ) in H6. 2 : {assumption. }
    apply (@ImplementRefines _ g2 g) in H6. 2 : {assumption. }
    exact H6.
    }
  apply ContractIntro. {exact c1. }
                       intros.
  rewrite <- CompAssoc.
  apply (sg q1 H5).
Defined.


Axiom Prop2: forall (A G : S') (X : VSet.t), InExpr G X -> Refines A (I X) -> InExpr (A,, G) X.

Axiom Prop3 : forall (Q : S') (X: VSet.t),
    InExpr Q X -> Refines ((I (X)) ⊓ Q |||| (Receptiveness X)) Q.

(* It's Prop6 in Isola *)
Axiom Prop6: forall (s1 s2 : S'), Refines (Conjunction s1 s2) (Parallel s1 s2).

Axiom Prop9 : forall (x y : VSet.t),
  Refines (Parallel (I x) (I y))
          (I (VSet.union x y)).

Axiom Prop10 : forall (x y : VSet.t), VSet.Subset x y -> Refines (I x) (I y).

Axiom Prop11 : forall (x : VSet.t),  Refines (R x) Copyright.

Axiom Prop12 : forall (x y : VSet.t), VSet.Equal (VSet.inter x y) (VSet.empty)
                                    -> Refines (I x) (Receptiveness y).

Axiom Prop13 : forall (uu : (sig IsUniverseV)) (x y : VSet.t),
  Refines (Conjunction (I x) (Receptiveness y))
          (Receptiveness (VSet.union y (@VComplement uu x ))).

Axiom Prop14 : forall (x y : VSet.t), VSet.Subset x y -> Refines (R y) (R x).

Axiom Prop18 : forall (v : VSet.t) (s : S'),  InExpr s v <-> s ⊓ © ∈ v.

Axiom Prop19: forall (s : S') ( x y : VSet.t),
                     InExpr s x -> VSet.Subset x y -> InExpr s y.


Axiom Lemma3 : forall (x1 x2 y : VSet.t),
  VSet.Subset (VSet.inter x1 x2) y ->
  Refines (
    (Parallel (Conjunction (I x1) Copyright )
                  (Conjunction (I x2) (Receptiveness y))))
  (Receptiveness (VSet.diff y x1)).

Axiom Lemma4 : forall (x y : VSet.t),
  VSet.Subset y x ->
    Refines (Parallel
      (Conjunction (I (x)) (Receptiveness y) )
      ((Receptiveness x)))
            (Receptiveness y).

Parameter ExprInv : forall (s : S') (x y : VSet.t),
    InExpr s x -> VSet.Subset x y -> InExpr s y.

Parameter InExprTrans : forall (s : S') (v1 v2 : VSet.t),
    InExpr s v1 -> VSet.subset v1 v2 -> InExpr s v2.

Lemma RefinesConj1Left' : forall (s1 s2 s3 : S'),
    Refines s1 s2 -> Refines (Conjunction s1 s3) (Conjunction s2 s3).
Proof.
  intros.
  rewrite BSet2Props.inter_sym.
  assert (eq : BSet2.Equal (s2 ∩ s3) (s3 ∩ s2)).
  { apply BSet2Props.inter_sym. }
  rewrite eq.
  apply BSet2Props.inter_subset_3.
  { apply BSet2Props.inter_subset_1. }
  rewrite BSet2Props.subset_trans.
  - apply H.
  - apply BSet2Props.inter_subset_2.
  - apply BSet2Props.subset_refl.
Defined.

(* TODO rename the other refinesConj or refactor it to use this one. *)
Lemma RefinesConj' : forall [s1 s2 : S'] (s3 : S'),
    Refines s2 s3 -> Refines (s1 ⊓ s2) (s1 ⊓ s3).
Proof.
  intros.
  apply BSet2Props.inter_subset_3.
  { apply BSet2Props.inter_subset_1. }
  rewrite BSet2Props.subset_trans.
  - apply H.
  - apply BSet2Props.inter_subset_2.
  - apply BSet2Props.subset_refl.
Defined.

Definition RefinesConj1' := RefinesConj'.


Lemma RefinesConj : forall (c1 : C) (s1 s2 s3 : S'),
    Implements c1 (Conjunction s1 s2) -> Refines s2 s3 -> Implements c1 (Conjunction s1 s3).
Proof.
  
  intros c s1 s2 s3.
  intros c_in_s1s2 s2_ref_s3.
  refine (BSet2Props.in_subset _ _ ).
  - apply c_in_s1s2.
  - apply RefinesConj'; assumption.
Defined.

Lemma RefinesCompIntro : forall (c1 : C) (s1 s2 : S'),
    Implements c1 s1 -> Refines s1 s2 -> Implements c1 (Conjunction s1 s2).
Proof.
  intros c s1 s2 s3 s1_refines_s2.
  apply BSet2Props.inter_subset_equal; assumption.
Defined.

Axiom Lemma s_ext : forall (s1 s2 : S'), BSet2.Equal s1 s2 -> s1 = s2.

Lemma ConjAssoc : forall (s1 s2 s3: S'),
    (Conjunction s1 (Conjunction s2 s3)) = (Conjunction (Conjunction s1 s2) s3).
Proof.
  intros.
  apply s_ext.
  rewrite BSet2Props.inter_assoc.
  apply BSet2Props.equal_refl.
Defined.

Lemma ConjComm : forall (s1 s2 : S'), (Conjunction s1 s2) = (Conjunction s2 s1).
Proof.
  intros.
  apply s_ext.
  rewrite BSet2Props.inter_sym.
  apply BSet2Props.equal_refl.
Defined.

(* These long-named properties should probably have the names RefinesConj left/right,
   but those were perhaps erroneously used above. TODO rename? *)
Lemma RefinesConjElimL : forall (s1 s2 : S'),  Refines (Conjunction s1 s2) s1.
Proof.
  intros.
  apply BSet2Props.inter_subset_1.
Defined.

Lemma RefinesConjElimR : forall (s1 s2 : S'),  Refines (Conjunction s1 s2) s2.
Proof.
  apply BSet2Props.inter_subset_2.
Defined.


Lemma RefinesTrans (s1 s2 s3 : S') : Refines s1 s2 -> Refines s2 s3 -> Refines s1 s3.
Proof.
  apply BSet2Props.subset_trans.
Defined.

Lemma ParallelComm : forall (s1 s2 : S'), BSet2.Equal (Parallel s1 s2) (Parallel s2 s1).
Proof.
  intros.
  unfold Parallel.
  rewrite BSet2Facts.equal_iff.
  try D.fsetdec.
  try setoid_rewrite ssr.ssrbool.andbC.
  replace (fun x : BSet.t => BSet2.mem x s1 && BSet2.mem x s2)
    with (fun x : BSet.t => BSet2.mem x s2 && BSet2.mem x s1).
  {rewrite <- BSet2Facts.equal_iff. apply BSet2Props.equal_refl. }
  apply functional_extensionality; intros.
  apply ssr.ssrbool.andbC.
Defined.


Lemma ParallelAssoc : forall (s1 s2 s3 : S'),
    BSet2.Equal (Parallel s1 (Parallel s2 s3)) (Parallel (Parallel s1 s2) s3).
Proof.
  intros.
  unfold Parallel.
  rewrite BSet2Facts.equal_iff.
  try D.fsetdec.
  try setoid_rewrite ssr.ssrbool.andbC.
  replace ((fun x : BSet.t =>
        BSet2.mem x s1 &&
        BSet2.mem x (B2filter (fun x0 : BSet.t => BSet2.mem x0 s2 && BSet2.mem x0 s3) UniverseB)))
    with (fun x : BSet.t =>
        BSet2.mem x (B2filter (fun x0 : BSet.t => BSet2.mem x0 s1 && BSet2.mem x0 s2) UniverseB) &&
        BSet2.mem x s3).
  {rewrite <- BSet2Facts.equal_iff. apply BSet2Props.equal_refl. }
  apply functional_extensionality; intros.
  try rewrite BSet2Facts.filter_b.
  try rewrite ssr.ssrbool.andbA.
  (* Try using the canonical MSet filter that has useful equalities proven. *)
Admitted.

Lemma SelfConj : forall (s : S'), BSet2.Equal (Conjunction s s) s.
Proof.
  intros.
  apply BSet2Props.inter_subset_equal.
  apply BSet2Props.subset_refl.
Defined.



(* Th. 1 From Isola. The original paper reasons over c_1, ... , c_n.
   We state a few cases explicitly. *)
Axiom Theorem1 : forall (c1 c2 : C), forall (s1 s2 s : S'), Implements c1 s1 -> Implements c2 s2 ->
                 Implements (Composition c1 c2) s -> Refines (Parallel s1 s2) (Conjunction s1 s2).

(* The following two axiomata are unsatisfying as they should follow eaiser from Theorem1 -
   for the moment, state them explicitly. *)
Axiom Theorem1_3x : forall (c1 c2 c3: C),
    forall (s1 s2 s3 s : S'), Implements c1 s1 -> Implements c2 s2 ->
                 Implements c3 s3 -> Implements (Composition c1 (Composition c2 c3)) s ->
                 Refines (Parallel s1 (Parallel s2 s3)) (Conjunction s1 (Conjunction s2 s3)).


Axiom Theorem1_4x : forall (c1 c2 c3 c4: C), forall (s1 s2 s3 s4 s : S'),
      Implements c1 s1 -> Implements c2 s2 -> Implements c3 s3 -> Implements c4 s4
    -> Implements (Composition c1 (Composition c2 (Composition c3 c4))) s
    -> Refines (Parallel s1 (Parallel s2 (Parallel s3 s4)))
               (Conjunction s1 (Conjunction s2 (Conjunction s3 s4))).



Axiom ConjRefinesParallel : forall (s1 s2 : S'), Refines (Conjunction s1 s2) (Parallel s1 s2).

(* These are not fully satisfactory. We would like them to follow from the
   above general form. *)
Axiom ConjRefinesParallel3x : forall (s1 s2 s3 : S'), Refines
                              (Conjunction s1 (Conjunction s2 s3))
                              (Parallel s1 (Parallel s2 s3)).
Axiom ConjRefinesParallel4x : forall (s1 s2 s3 s4: S'), Refines
                              (Conjunction s1 (Conjunction s2 (Conjunction s3 s4)))
                              (Parallel s1 (Parallel s2 (Parallel s3 s4))).


(* Require Import Coq.Lists.List.
Require Import List. *) (*TODO remove these if possible*)

(* As always, it is not satisfying to repeat essentially the same proofs and
   procedures for such similar constructs - TODO? give these procedures
   on the level of MSets instead of V/BSets. *)
Fixpoint ListToSetV  (lst : list VSet.elt) {struct lst} : VSet.t.
Proof.
  exact (match lst with
  | nil => VSet.empty
  | hd :: tl  => VSet.add hd (ListToSetV tl)
  end  ).
Defined.

Fixpoint ListToSetB2  (lst : list BSet2.elt) {struct lst} : BSet2.t.
Proof.
  exact (match lst with
  | nil => BSet2.empty
  | hd :: tl  => BSet2.add hd (ListToSetB2 tl)
  end  ).
Defined.

Require Import Coq.MSets.MSetDecide.
Module BSet2SDec := MSetDecide.WDecide BSet2.


(* Open Scope list_scope.  *)

Section LampProof.

Variable Lamp Gap Bat Sens : C.
Variable LampA LampG : S'.
Variable GapA  GapG  : S'.
Variable BatA BatG   : S'.
Variable SensA SensG : S'.
Variable LampS GapS BatS SensS : S'.


Local Definition vb := 1%nat.
Local Definition ib := 2%nat.
Local Definition l  := 3%nat.
Local Definition o  := 4%nat.
Local Definition ls := 5%nat.
Local Definition z  := 6%nat.


(* We create a universe out of these 6 variables .
   Using this definition outside of this example will
   introduce contradictions. One possible alternative is
   to create a dependent type for sets that additionally
   asserts that all sets are subsets of the universe.   *)
Local Definition E1UU_els := ListToSetV [vb ; ib ; l ; o ; ls ; z].

(* This is certainly only true for this section *)
Local Parameter IsUniverseE1 : IsUniverseV E1UU_els.

Local Definition E1UU := MkUniverseV IsUniverseE1.


Definition set1 := ListToSetV  [vb ; ib ; l].
Definition set2 := ListToSetV  [l].
Definition set3 := ListToSetV  [vb ; ib ; l; o].
Definition set4 := ListToSetV  [l ; o].
Definition set5 := ListToSetV  [l ; o ; ls].
Definition set6 := ListToSetV  [vb ; ib].
Definition set7 := ListToSetV  [o].

Lemma VSetEqRefl : forall (x : VSet.t), VSet.Equal x x.
Proof.
  intros.
  apply VSetProps.equal_refl.
Defined.

Lemma VSeteqRefl : forall (x : VSet.t), VSet.equal x x.
Proof.
  intros.
  apply VSetFacts.equal_iff.
  apply VSetEqRefl.
Defined.

Lemma VSetInter1 : forall (x : VSet.t), VSet.equal (VSet.inter x x) x.
Proof.
  intros x.
  rewrite VSetProps.inter_subset_equal.
  { apply VSetFacts.equal_iff. apply VSetProps.equal_refl. }
  apply VSetProps.subset_refl.
Defined.

Lemma BSet2SubsetInterRight  : forall (x y: BSet2.t), BSet2.Subset (BSet2.inter x y) x.
Proof. apply BSet2Props.inter_subset_1. Defined.

Lemma BSet2SubsetInterLeft   : forall (x y: BSet2.t), BSet2.Subset (BSet2.inter y x) x.
Proof. intros. apply BSet2Props.inter_subset_2. Defined.

Definition ParallelIntro (c1 c2 : C) (s1 s2 : S') (p1 : Implements c1 s1) (p2 : Implements c2 s2) :
  Implements (Composition c1 c2) (Parallel s1 s2).
Proof.
Admitted.

(* TODO upstream if not already stated. *)
Definition ConjElimL (c : C) (s1 s2 : S') : Implements c (Conjunction s1 s2) -> Implements c s1.
Proof. apply BSet2Facts.inter_1. Defined.

Definition ConjElimR (c : C) (s1 s2 : S') : Implements c (Conjunction s1 s2) -> Implements c s2.
Proof. apply BSet2Facts.inter_2. Defined.

Definition lsv := ListToSetV. (* An even terser approachis defining
                                 a list notation [] in terms of lsv already*)

Parameter assume1 : Implements Lamp (I set1).
Parameter assume2 : Implements Lamp (LampA ⊓ (Receptiveness set2) ⊓ Copyright ,, (LampG ⊓ Copyright) ).
Parameter assume3 : Implements Gap (Receptiveness set4).
Parameter assume4 : Implements Gap (I set5).

Parameter Assumption25 : InExpr LampG set2.

Parameter AssumptionUN0 : Implements Gap GapS.

Definition GoalS := Contract ((Conjunction (Conjunction LampA (Receptiveness set2)) (I set1))) LampG.

(* (X)S are all assertional *)
Axiom Assumption24A : Assertional BatS.
Axiom Assumption24B : Assertional LampS.
Axiom Assumption24C : Assertional GapS.
Axiom Assumption24D : Assertional SensS.

Parameter Specification19 : Implements Lamp
  (Conjunction (Contract (Conjunction LampA (R set2)) (LampG)) (I ( set1))).

Parameter Specification20 : Implements Bat ( Conjunction BatS (I (set6))).

Definition Specification21 := Conjunction GapS (Conjunction (I (set5)) (R (set4))).

Definition Specification22:= Conjunction SensS (Conjunction (I (lsv [ls ; z ]))  (R (lsv [ls]))).

Parameter Assumption21 : Implements Gap Specification21.

Parameter Assumption21' : Implements Gap GapS.

Parameter Assumption28 : Refines BatS LampA.

Parameter assumeun5 : Implements Bat (I (lsv [vb ; ib])).

Parameter Assumption24E : Assertional LampG.

Definition Sys := (Composition Bat (Composition Lamp (Composition Gap Sens))).
Parameter SysS : S'.

Parameter Spec22 : Implements Sens (Conjunction SensS
                                               (Conjunction (I (lsv [ls ; z ]))
                                                            (R ( lsv [ls ])))).


Parameter AssumptionUN1 : Implements Sens SensS.

Parameter Assumption27: Refines (Parallel LampG (Parallel GapS (SensS))) SysS.

Parameter CompImpSpecLamp : Implements Lamp LampS.
Parameter CompImpSpecGap : Implements Gap GapS.
Parameter CompImpSpecBat : Implements Bat BatS.
Parameter CompImpSpecSens : Implements Sens SensS.


Definition Specification18 :=  (Conjunction SysS (Conjunction (R (lsv [ o ] )) Copyright )).

Definition SysTotal := Specification18.


Definition LampTotal := Conjunction
                          (Conjunction LampA (R (lsv [l ])) ,, LampG)
                          (I (lsv [ vb ;ib ; l])).
Definition BatTotal  := Conjunction BatS ((I (lsv [l ; o ; ls ]))).
Definition GapTotal  := Conjunction GapS (Conjunction (I (lsv [ l ; o ; ls]))
                                                      (R (lsv [l ; o]))).
Definition SensTotal := Conjunction SensS (Conjunction (I (lsv [ls ; z ]))
                                                       (R (lsv [ls]))).

Parameter GapByTotal: Implements Gap GapTotal.
Parameter LampByTotal: Implements Lamp LampTotal.
Parameter SensByTotal: Implements Sens SensTotal.
Parameter BatByTotal: Implements Bat BatTotal.


(* Now follows the proofs.
   There are stylistic improvements possible, by taking a more idiomatic approach to the
   proofs - top down instead of bottoms up, that is, not proving multiple intermediate
   properties using asserts but decomposing the final goal with refines would render
   more readable proofs. *)
Lemma Sublemma1 : Implements (Composition  Lamp Gap) GoalS.
Proof.
  assert (L29 : Refines
         (Contract (Conjunction (Conjunction LampA (Receptiveness set2)) ©) (LampG))
         (((LampA ∩ R set2) ∩ (I set1) ∩ Copyright ),, (LampG ))).
  { unfold GoalS.
    set (l := (LampA ∩ R set2  ∩ Copyright),, (LampG)).
    set (r := (((LampA ∩ R set2) ∩ (I set1)  ∩ Copyright),, (LampG))).
    assert (subg : (Refines l r)).
    { apply Prop7.
      - apply RefinesConj1Left'.
        apply BSet2SubsetInterRight.
      - unfold Refines.
        Check (BSet2.subset LampG LampG).
        Check (BSet2.subset LampG LampG = true).
        simpl.
        try apply BSet2Props.subset_refl.
    }
    simpl in subg.
    apply subg.
  }
  assert (UN1 : Refines
                  ((Conjunction (Conjunction LampA (Receptiveness set2)) (I set1)))
                  ((I set1))).
  { apply BSet2SubsetInterLeft . }
  assert (UN2 : InExpr LampG set1).
  { refine (Prop19 _ _).
    - apply Assumption25.
    - rewrite VSetFacts.subset_iff. D.fsetdec. }
  assert (UN3 : InExpr GoalS set1).
  { refine (Prop2 _ _ ).
    {assumption. }
    refine ( RefinesTrans _ _ ).
    - apply UN1.
    - apply Prop10; rewrite VSetFacts.subset_iff; D.fsetdec.
  }
  assert (UN4: Implements Gap (R (lsv [vb ; ib ; l ; o]))).
  { refine (ImplementRefines _ _ ).
    - apply (ConjunctionIntro assume3 assume4).
    - assert (intm1 : VSet.Equal
                        (@VComplement E1UU (ListToSetV [l; o; ls]))
                        (ListToSetV [vb ; ib; z])).
      {  rewrite VSetFacts.equal_iff. D.fsetdec. }
      assert (intm1' : (VSet.equal
                          (@VComplement E1UU (ListToSetV [l; o; ls]))
                          (ListToSetV [vb ; ib; z]))).
      { D.fsetdec. }
      assert (intm2' : (VSet.Equal
                          (VSet.union (ListToSetV [l; o]) (ListToSetV [vb ; ib; z]))
                          (ListToSetV [vb;ib;l;o;z]))).
      { rewrite VSetFacts.equal_iff. D.fsetdec. }
      refine (RefinesTrans _ _ ).
      + rewrite ConjComm.
        unfold Refines.
        set (p := Prop13).
        apply p.
      + refine (RefinesTrans _ _).
        * unfold set4, set5.
          apply Prop14.
          apply VSetProps.subset_equal.
          rewrite intm1.
          rewrite intm2'.
          assert (sub: VSet.Subset
                         (ListToSetV [vb; ib; l; o])
                         (ListToSetV [vb; ib; l; o; z])).
          {rewrite VSetFacts.subset_iff. D.fsetdec. }
          apply VSetProps.equal_refl.
        * apply Prop14.
          apply VSetFacts.subset_iff.
          D.fsetdec.
  }
  assert (Text : Implements Gap (GapA,, GapG)
                 -> Implements Gap (Receptiveness set3 )
                 -> Implements Gap (Receptiveness set1)).
  { intros imp1 imp2.
    apply (ImplementRefines imp2).
    apply Prop14.
    rewrite VSetFacts.subset_iff.
    D.fsetdec.
  }
  assert (UN5 : InExpr
                  ((LampA ⊓ (Receptiveness set2) ⊓ (I ( set1 ))  ⊓ Copyright ,, (LampG)))
                  set1).
  {  refine (Prop2 _ _ ).
     - unfold set1.
       assumption.
     - rewrite ConjComm. rewrite ConjAssoc. apply RefinesConjElimR.
  }
  assert (lxg : Implements (Composition Lamp Gap )
                           (LampA  ⊓ (Receptiveness set2)
                         ⊓ (I (set1 )) ⊓ Copyright ,, LampG)).
  { simpl.
    set (a := assume1).
    set (b := assume2).
    assert (b' : Lamp <| (((LampA ∩ R set2) ∩ ©),, (LampG))).
    { refine (ImplementRefines _ _).
      - apply b.
      - apply Prop7.
        + apply BSet2Props.subset_refl.
        + apply RefinesConjElimL.
    }
    assert (UN6 : Implements Gap (R (lsv [ vb ; ib ; l]))).
    { refine (ImplementRefines _ _).
      - apply UN4.
      - apply Prop14. rewrite VSetFacts.subset_iff. D.fsetdec.
    }
    set (f := Specification19).
    set (g := ParallelIntro).
    rewrite ConjComm in f.
    assert (tt1' : Implements Lamp
      (((LampA ∩ R (ListToSetV [l]))∩ (I (ListToSetV [vb; ib; l])) ∩ Copyright ),, LampG)).
    { refine (ImplementRefines _ _).
      - refine (ImplementRefines _ _).
        + exact b'.
        + apply L29.
      - apply BSet2Props.subset_refl.
    }
    refine (ImplementRefines _ _).
    Focus 2.
    - apply Prop3.
      + apply UN5.
      + apply ParallelIntro; try assumption.
        apply ConjunctionIntro.
        {assumption. }
        refine (ImplementRefines _ _).
        {apply b'. }
        apply L29.
  }
  refine (ImplementRefines _ _).
  Focus 2.
  - refine (Prop7 _ _).
    + rewrite ConjComm.
      rewrite ConjAssoc.
      rewrite ConjComm.
      rewrite <- (SelfConj (R set2)).
      rewrite <- ConjAssoc.
      refine (RefinesConj1Left' _ ).
      apply Prop11.
      rewrite ConjComm.
      replace (R set2 ∩ ((I set1) ∩ LampA))
        with ((LampA ∩ R set2) ∩ (I set1)).
      2: {  rewrite <- ConjAssoc.
            rewrite ConjComm.
            repeat rewrite ConjAssoc.
            reflexivity.
      }
      apply lxg.
      apply BSet2Props.subset_refl.
Defined.


Lemma Subproof2 : Implements (Composition Lamp Gap) GapS.
Proof.
  rewrite CompComm. (* Rename to CompositionComm ... *)
  apply AssertionalEx.
  - exact Assumption24C.
  - apply (ConjElimL Assumption21).
Defined.

(* Probably only need Prop10 and not this. *)
Axiom I_ext : forall (v1 v2 : VSet.t) (f : VSet.t -> BSet2.t),
    VSet.Equal v1 v2 -> BSet2.Equal (f v1) (f v2).

Lemma Subproof3 : Implements
                    (Composition Lamp Gap)
                    (I (( ListToSetV [vb ; ib ; l ; o ; ls ]))).
Proof.
  unfold E1UU.
  assert (part1 : Implements Lamp (I set1)).
  { apply (ConjElimR Specification19). }
  assert (part2 : Implements Gap (I set5)).
  { apply (ConjElimL (ConjElimR Assumption21)). }
  assert (part3 : Refines (Parallel (I set1) (I set5))
                          (I (lsv [vb ; ib ; l ; o ; ls]))).
  { refine (RefinesTrans _ _).
    { apply Prop9.  }
    rewrite  BSet2Props.subset_equal.
    assert (subg : BSet2.Equal
                     (I (lsv [vb; ib; l; o; ls]))
                     (I (VSet.union (set1) (set5)))).
    { apply I_ext. rewrite VSetFacts.equal_iff. D.fsetdec. }
    apply BSet2Props.subset_equal. apply BSet2Props.equal_sym. apply subg.
    apply BSet2Props.equal_refl.
  }
  set (parall := (ParallelIntro part1 part2)).
  apply (ImplementRefines parall); assumption.
Defined.

Lemma Subproof4tt : Implements Bat (Conjunction LampA
                                                (Conjunction (R (lsv [l]))
                                                             (I (lsv [vb ; ib ])))).
Proof.
  assert (tx : Implements Bat (Conjunction (I (lsv [vb; ib])) BatS)).
  { rewrite ConjComm.
    refine Specification20.
  }
  assert (t2 : Refines (I ( lsv [vb ; ib])) (R (lsv [l ]))).
  { apply Prop12.
    rewrite VSetFacts.equal_iff.
    D.fsetdec. }
  assert (t3 : Refines BatS LampA). { apply Assumption28. }
  assert (tt :  Bat <| (I (lsv [vb; ib]) ⊓ LampA) ).
  { refine (RefinesConj _ t3 ). apply tx. }
  rewrite ConjAssoc.
    rewrite ConjComm.
    rewrite ConjAssoc.
    apply RefinesCompIntro.
    {assumption. }
    refine (RefinesTrans _ _).
    - apply RefinesConjElimL.
    - assumption.
Defined.


Lemma Subproof4 :
  Implements
    (Composition (Composition Bat Lamp) Gap)
    (Conjunction LampG GapS).
Proof.
  assert (tx : Implements Bat (Conjunction (I ( lsv [vb; ib] )) BatS)).
  { rewrite ConjComm.
    refine Specification20.
  }
  assert (t2 : Refines (I ( lsv [vb ; ib] )) (R (lsv [l] ))).
  { apply Prop12.
    rewrite VSetFacts.equal_iff.
    D.fsetdec. }
  assert (t3 : Refines BatS LampA). { apply Assumption28. }
  assert (tt : Bat <| (I (lsv [vb; ib]) ⊓ LampA)).
  { refine (RefinesConj _ t3 ). apply tx. }
  assert (t4 : Implements Bat (Conjunction LampA
                                          (Conjunction (R (lsv [l]))
                                                       (I ( lsv [vb ; ib ] ))))).
  { apply Subproof4tt. }
  assert (t5 : Refines (I (lsv [vb ; ib ])) (I (lsv [ vb ; ib ; l ]))).
  { apply Prop10. rewrite VSetFacts.subset_iff. D.fsetdec. }
  assert (t6 : Implements Bat (Conjunction LampA (Conjunction (R (lsv [l]))
                                                 (I ( lsv [vb ; ib ; l]))))).
  { rewrite ConjAssoc. rewrite ConjComm.
    refine (ConjunctionIntro _ _).
    - refine (ImplementRefines _ _).
      + exact (ConjElimL tt).
      + apply Prop10. rewrite VSetFacts.subset_iff. D.fsetdec.
    - apply (ImplementRefines t4).
      rewrite ConjAssoc.
      apply (RefinesConjElimL).
  }
  assert (t7 : Implements (Composition Bat (Composition Lamp Gap)) LampG).
  { refine (ContractElim _ _ _).
    - apply t4.
    - refine (ImplementRefines _ _).
      + apply Sublemma1.
      + refine (Prop7 _ _ ).
        2: { apply BSet2Props.subset_refl. }
        simpl.
        rewrite ConjAssoc.
        rewrite ConjComm.
        rewrite ConjComm.
        apply RefinesConj'.
        apply Prop10.
        unfold set1.
        rewrite VSetFacts.subset_iff.
        D.fsetdec.
  }
  set (tt1 := Assumption24C) .
  set (tt2 := Subproof2).
  Print AssertionalEx.
  assert (t8 : Implements (Composition Bat (Composition Lamp Gap)) GapS).
  { rewrite CompComm. apply AssertionalEx; assumption. }
  rewrite CompAssoc.
  apply ConjunctionIntro; assumption.
Defined.


Lemma Subproof5: Implements (Composition Bat (Composition Lamp Gap))
                            (I (ListToSetV [vb ; ib ; l ; o ; ls ])).
Proof.
  assert (veq : VSet.Equal (VSet.union set1 set5) (ListToSetV [vb ; ib ; l ; o ; ls ])).
  { rewrite VSetFacts.equal_iff. D.fsetdec. }
  refine ( BSet2Props.in_subset _ _).
  2: {apply Prop10.  apply VSetProps.subset_equal. apply veq. }
  assert(eq: VSet.Equal (VSet.union  set1 set5) (lsv ([vb ; ib ;l ; o ; ls] ))).
  { rewrite VSetFacts.equal_iff. D.fsetdec. }
  refine (ImplementRefines _ _ ).
  - refine (ParallelIntro _ _ ).
    + apply (ConjElimR Specification20).
    + apply Subproof3.
  - refine (RefinesTrans _ _).
    + rewrite BSet2Props.subset_equal.
      2: { apply ParallelComm. }
      apply Prop9.
    + apply Prop10.
      rewrite VSetFacts.subset_iff.
      D.fsetdec.
Defined.


Lemma Subproof6: Implements (Composition Bat (Composition Lamp Gap)) (R (lsv [o])).
Proof.
  assert (x: Implements Bat (Conjunction LampA (Conjunction (R (lsv [l]))
                                        (Conjunction (I (lsv [vb ; ib ; l])) Copyright)))).
  { set (p := Subproof4tt).
    rewrite ConjComm.
    rewrite ConjComm in p.
    assert (tt1 : Bat <| ((R (lsv [l]) ⊓  (R (lsv [l]) ⊓ (I (lsv [vb; ib]))) ⊓ LampA))).
    { rewrite <- ConjAssoc.
      rewrite <- ConjAssoc.
      refine (ImplementRefines _ _).
      - apply Subproof4tt.
      - rewrite ConjComm.
        rewrite <- ConjAssoc.
        apply BSet2Props.subset_equal.
        repeat rewrite <- ConjAssoc.
        assert (eq : BSet2.Equal ((R (lsv [l])) ∩ (R (lsv [l]))) (R (lsv [l]))).
        { rewrite SelfConj. apply BSet2Props.equal_refl. }
        assert (eq' : BSet2.Equal (R (lsv [l]) ∩ (R (lsv [l]) ∩ (I (lsv [vb; ib]) ∩ LampA)))
                      ((R (lsv [l]) ∩ (R (lsv [l]))) ∩ (I (lsv [vb; ib]) ∩ LampA))).
        { rewrite ConjAssoc. apply BSet2Props.equal_refl. }
        rewrite eq'.
        rewrite eq.
        apply BSet2Props.equal_refl.
   }
    repeat rewrite <- ConjAssoc.
    rewrite ConjComm.
    do 2 rewrite <- ConjAssoc.
    rewrite ConjComm.
    repeat rewrite <- ConjAssoc.
    refine (ImplementRefines _ _).
    - apply tt1.
    - rewrite ConjAssoc at 1.
      refine (RefinesTrans _ _).
      + repeat rewrite <- ConjAssoc. apply RefinesConj1'.
        apply BSet2Props.subset_refl.
      + refine (RefinesTrans _ _ ).
        * rewrite ConjAssoc. rewrite ConjComm.
          repeat rewrite <- ConjAssoc.
          apply RefinesConj1Left'.
          refine (Prop10 _ ).
          assert (sub : VSet.Subset (lsv [vb; ib]) (lsv [vb; ib; l])).
          { rewrite VSetFacts.subset_iff. D.fsetdec. }
          apply sub.
        * rewrite ConjComm.
          rewrite <- ConjAssoc.
          rewrite ConjComm.
          assert (eq : BSet2.Equal (LampA ∩ (R (lsv [l]) ∩ (I (lsv [vb; ib; l]))))
           (R (lsv [l]) ∩ (I (lsv [vb; ib; l]) ∩ LampA))).
          {repeat rewrite <- ConjAssoc.
           rewrite ConjComm.
           repeat rewrite ConjAssoc.
           apply BSet2Props.equal_refl.
          }
          rewrite eq.
          do 2 rewrite  ConjAssoc.
          rewrite ConjComm.
          assert (eq' : BSet2.Equal (Conjunction Copyright (R (lsv [l]))) (R (lsv [l]))).
          { rewrite ConjComm. rewrite BSet2Props.inter_subset_equal.
            - apply BSet2Props.equal_refl.
            - apply Prop11.
          }
          rewrite eq'.
          rewrite ConjComm.
          repeat rewrite <- ConjAssoc.
          assert (eq'' : BSet2.Equal (R (lsv [l]) ∩ (R (lsv [l]))) (R (lsv [l]))).
          { rewrite SelfConj. apply BSet2Props.equal_refl. }
          rewrite ConjAssoc.
          rewrite eq''.
          repeat rewrite <- ConjAssoc.
          apply BSet2Props.subset_refl.
  }
  assert (t1: Implements Bat (Conjunction LampA ( Conjunction (R ( lsv [l ] ) ) Copyright ))).
  { rewrite ConjComm in x at 1.
    rewrite <- ConjAssoc in x.
    rewrite ConjComm in x.
    repeat rewrite <- ConjAssoc in x.
    set (y := ConjElimR x).
    rewrite ConjAssoc.
    rewrite ConjComm.
    apply y.
  }
  assert (t2: Implements Lamp
                         (Contract (Conjunction LampA (Conjunction (R ( lsv [l ])) Copyright ))
                                   (Conjunction LampG Copyright) ) ).
  { set (z := assume2).
    rewrite ConjAssoc.
    apply assume2.
  }
  assert (t3 : Implements (Composition Bat Lamp) (Conjunction LampG Copyright)).
  { refine (ContractElim _ _ _).
    - apply t1.
    - exact t2.   }
  assert (t4: Implements (Composition Bat Lamp) Copyright).
  { refine (ConjElimR _ ).
    exact t3. }
  assert (t5 : Implements Bat (I (lsv [vb ; ib ]))).
  { apply assumeun5. }
  assert (t6: Implements Lamp (I ( lsv [vb ; ib ; l ]))).
  { apply assume1.  }
  assert (t7: Implements (Composition Bat Lamp) (I ( lsv [vb ; ib ; l ]))). {
  set (z := ParallelIntro).
  set (w := Prop9 ).
  assert (eq :  VSet.Equal (lsv [vb; ib; l]) (VSet.union (lsv [vb ; ib]) (lsv [vb ; ib ; l] ))).
  { rewrite VSetFacts.equal_iff. D.fsetdec. }
  refine (ImplementRefines _ _).
  - refine (ParallelIntro _ _).
    + exact t5.
    + exact t6.
  - assert (eq' : BSet2.Equal (I (lsv [vb; ib; l]))
                              (I (VSet.union (lsv [vb; ib]) (lsv [vb; ib; l])))).
    { apply BSet2Props.double_inclusion.
      split.
      - apply Prop10.
        rewrite VSetFacts.subset_iff.
        D.fsetdec.
      - apply Prop10.
        rewrite VSetFacts.subset_iff.
        D.fsetdec.
    }
    rewrite BSet2Props.subset_trans.
    + apply BSet2Props.subset_equal.
      rewrite eq'.
      apply BSet2Props.equal_refl.
    + apply BSet2Props.subset_refl.
    + apply Prop9.
  }
  rewrite <- CompAssoc.
  rewrite CompComm.
  refine (ImplementRefines _ _).
  - refine (ParallelIntro _ _).
    + apply (ConjunctionIntro assume4 assume3).
    + apply (ConjunctionIntro t7 t4).
  - unfold set5.
    set (s := Prop9).
    set (s1 := (lsv [vb ; ib ; l])).
    set (s2 := (lsv [l ; o; ls])).
    set (s3 := (lsv [l ; o])).
    set (s4 := (lsv [o])).
    assert (e1 : VSet.Subset (VSet.inter s1 s2) s3).
    { rewrite VSetFacts.subset_iff. D.fsetdec. }
    assert (e2 : (VSet.Equal (VSet.diff s3 s1))  s4).
    { rewrite VSetFacts.equal_iff. D.fsetdec. }
    assert (e3 : (BSet2.Equal (R (VSet.diff s3 s1))) (R s4)).
    { apply BSet2Props.subset_antisym.
      - apply Prop14. rewrite e2. apply VSetProps.subset_refl.
      - apply Prop14. rewrite e2. apply VSetProps.subset_refl.
    }
    set (y := @Lemma3  s1 s2 s3 e1).
    rewrite <- e3.
    assert (f : Refines (I (lsv [vb; ib; l])) (R (lsv [o]))).
    {apply Prop12.
     apply VSetFacts.equal_iff. D.fsetdec. }
    rewrite BSet2Props.subset_equal.
    2: { apply ParallelComm.  }
    assumption.
Defined.


Lemma Subproof7: Implements (Composition Bat (Composition Lamp (Composition Gap Sens )))
                            (Conjunction LampG (Conjunction GapS SensS)).
Proof.
  set (x := Subproof5).
  set (y := Spec22).
  assert (t1: Implements Sens (Conjunction (R (lsv [ls])) (I (lsv [ls ; z])))).
  { rewrite ConjComm. apply (ConjElimR y). }
  assert (t2: Implements Sens (R (lsv [vb ; ib ; l ; o ; ls] ) )).
  { refine (ImplementRefines _ _).
    - refine (ImplementRefines _ _).
      + apply t1.
      + rewrite ConjComm.
        apply Prop13.
    -  assert (eq : VSet.Equal (@VComplement E1UU (lsv [ls ; z] ))
         (lsv [vb; ib; l; o])).
       { unfold VComplement.
         simpl.
         unfold E1UU_els.
         rewrite VSetFacts.equal_iff.
         simpl. D.fsetdec. }
       assert (eq' : VSet.Equal
                       (VSet.union (lsv [ls]) (@VComplement E1UU (lsv [ls; z])))
                       (VSet.union (lsv [ls]) (lsv [vb; ib; l; o]))).
       { rewrite eq. apply VSetProps.equal_refl. }
       refine (RefinesTrans _ _).
       2: { apply Prop14.
            apply VSetProps.subset_refl.
       }
       apply Prop14.
       rewrite VSetFacts.subset_iff.
       rewrite eq'. D.fsetdec.
  }
  set (z := Assumption25).
  unfold set2 in z.
  assert (t3 : InExpr LampG ( (lsv [vb ; ib ;l ]) )).
  { refine (ExprInv _ _).
    - apply z.
    - rewrite VSetFacts.subset_iff. D.fsetdec.
  }
  assert (t4: InExpr LampG ( lsv [vb ; ib ; l ; o ; ls])).
  { apply (Prop19 t3). rewrite VSetFacts.subset_iff. D.fsetdec. }
  set (w := Subproof4).
  assert (t5: Implements (Composition Bat ( Composition Lamp Gap )) LampG).
  { rewrite <- CompAssoc.
    refine (ImplementRefines _ _).
    - apply w.
    - apply BSet2Props.inter_subset_1. }
  assert (tt: Implements (Composition Bat ( Composition Lamp Gap )) GapS).
  { rewrite <- CompAssoc.
    refine (ImplementRefines _ _).
    - apply w.
    - rewrite ConjComm. apply BSet2Props.inter_subset_1. }
  assert (tt2 :  Implements
                   (Composition Bat ( Composition Lamp (Composition Gap Sens)))
                   GapS).
  { do 1 rewrite <- CompAssoc.
    rewrite CompComm.
    rewrite CompAssoc.
    apply AssertionalEx.
    - apply Assumption24C.
    - apply Assumption21'.
  }
  assert (tt3 :  Implements
                   (Composition Bat ( Composition Lamp (Composition Gap Sens)))
                   SensS).
  { rewrite CompComm.
    rewrite CompAssoc.
    rewrite CompComm.
    do 2 rewrite CompAssoc.
    rewrite CompComm.
    rewrite CompAssoc.
    apply AssertionalEx.
    - apply Assumption24D.
    - apply AssumptionUN1.
  }
  assert (t6: (forall (s : S'),
                  InExpr s (lsv ([vb ; ib ; l ; o ; ls] ))
                  -> (Refines (Parallel (Conjunction (I (lsv ([vb ; ib ; l ; o ; ls]))) s)
                     (R (lsv ([vb ; ib ; l; o; ls] )))) s))).
  { intros ?.
    apply Prop3.
  }
  assert (tt4 :  Implements
                   (Composition Bat ( Composition Lamp (Composition Gap Sens)))
                   LampG).
  { rewrite CompComm.
    rewrite CompAssoc.
    rewrite CompComm.
    do 2 rewrite CompAssoc.
    rewrite CompComm.
    rewrite CompAssoc.
    rewrite CompComm.
    apply AssertionalEx.
    - apply Assumption24E.
    - rewrite CompAssoc. apply t5.
  }
  refine ( ConjunctionIntro _ _ ).
  - assumption.
  - refine (ConjunctionIntro _ _ ); try assumption.
Defined.

Lemma Subproof8: Implements
                   (Composition Bat (Composition Lamp (Composition Gap Sens)))
                   (R (lsv [ o ])).
Proof.
  assert (t1: Implements Sens (Conjunction (R (lsv [ls])) (I (lsv [ls ; z])))).
  { rewrite ConjComm.
    refine (ConjElimR _ ).
    apply Spec22.
  }
  set (y := Prop13).
  assert (tt21: ( VSet.Equal (lsv [ls ; z] )) (@VComplement E1UU (lsv [vb; ib; l; o]))).
  { rewrite VSetFacts.equal_iff. D.fsetdec. }
  assert (tt22: (VSet.Equal (lsv [vb ; ib ; l ; o ; ls]))
                  (VSet.union (lsv [ls]) (@VComplement E1UU (lsv  [ls ; z])))).
  { rewrite VSetFacts.equal_iff; D.fsetdec. }
  assert (tt23: (BSet2.Equal (R (lsv [vb ; ib ; l ; o ; ls])))
                  (R (VSet.union (lsv [ls]) (@VComplement E1UU (lsv  [ls ; z]))))).
  { apply BSet2Props.double_inclusion.
    split.
    - rewrite BSet2Props.subset_equal; try assumption.
      + apply Prop14.
        apply VSetProps.subset_equal.
        rewrite <- tt22.
        apply VSetProps.equal_refl.
      + apply BSet2Props.equal_refl.
    - apply Prop14.
      apply VSetProps.subset_equal.
      assumption.
  }
  assert (t2: Implements Sens (R (lsv [vb ; ib ; l ; o ; ls ]))).
  { refine (ImplementRefines _ _).
    - exact t1.
    - rewrite ConjComm.
      refine ( BSet2Props.subset_trans _ _).
      + apply Prop13.
      + refine ( BSet2Props.subset_trans _ _).
        2: { apply BSet2Props.subset_equal.
             rewrite tt23.
             apply BSet2Props.equal_refl. }
        apply BSet2Props.subset_refl.
  }
  assert (t3: Implements (Composition Bat (Composition Lamp Gap))
                         (Conjunction ( I (lsv ([ vb ; ib ; l ; o ; ls])))
                                      (R (lsv [o])))).
  { apply ConjunctionIntro.
    - apply Subproof5.
    - apply Subproof6.
  }
  refine (ImplementRefines _ _).
  - do 2  rewrite <- CompAssoc.
    rewrite CompComm.
    refine (ParallelIntro _ _).
    + exact t2.
    + rewrite CompAssoc. exact t3.
  - rewrite ParallelComm.
    apply Lemma4.
    rewrite VSetFacts.subset_iff.
    D.fsetdec.
Defined.


Lemma Subproof9:
  Refines (Parallel LampTotal (Parallel BatTotal (Parallel GapTotal SensTotal)))
          SysTotal.
Proof.
  set (x := Spec22).
  set (y := Subproof8).
  assert (t1 : Implements
                 (Composition Bat (Composition Lamp (Composition Gap Sens)))
                 Copyright ).
  {refine (ImplementRefines _ _).
   - apply y.
   - apply Prop11. }
  set (z := Subproof7).
  assert (t2 : Implements  (Composition Bat (Composition Lamp (Composition Gap Sens)))
         (Conjunction LampG (Conjunction GapS(Conjunction SensS
                                             (Conjunction (R (lsv [o])) Copyright))))).
  { refine (ConjunctionIntro _ _).
    - apply (ConjElimL z).
    - refine (ConjunctionIntro _ _).
      { apply ConjElimR in z. apply ConjElimL in z. exact z. }
      refine (ConjunctionIntro _ _).
      { apply ConjElimR in z. apply ConjElimR in z. exact z. }
      refine (ConjunctionIntro _ _); try assumption.
  }
  set (a := Specification18). unfold Specification18 in a.
  set (b := Assumption27).
  unfold SysTotal, Specification18.
  Print Specification18.
  unfold SysTotal.
  set (c := Prop6).
  assert (t4 : Implements
                 (Composition Bat (Composition Lamp (Composition Gap Sens)))
                 SysS).
  {refine (ImplementRefines _ _).
   { exact z. }
   refine (RefinesTrans _ _).
   - apply  ConjRefinesParallel3x.
   -  assumption.  }
  assert (t5 : Implements
                 (Composition Bat (Composition Lamp (Composition Gap Sens)))
                 SysTotal).
  { apply ConjunctionIntro. assumption.
    apply ConjunctionIntro. assumption.
    assumption. }
  (* We can probably end here at t5? *)
  refine (RefinesTrans _ _).
  - refine (Theorem1_4x _ _ _ _ _).
    + apply LampByTotal.
    + apply BatByTotal.
    + apply GapByTotal.
    + apply SensByTotal.
    + rewrite <- CompAssoc.
      rewrite <- CompAssoc.
      assert (eq : BSet.Equal (Composition Lamp Bat)
                              (Composition Bat Lamp)).
      { apply CompComm. }
      rewrite eq.
      do 2 rewrite CompAssoc.
      apply t4.
  - rewrite ConjAssoc.
    assert (eq : BSet2.Equal (Conjunction LampTotal BatTotal)
                             (Conjunction BatTotal LampTotal)).
    {rewrite ConjComm. apply BSet2Props.equal_refl. }
    rewrite ConjAssoc.
    repeat rewrite <- ConjAssoc.
    unfold LampTotal.
    unfold BatTotal, LampTotal, GapTotal,SensTotal.
    (* The rest follows easily *)
Abort.
