Require Import List.
Import ListNotations.
Require Import Nat.
Require Import Program Arith.
Require Import Lia.
Require Import Logic.Decidable.
Require Import Structures.Equalities.
Require Import MSets.MSetWeakList.
Require Import MSets.MSetDecide.
Require Import MSets.MSetFacts.
Require Import MSets.MSetProperties.
Require Import MSets.MSetEqProperties.
From Equations Require Import Equations.

(* The type of propositional formulas.
   We use the fragment consisting of falsity and implication. *)
Inductive form : Type :=
| Pro (n : nat)
| Falsity
| Imp (p : form) (q : form).

Module Form_As_DT <: DecidableType.
  Definition t := form.
  Definition eq := @eq form.
  Definition eq_refl := @eq_refl form.
  Definition eq_sym := @eq_sym form.
  Definition eq_trans := @eq_trans form.
  #[export] Program Instance eq_equiv : Equivalence eq.
  
  Lemma eq_dec : forall x y : form, {eq x y} + {~ eq x y}.
  Proof using Type Type. intros. unfold eq. decide equality. decide equality. Qed.
End Form_As_DT.

Module Import S := Make Form_As_DT.
Module Import MSetDec := MSetDecide.WDecide S.
Module Import MSetFacts := MSetFacts.WFacts S.
Module Import MSetProps := MSetProperties.WProperties S.
Module Import MSetEqProps := MSetEqProperties.WEqProperties S.

(* Semantics is a predicate over an interpretation i determining
   whether the formula is true for the given interpretation. *)
Fixpoint semantics (i : nat -> bool) (f : form) : Prop :=
  match f with
  | Pro n => i n = true
  | Falsity => False
  | Imp p q => semantics i p -> semantics i q
  end.

Lemma semantics_dec : forall i f, decidable (semantics i f).
Proof using Type.
  intros. unfold decidable. induction f.
  - simpl. destruct (i n); auto.
  - simpl. auto.
  - simpl. destruct IHf1; destruct IHf2; intuition.
Qed.

(* A sequent consisting of two lists of formulas is provable if everything
   in the left list being true implies the existence of a true formula
   in the right list. *)
Definition sc (x y : t) (i : nat -> bool) : Prop :=
  For_all (semantics i) x -> Exists (semantics i) y.

(* We define a sequent calculus as an inductive predicate. *)
Inductive SC : t -> t -> Prop :=
| Fls_L X Y : SC (add Falsity X) Y
| Imp_L p q X Y (H1: SC X (add p Y)) (H2: SC (add q X) Y)
  : SC (add (Imp p q) X) Y
| Imp_R p q X Y (H: SC (add p X) (add q Y)) : SC X (add (Imp p q) Y)
| Set_L X X' Y (H1: SC X Y) (H2: eq X' X) : SC X' Y
| Set_R Y X Y' (H1: SC X Y) (H2: eq Y' Y) : SC X Y'
| Basic p X Y : SC (add p X) (add p Y).

(* This tactic proves equality of two sets, which is useful for the Set_L and Set_R rules. *)
Ltac prove_set_equality := simpl; unfold eq; unfold Equal; intros; split;
                       let a := fresh "H" in
                       intros a; repeat rewrite add_spec in a;
                       repeat (match goal with
                               | [H: (_ \/ _) |- _] => destruct H
                               end);
                       subst; repeat rewrite add_spec; intuition.

(* We can use the sequent calculus as a proof system to prove various formulas. *)
Example SC_ex1 : SC empty (of_list [Imp (Pro 0) (Pro 0)]).
Proof using Type. apply Imp_R. apply Basic. Qed.

Example SC_ex2 : SC empty (of_list [Imp (Pro 0) (Imp (Imp (Pro 0) (Pro 1)) (Pro 1))]).
Proof using Type. repeat apply Imp_R. apply Imp_L; apply Basic. Qed.

Example SC_ex3 : SC empty (of_list [Imp (Pro 0) (Imp (Pro 1) (Imp (Pro 1) (Pro 0)))]).
Proof using Type. repeat apply Imp_R. apply (Set_L (of_list [Pro 0; Pro 1; Pro 1])).
       - apply Basic.
       - prove_set_equality.
Qed.

Example SC_ex4 : SC empty (of_list [Imp (Pro 0) (Imp (Imp (Pro 0) Falsity) Falsity)]).
Proof using Type. repeat apply Imp_R. apply Imp_L.
       - apply Basic.
       - apply Fls_L.
Qed.

Example SC_ex5 : SC empty (of_list [Imp (Imp (Imp (Pro 0) (Falsity)) (Falsity)) (Pro 0)]).
Proof using Type. repeat apply Imp_R. apply Imp_L.
       - apply Imp_R. apply (Set_R (of_list [Pro 0; Falsity])).
         + apply Basic.
         + prove_set_equality.
       - apply Fls_L.
Qed.

Example sc_ex1 : forall i, sc empty (of_list [Imp (Imp (Imp (Pro 0) (Falsity)) (Falsity)) (Pro 0)]) i.
Proof using Type.
  unfold sc. intros. destruct (i 0) eqn:EP.
  - unfold Exists. exists (Imp (Imp (Imp (Pro 0) Falsity) Falsity) (Pro 0)). split.
    + apply add_spec. intuition.
    + simpl. intuition.
  - unfold Exists. exists (Imp (Imp (Imp (Pro 0) Falsity) Falsity) (Pro 0)). split.
    + apply add_spec. intuition.
    + simpl. intros. exfalso. apply H0. intros. rewrite EP in H1. inversion H1.
Qed.

(* The proof system above is sound in the sense that if there is a proof
   in it, the sc predicate is true. *)

Lemma sound_imp_l : forall p q l r i, sc l (add p r) i -> sc (add q l) r i -> sc (add (Imp p q) l) r i.
Proof.
  unfold sc. intros.
  destruct (semantics_dec i (Imp p q)).
  - unfold For_all in H1.
    assert (forall x, In x l -> semantics i x).
    { intros. apply H1. apply add_spec. intuition. }
    specialize (H H3). unfold Exists in H. destruct H as [x [HxIn Hx]].
    apply add_spec in HxIn. destruct HxIn.
    + subst. apply H0. unfold For_all. intros. apply add_spec in H.
      destruct H.
      * subst. simpl in H2. intuition.
      * intuition.
    + unfold Exists. exists x. intuition.
  - assert (semantics i (Imp p q)).
    { unfold For_all in H1. apply H1. apply add_spec. intuition. }
    intuition.
Qed.

Lemma semantics_imp : forall p q i, ~ semantics i (Imp p q) -> semantics i p /\ ~ semantics i q.
Proof.
  intros. split.
  - destruct (semantics_dec i p).
    + assumption.
    + exfalso. apply H. simpl. intros. contradiction.
  - destruct (semantics_dec i q).
    + exfalso. apply H. simpl. intros. assumption.
    + assumption.
Qed.

Lemma sound_imp_r : forall p q l r i, sc (add p l) (add q r) i -> sc l (add (Imp p q) r) i.
Proof.
  unfold sc. intros.
  destruct (semantics_dec i (Imp p q)).
  - unfold Exists. exists (Imp p q). split.
    + apply add_spec. intuition.
    + intuition.
  - apply semantics_imp in H1. destruct H1 as [Hp Hnq].
    assert (Hpl: For_all (semantics i) (add p l)).
    { unfold For_all. intros. apply add_spec in H1. destruct H1.
      - subst. assumption.
      - intuition. }
    specialize (H Hpl). unfold Exists in H. destruct H as [x [Hxq Hx]].
    apply add_spec in Hxq. destruct Hxq.
    + subst. intuition.
    + unfold Exists. exists x. split.
      * apply add_spec. intuition.
      * intuition.
Qed.

Theorem sound_sc : forall X Y i,  SC X Y -> sc X Y i.
Proof.
  intros X Y i HSC. induction HSC.
  - unfold sc. intros H. unfold For_all in H.
    specialize (H Falsity). simpl in H. exfalso.
    rewrite add_spec in H. intuition.
  - apply sound_imp_l; assumption.
  - apply sound_imp_r; assumption.
  - unfold sc. unfold eq in H2. unfold Equal in H2. unfold For_all. intros.
    unfold For_all in IHHSC. apply IHHSC. unfold For_all. intros. apply H.
    apply H2. assumption.
  - unfold sc. unfold eq in H2. unfold Equal in H2. unfold Exists. intros.
    unfold Exists in IHHSC. specialize (IHHSC H).
    destruct IHHSC. exists x. rewrite H2. assumption.
  - unfold sc. intros H. unfold Exists. unfold For_all in H. exists p. split.
    + apply add_spec. intuition.
    + apply H. apply add_spec. intuition.
Qed.

(* Specifically, a proof of a single formula means that the formula is semantically valid *)

Corollary sound : forall i p, SC empty (singleton p) -> semantics i p.
Proof.
  intros i p H. apply (sound_sc _ _ i) in H. unfold sc in H.
  destruct H.
  - unfold For_all. intros. apply empty_spec in H. contradiction.

  - intuition. apply singleton_spec in H0. subst. assumption.
Qed.

(* Now we want to define a prover, but first we need some executable helper functions  *)

Fixpoint member (x : nat) (xs : list nat) : bool :=
  match xs with
  | [] => false
  | y :: ys => if Nat.eqb x y then true else member x ys
  end.

Fixpoint common (a b : list nat) : bool :=
  match b with
  | [] => false
  | m :: ms => if member m a then true else common a ms
  end.

(* We define a notion of size for formulas and lists of formulas *)
Fixpoint form_size (f : form) : nat :=
  match f with
  | Pro _ => 1
  | Falsity => 1
  | Imp p q => 1 + form_size p + form_size q
  end.

Fixpoint forms_size (s : list form) : nat :=
  match s with
  | [] => 0
  | x :: xs => form_size x + forms_size xs
  end.

(* We define a prover algorithm to prove formulas.
   We use the measure on lists of formulas to measure the total size of
   the sequent, which is decreasing. *)
Equations? mp (a b : list nat) (c d: list form) : bool by wf (forms_size c + forms_size d) lt :=
  mp a b (Pro n :: c) [] => mp (n :: a) b c [];
  mp a b (Pro m :: c) (Pro n :: d) => mp a (n :: b) (Pro m :: c) d;
  mp a b c (Pro n :: d) => mp a (n :: b) c d;
  mp a b (Falsity :: c) [] => true;
  mp a b c (Falsity :: d) => mp a b c d;
  mp a b (Imp p q :: c) [] => if mp a b c [p] then mp a b (q :: c) [] else false;
  mp a b (Imp r s :: c) (Imp p q :: d) => mp a b (p :: Imp r s :: c) (q :: d);
  mp a b c (Imp p q :: d) => mp a b (p :: c) (q :: d);
  mp a b [] [] => common a b.
Proof. all: try apply lt_n_S; lia. Qed.

Definition prover (p : form) : bool := mp [] [] [] [p].

(* We now want to prove that the prover mp is sound and complete with regards
   to the semantics. *)

(* But first, we take a detour to specify a prover that returns counterexamples, since
   we will need more information than just a boolean value to actually prove
   completeness. *)

(* We define a prover that returns the information necessary to build counterexamples *)
Equations? mu (a b : list nat) (c d : list form) : list (list nat) by wf (forms_size c + forms_size d) lt :=
  mu a b (Pro n :: c) [] => mu (n :: a) b c [];
  mu a b (Pro m :: c) (Pro n :: d) => mu a (n :: b) (Pro m :: c) d;
  mu a b c (Pro n :: d) => mu a (n :: b) c d;
  mu _ _ (Falsity :: _) [] => [];
  mu a b c (Falsity :: d) => mu a b c d;
  mu a b (Imp p q :: c) [] => mu a b c [p] ++ mu a b (q :: c) [];
  mu a b (Imp r s :: c) (Imp p q :: d) => mu a b (p :: Imp r s :: c) (q :: d);
  mu a b c (Imp p q :: d) => mu a b (p :: c) (q :: d);
  mu a b [] [] => if common a b then [] else [a].
Proof. all: try apply lt_n_S; lia. Qed.       

Lemma set_in_add : forall x s, In x s -> exists s', Equal s (add x s').
Proof.
  intros. exists (remove x s). unfold Equal. intros. split.
  - intros. apply add_spec. rewrite remove_spec.
    destruct (Form_As_DT.eq_dec a x).
    + unfold Form_As_DT.eq in e. intuition.
    + unfold Form_As_DT.eq in n. intuition.
  - rewrite add_spec. rewrite remove_spec. intros.
    destruct H0.
    + subst. assumption.
    + intuition.
Qed.

Lemma shared_proven : forall x l r, In x l -> In x r -> SC l r.
Proof.
  intros. apply set_in_add in H. apply set_in_add in H0.
  destruct H as [l' Hl']. destruct H0 as [r' Hr'].
  apply (Set_L (add x l')); try assumption.
  apply (Set_R (add x r')); try assumption.
  apply Basic.
Qed.

Lemma member_In : forall x xs, member x xs = true <-> List.In x xs.
Proof.
  split; intros.
  - induction xs.
    + inversion H.
    + simpl in *. destruct (x =? a) eqn: Hxa.
      * apply Nat.eqb_eq in Hxa. intuition.
      * intuition.
  - induction xs.
    + inversion H.
    + inversion H.
      * subst. simpl. rewrite Nat.eqb_refl. reflexivity.
      * specialize (IHxs H0). simpl. rewrite IHxs. destruct (x =? a); intuition.
Qed.

Lemma common_spec : forall a b, common a b = true -> exists x, List.In x a /\ List.In x b.
Proof.
  intros. induction b.
  - inversion H.
  - destruct a.
    + simpl in *. specialize (IHb H). destruct IHb as [_ [contra _]]. contradiction.
    + destruct (a0 =? n) eqn:Hn.
      * exists n. apply Nat.eqb_eq in Hn. subst. intuition.
      * simpl in H. rewrite Hn in H. destruct (member a0 a) eqn: Ha.
        -- exists a0. apply member_In in Ha. split; intuition.
        -- specialize (IHb H). destruct IHb as [x [Hxa Hxb]]. exists x. intuition.
Qed.

Lemma In_set : forall x b, List.In x b -> In x (of_list b).
Proof.
  intros. induction b.
  - inversion H.
  - simpl. apply add_spec. destruct H; intuition.
Qed.

Lemma in_set_map : forall f : nat -> elt, forall x b, List.In x b -> In (f x) (of_list (map f b)).
Proof.
  intros. apply In_set. apply in_map. assumption.
Qed.

Lemma of_list_comm : forall a b n, Equal (of_list (a ++ n :: b)) (of_list (n :: a ++ b)).
Proof.
  intros. induction a.
  - fsetdec.
  - split.
    + intros. simpl in *. rewrite add_add. rewrite <- IHa. assumption.
    + intros. simpl in *. rewrite add_add in H. rewrite IHa. assumption.
Qed.

Lemma set_add_comm : forall x y A, eq (add x (add y A)) (add y (add x A)).
  intros. unfold eq. unfold Equal. split.
  - intros. apply add_spec in H. destruct H.
    + apply add_spec. right. apply add_spec. intuition.
    + apply add_spec in H. destruct H.
      * apply add_spec. intuition.
      * apply add_spec. right. apply add_spec. intuition.
  - intros. apply add_spec in H. destruct H.
    + apply add_spec. right. apply add_spec. intuition.
    + apply add_spec in H. destruct H.
      * apply add_spec. intuition.
      * apply add_spec. right. apply add_spec. intuition.
Qed.

Lemma weaken : forall l r f, SC l r -> SC l (add f r).
Proof.
  intros. induction H.
  - apply Fls_L.
  - apply Imp_L.
    + apply (Set_R (add f (add p Y))); try assumption; apply set_add_comm.
    + assumption.
  - apply (Set_R (add (Imp p q) (add f Y))); try apply set_add_comm.
    apply Imp_R. apply (Set_R (add f (add q Y))); try assumption; apply set_add_comm.
  - apply (Set_L X); try assumption.
  - apply (Set_R (add f Y)); try assumption. unfold eq. unfold Equal. intros. split.
    + intros. apply add_spec in H0. destruct H0.
      * subst. apply add_spec. intuition.
      * apply add_spec. right. unfold eq in H2. unfold Equal in H2. apply H2. assumption.
    + intros. apply add_spec in H0. destruct H0.
      * subst. apply add_spec. intuition.
      * apply add_spec. right. unfold eq in H2. unfold Equal in H2. apply H2. assumption.
  - apply (Set_R (add p (add f Y))); try apply set_add_comm. apply Basic.
Qed.


Lemma proven : forall a b c d, mu a b c d = [] -> SC (of_list (c ++ map Pro a)) (of_list (d ++ map Pro b)).
Proof.
  intros. funelim (mu a b c d).
  - simpl. simp mu in H.
    assert (Hc: common a b = true).
    { destruct (common a b); congruence. }
    apply common_spec in Hc. destruct Hc as [x [Hxa Hxb]].
    apply (in_set_map Pro) in Hxa. apply (in_set_map Pro) in Hxb.
    apply (shared_proven (Pro x)); assumption.
  - simpl. simp mu in H0. specialize (H a (n :: b) [] d). intuition.
    apply (Set_R (of_list (d ++ Pro n :: map Pro b))).
    + assumption.
    + rewrite of_list_comm. simpl. unfold eq. fsetdec.
  - simpl in *. simp mu in H0. specialize (H a b [] d). intuition.
    apply weaken. assumption.
  - simpl in *. simp mu in H0. specialize (H a b [p] (q :: d)). intuition.
    apply Imp_R. intuition.
  - simpl in *. simp mu in H0. specialize (H (n :: a) b c []). intuition.
    apply (Set_L (of_list (c ++ Pro n :: map Pro a))).
    + assumption.
    + rewrite of_list_comm. simpl. unfold eq. fsetdec.
  - simpl in *. simp mu in H0. specialize (H a (n :: b) (Pro m :: c) d). intuition.
    apply (Set_R (of_list (d ++ map Pro (n :: b)))).
    + assumption.
    + simpl. rewrite of_list_comm. unfold eq. simpl. fsetdec.
  - simpl in *. simp mu in H0. specialize (H a b (Pro n :: l) d). intuition.
    apply weaken. assumption.
  - simpl in *. simp mu in H0. specialize (H a b (p :: Pro n :: l) (q :: d)). intuition.
    apply Imp_R. assumption.
  - apply Fls_L.
  - apply Fls_L.
  - apply Fls_L.
  - apply Fls_L.
  - simpl in *. simp mu in H1. assert (mu a b c [p] = [] /\ mu a b (q :: c) [] = []). { apply app_eq_nil. assumption. }
    destruct H2. specialize (H a b c [p]). specialize (H0 a b (q :: c) []). intuition. apply Imp_L; assumption.
  - simpl in *. simp mu in H0. specialize (H a (n :: b) (Imp p q :: l) d). intuition.
    apply (Set_R (of_list (d ++ map Pro (n :: b)))).
    + assumption.
    + simpl. rewrite of_list_comm. simpl. unfold eq. fsetdec.
  - simpl in *. simp mu in H0. specialize (H a b (Imp p q :: l) d). intuition.
    apply weaken. assumption.
  - simpl in *. simp mu in H0. specialize (H a b (p :: Imp r s :: c) (q :: d)). intuition.
    apply Imp_R. assumption.
Qed.

Lemma mu_sound : forall a b c d, mu a b c d = [] -> forall i, sc (of_list (c ++ map Pro a)) (of_list (d ++ map Pro b)) i.
Proof.
  intros. apply sound_sc. apply proven. assumption.
Qed.

(* Equivalence between mu and mp *)

Lemma mu_mp_eq : forall a b c d, mu a b c d = [] <-> mp a b c d = true.
Proof.
  split.
  - intros. funelim (mu a b c d); simp mp; simp mu in *.
    + destruct (common a b).
      * reflexivity.
      * inversion H.
    + specialize (H a (n :: b) [] d). intuition.
    + specialize (H a b [] d). intuition.
    + specialize (H a b [p] (q :: d)). intuition.
    + specialize (H (n :: a) b c []). intuition.
    + specialize (H a (n :: b) (Pro m :: c) d). intuition.
    + specialize (H a b (Pro n :: l) d). intuition.
    + specialize (H a b (p :: Pro n :: l) (q :: d)). intuition.
    + reflexivity.
    + specialize (H a (n :: b) (Falsity :: l) d). intuition.
    + specialize (H a b (Falsity :: l) d). intuition.
    + specialize (H a b (p :: Falsity :: l) (q :: d)). intuition.
    + assert (mu a b c [p] = [] /\ mu a b (q :: c) [] = []). { apply app_eq_nil. assumption. }
      destruct H2. specialize (H a b c [p]). specialize (H0 a b (q :: c) []). intuition.
      rewrite H. assumption.        
    + specialize (H a (n :: b) (Imp p q :: l) d). intuition.
    + specialize (H a b (Imp p q :: l) d). intuition.
    + specialize (H a b (p :: Imp r s :: c) (q :: d)). intuition.
  - intros. funelim (mp a b c d); simp mu; simp mp in *.
    + rewrite H. reflexivity.
    + specialize (H a (n :: b) [] d). intuition.
    + specialize (H a b [] d). intuition.
    + specialize (H a b [p] (q :: d)). intuition.
    + specialize (H (n :: a) b c []). intuition.
    + specialize (H a (n :: b) (Pro m :: c) d). intuition.
    + specialize (H a b (Pro n :: l) d). intuition.
    + specialize (H a b (p :: Pro n :: l) (q :: d)). intuition.
    + reflexivity.
    + specialize (H a (n :: b) (Falsity :: l) d). intuition.
    + specialize (H a b (Falsity :: l) d). intuition.
    + specialize (H a b (p :: Falsity :: l) (q :: d)). intuition.
    + assert (mp a b (q :: c) [] = true /\ mp a b c [p] = true).
      { destruct (mp a b (q :: c) []); destruct (mp a b c [p]); intuition. } destruct H2.
      specialize (H a b c [p]). specialize (H0 a b (q :: c) []). intuition. rewrite H. rewrite H0.
      reflexivity.
    + specialize (H a (n :: b) (Imp p q :: l) d). intuition.
    + specialize (H a b (Imp p q :: l) d). intuition.
    + specialize (H a b (p :: Imp r s :: c) (q :: d)). intuition.
Qed.

(* Completeness *)

Definition counter_sem (ns : list nat) : (nat -> bool) :=
  fun n => member n ns.

Lemma member_app : forall extra x xs, member x xs = true -> member x (extra ++ xs) = true.
Proof.
  intros. generalize dependent extra. induction xs.
  - inversion H.
  - intros. destruct (x =? a) eqn:Hax.
    + apply member_In. apply Nat.eqb_eq in Hax. subst. intuition.
    + simpl in H. rewrite Hax in H.
      replace (extra ++ a :: xs) with ((extra ++ [a]) ++ xs) by (rewrite <- app_assoc; intuition).
      apply (IHxs H (extra ++ [a])).
Qed.

Lemma counter_lhs : forall extra a, For_all (semantics (counter_sem (extra ++ a))) (of_list (map Pro a)).
Proof.
  unfold For_all. intros. generalize dependent extra. induction a.
  - inversion H.
  - intros. simpl in *. apply add_spec in H. destruct H.
    + subst. simpl in *. unfold counter_sem in *. apply member_app. simpl. rewrite Nat.eqb_refl. reflexivity.
    + replace (extra ++ a :: a0) with ((extra ++ [a]) ++ a0).
      * apply IHa. assumption.
      * rewrite <- app_assoc. reflexivity.
Qed.

Lemma drop_falsity : forall a b i, sc a (add Falsity b) i -> sc a b i.
Proof.
  unfold sc. intros. unfold Exists in *. specialize (H H0).
  destruct H as [x [Hin Hx]]. exists x. intuition.
  apply add_spec in Hin. destruct Hin.
  - subst. contradiction.
  - assumption.
Qed.

Lemma sc_of_list_comm_right : forall x y z w i, sc x (add z (of_list (y ++ w))) i -> sc x (of_list (y ++ z :: w)) i.
Proof.
  unfold sc. unfold Exists. intros. specialize (H H0).
  destruct H as [a [Hin Ha]]. exists a. split.
  - apply of_list_comm. assumption.
  - assumption.
Qed.

Lemma sc_of_list_comm_left : forall x y z w i,  sc (add x (of_list (y ++ z))) w i -> sc (of_list (y ++ x :: z)) w i.
Proof.
  unfold sc. unfold For_all. intros. apply H.
  intros. apply H0. apply of_list_comm. assumption.
Qed.

Lemma complete_imp_r : forall p q x y i, sc x (add (Imp p q) y) i -> sc (add p x) (add q y) i.
Proof.
  unfold sc. unfold Exists. unfold For_all. intros. destruct (semantics_dec i q).
  - exists q. intuition.
  - assert (Hasm: forall x0, In x0 x -> semantics i x0). { intros. apply H0. apply add_spec. intuition. }
    specialize (H Hasm). destruct H as [e [Hin He]].
    exists e. apply add_spec in Hin. split.
    + destruct (semantics_dec i p).
      * destruct Hin.
        -- subst. intuition.
        -- apply add_spec. intuition.
      * destruct Hin.
        -- subst. intuition.
        -- apply add_spec. intuition.
    + assumption.
Qed.

Lemma complete_imp_l : forall p q x y i, sc (add (Imp p q) x) y i -> sc x (add p y) i /\ sc (add q x) y i.
Proof.
  unfold sc. unfold Exists. unfold For_all. split.
  - intros. destruct (semantics_dec i p).
    + exists p. intuition.
    + destruct (semantics_dec i (Imp p q)).
      * assert (Hasm: forall x0, In x0 (add (Imp p q) x) -> semantics i x0).
        { intros. apply add_spec in H3. destruct H3.
          - subst. assumption.
          - intuition. }
        specialize (H Hasm). destruct H as [a [Hin Ha]].
        exists a. intuition.
      * simpl in H2. intuition.
  - intros. destruct (semantics_dec i q).
    + destruct (semantics_dec i (Imp p q)).
      * assert (Hasm: forall x0, In x0 x -> semantics i x0). { intros. apply H0. intuition. }
        apply H. intros. apply add_spec in H3. destruct H3.
        -- subst. assumption.
        -- intuition.
      * simpl in H2. intuition.
    + intuition.
Qed.

Lemma member_common : forall a x y, member a x = true -> member a y = true -> common x y = true.
Proof.
  intros a x. induction y.
  - intros. inversion H0.
  - intros. simpl. destruct (a =? a0) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. rewrite H. reflexivity.
    + simpl in H0. rewrite Heq in H0. specialize (IHy H H0).
      rewrite IHy. destruct (member a0 x); intuition.
Qed.

Lemma in_of_list_member : forall x xs, In (Pro x) (of_list (map Pro xs)) -> member x xs = true.
Proof.
  intros. induction xs.
  - inversion H.
  - simpl. destruct (x =? a) eqn:Heq.
    + reflexivity.
    + apply IHxs. simpl in H. apply add_spec in H. destruct H.
      * apply Nat.eqb_neq in Heq. inversion H. contradiction.
      * assumption.
Qed.

Lemma in_map_inversion : forall x xs, In x (of_list (map Pro xs)) -> exists y, x = Pro y /\ List.In y xs.
Proof.
  intros. induction xs.
  - inversion H.
  - simpl in H. apply add_spec in H. destruct H.
    + exists a. intuition.
    + specialize (IHxs H). destruct IHxs as [y [Hxy Hin]].
      exists y. intuition.
Qed.
    
Lemma counter : forall a b c d (xs : list nat), List.In xs (mu a b c d) -> ~ sc (of_list (c ++ map Pro a)) (of_list (d ++ map Pro b)) (counter_sem xs).
Proof.
  intros. funelim (mu a b c d).
  - simpl in *. simp mu in H. destruct (common a b) eqn:Hab.
    + inversion H.
    + inversion H.
      * subst. unfold sc. unfold not. intros. specialize (H0 (counter_lhs [] xs)).
        unfold Exists in H0. destruct H0 as [x [Hin Hx]].
        assert (exists x', x = Pro x').
        { apply in_map_inversion in Hin. destruct Hin as [y [Hxy Hin]]. exists y. intuition. }
        destruct H0 as [x' Hx']. subst. simpl in *.
        apply in_of_list_member in Hin.
        assert (common xs b = true). apply (member_common x'); assumption.
        congruence.
      * contradiction.
  - simpl in *. simp mu in H0. specialize (H xs H0). unfold not. intros. apply H.
    apply sc_of_list_comm_right. assumption.
  - simpl in *. simp mu in H0. specialize (H xs H0). unfold not. intros. apply drop_falsity in H1.
    intuition.
  - simpl in *. simp mu in H0. specialize (H xs H0). unfold not. intros. apply H.
    apply complete_imp_r. assumption.
  - simpl in *. simp mu in H0. specialize (H xs H0). unfold not. intros. apply H.
    apply sc_of_list_comm_left. assumption.
  - simpl in *. simp mu in H0. specialize (H xs H0). unfold not. intros. apply H.
    apply sc_of_list_comm_right. assumption.
  - simpl in *. simp mu in H0. specialize (H xs H0). unfold not. intros. apply drop_falsity in H1.
    intuition.
  - simpl in *. simp mu in H0. specialize (H xs H0). unfold not. intros. apply H.
    apply complete_imp_r. assumption.
  - simp mu in H. inversion H.
  - simpl in *. simp mu in H0. specialize (H xs H0). unfold not. intros. apply H.
    apply sc_of_list_comm_right. assumption.
  - simpl in *. simp mu in H0. specialize (H xs H0). unfold not. intros. apply drop_falsity in H1.
    intuition.
  - simpl in *. simp mu in H0. specialize (H xs H0). unfold not. intros. apply H.
    apply complete_imp_r. assumption.
  - simpl in *. simp mu in H1. apply in_app_or in H1. destruct H1.
    + specialize (H xs H1). unfold not. intros. apply H. apply complete_imp_l in H2. intuition.
    + specialize (H0 xs H1). unfold not. intros. apply H0. apply complete_imp_l in H2. intuition.
  - simpl in *. simp mu in H0. specialize (H xs H0). unfold not. intros. apply H.
    apply sc_of_list_comm_right. assumption.
  - simpl in *. simp mu in H0. specialize (H xs H0). unfold not. intros. apply drop_falsity in H1.
    intuition.
  - simpl in *. simp mu in H0. specialize (H xs H0). unfold not. intros. apply H.
    apply complete_imp_r. assumption.
Qed.

Lemma mu_complete : forall a b c d, (forall i, sc (of_list (c ++ map Pro a)) (of_list (d ++ map Pro b)) i) -> mu a b c d = [].
Proof.
  intros. destruct (mu a b c d) eqn:He.
  - reflexivity.
  - exfalso. specialize counter. intros counter.
    specialize (counter a b c d l). unfold not in counter.
    apply counter.
    + rewrite He. apply in_eq.
    + apply H.
Qed.

Theorem sound_complete' : forall a b c d, (forall i, sc (of_list (c ++ map Pro a)) (of_list (d ++ map Pro b)) i) <-> mp a b c d = true.
Proof.
  unfold prover. split.
  - intros. apply mu_mp_eq. apply mu_complete. assumption.
  - intros. apply mu_mp_eq in H. apply mu_sound. assumption.
Qed.

Lemma sc_semantics : forall i p, sc (of_list ([] ++ map Pro [])) (of_list ([p] ++ map Pro [])) i -> semantics i p.
Proof.
  intros. simpl in H. unfold sc in H. unfold Exists in H. unfold For_all in H.
  assert (forall x, In x empty -> semantics i x). { intros. inversion H0. }
  specialize (H H0). destruct H as [x [Hadd Hx]]. apply add_spec in Hadd. destruct Hadd.
  - subst. assumption.
  - inversion H.
Qed.

Corollary sound_complete : forall p, (forall i, semantics i p) <-> prover p = true.
Proof.
  intros p. split.
  - intros H. apply sound_complete'. intros i. unfold sc. simpl.
    intros Hs. unfold For_all in Hs. unfold Exists. exists p; intuition.
  - intros. unfold prover in H. apply sc_semantics. apply sound_complete'. assumption.
Qed.

Extraction Language Haskell.
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.
Extraction "prover/MicroProver.hs" prover.
