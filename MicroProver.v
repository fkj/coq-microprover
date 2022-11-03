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

(* Before we can form MSets of formulas, we need to show that they are a decidable type *)
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

(* Now we can obtain MSets of formulas and a number of theorems about them *)
Module Import S := Make Form_As_DT.
Module Import MSetDec := MSetDecide.WDecide S.
Module Import MSetFacts := MSetFacts.WFacts S.
Module Import MSetProps := MSetProperties.WProperties S.
Module Import MSetEqProps := MSetEqProperties.WEqProperties S.
Infix "[+]" := add (at level 81, right associativity).

(* Semantics is a predicate over an interpretation i determining
   whether the formula is true for the given interpretation. *)
Fixpoint semantics (i : nat -> bool) (f : form) : Prop :=
  match f with
  | Pro n => i n = true
  | Falsity => False
  | Imp p q => semantics i p -> semantics i q
  end.

(* The semantics function is decidable, which we will need to
   perform proofs by case analysis on the semantics *)
Lemma semantics_dec : forall i f, decidable (semantics i f).
Proof using Type.
  intros. unfold decidable. induction f as [ | | IHf1 IHf2 ].
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

Reserved Infix ">>" (at level 90, no associativity).
Inductive SC : t -> t -> Prop :=
| Fls_L X Y : Falsity [+] X >> Y
| Imp_L p q X Y (H1: X >> p [+] Y) (H2: q [+] X >> Y)
  : Imp p q [+] X >> Y
| Imp_R p q X Y (H: p [+] X >> q [+] Y) : X >> (Imp p q [+] Y)
| Set_L X X' Y (H1: X >> Y) (H2: eq X' X) : X' >> Y
| Set_R Y X Y' (H1: X >> Y) (H2: eq Y' Y) : X >> Y'
| Basic p X Y : (p [+] X) >> (p [+] Y)
where "X >> Y" := (SC X Y).

(* This tactic proves equality of two concrete sets, which is useful
   for the Set_L and Set_R rules in the examples below. *)
Ltac prove_set_equality := simpl; unfold eq; unfold Equal; intros; split;
                       let a := fresh "H" in
                       intros a; repeat rewrite add_spec in a;
                       repeat (match goal with
                               | [H: (_ \/ _) |- _] => destruct H
                               end);
                       subst; repeat rewrite add_spec; intuition.

(* We can use the sequent calculus as a proof system to prove various formulas. *)
Example SC_ex1 : empty >> (of_list [Imp (Pro 0) (Pro 0)]).
Proof using Type. apply Imp_R. apply Basic. Qed.

Example SC_ex2 : empty >> (of_list [Imp (Pro 0) (Imp (Imp (Pro 0) (Pro 1)) (Pro 1))]).
Proof using Type. repeat apply Imp_R. apply Imp_L; apply Basic. Qed.

Example SC_ex3 : empty >> (of_list [Imp (Pro 0) (Imp (Pro 1) (Imp (Pro 1) (Pro 0)))]).
Proof using Type. repeat apply Imp_R. apply (Set_L (of_list [Pro 0; Pro 1; Pro 1])).
       - apply Basic.
       - prove_set_equality.
Qed.

Example SC_ex4 : empty >> (of_list [Imp (Pro 0) (Imp (Imp (Pro 0) Falsity) Falsity)]).
Proof using Type. repeat apply Imp_R. apply Imp_L.
       - apply Basic.
       - apply Fls_L.
Qed.

Example SC_ex5 : empty >> (of_list [Imp (Imp (Imp (Pro 0) (Falsity)) (Falsity)) (Pro 0)]).
Proof using Type. repeat apply Imp_R. apply Imp_L.
       - apply Imp_R. apply (Set_R (of_list [Pro 0; Falsity])).
         + apply Basic.
         + prove_set_equality.
       - apply Fls_L.
Qed.

Example sc_ex1 : forall i, sc empty (of_list [Imp (Imp (Imp (Pro 0) (Falsity)) (Falsity)) (Pro 0)]) i.
Proof using Type.
  unfold sc. intros i Hempty. destruct (i 0) eqn:EP.
  - unfold Exists. exists (Imp (Imp (Imp (Pro 0) Falsity) Falsity) (Pro 0)). split.
    + apply add_spec. intuition.
    + simpl. intuition.
  - unfold Exists. exists (Imp (Imp (Imp (Pro 0) Falsity) Falsity) (Pro 0)). split.
    + apply add_spec. intuition.
    + simpl. intros. exfalso. apply H. intros H'. rewrite EP in H'. inversion H'.
Qed.

(* The proof system above is sound in the sense that if there is a proof
   in it, the sc predicate is true. *)

Lemma sound_imp_l : forall p q l r i, sc l (p [+] r) i -> sc (q [+] l) r i -> sc ((Imp p q) [+] l) r i.
Proof.
  unfold sc. intros p q l r i Hp Hq Hpq.
  destruct (semantics_dec i (Imp p q)) as [H | H].
  - unfold For_all in Hpq.
    assert (Hxl: forall x, In x l -> semantics i x).
    { intros. apply Hpq. apply add_spec. intuition. }
    specialize (Hp Hxl). unfold Exists in Hp. destruct Hp as [x [HxIn Hx]].
    apply add_spec in HxIn. destruct HxIn.
    + subst. apply Hq. unfold For_all. intros x Hx'. apply add_spec in Hx'.
      destruct Hx'.
      * subst. simpl in Hpq. intuition.
      * intuition.
    + unfold Exists. exists x. intuition.
  - assert (Himp: semantics i (Imp p q)).
    { unfold For_all in Hq. apply Hpq. apply add_spec. intuition. }
    intuition.
Qed.

Lemma semantics_imp : forall p q i, ~ semantics i (Imp p q) -> semantics i p /\ ~ semantics i q.
Proof.
  intros p q i H. split.
  - destruct (semantics_dec i p).
    + assumption.
    + exfalso. apply H. simpl. intuition.
  - destruct (semantics_dec i q).
    + exfalso. apply H. simpl. intuition.
    + assumption.
Qed.

Lemma sound_imp_r : forall p q l r i, sc (p [+] l) (q [+] r) i -> sc l (Imp p q [+] r) i.
Proof.
  unfold sc. intros p q l r i Hsc Hl.
  destruct (semantics_dec i (Imp p q)) as [ | H].
  - unfold Exists. exists (Imp p q). split.
    + apply add_spec. intuition.
    + intuition.
  - apply semantics_imp in H. destruct H as [Hp Hnq].
    assert (Hpl: For_all (semantics i) (add p l)).
    { unfold For_all. intros. apply add_spec in H. destruct H.
      - subst. assumption.
      - intuition. }
    specialize (Hsc Hpl). unfold Exists in Hsc. destruct Hsc as [x [Hxq Hx]].
    apply add_spec in Hxq. destruct Hxq.
    + subst. intuition.
    + unfold Exists. exists x. split.
      * apply add_spec. intuition.
      * intuition.
Qed.

Theorem sound_sc : forall X Y i, X >> Y -> sc X Y i.
Proof.
  intros X Y i HSC. induction HSC as [ | | | X X' Y HSC IH Heq | Y X Y' HSC IH Heq | ].
  - unfold sc. intros H. unfold For_all in H.
    specialize (H Falsity). simpl in H. exfalso.
    rewrite add_spec in H. intuition.
  - apply sound_imp_l; assumption.
  - apply sound_imp_r; assumption.
  - unfold sc. unfold eq in Heq. unfold Equal in Heq. unfold For_all. intros.
    unfold For_all in IH. apply IH. unfold For_all. intros. intuition.
  - unfold sc. unfold eq in Heq. unfold Equal in Heq. unfold Exists. intros.
    unfold Exists in IH. specialize (IH H). destruct IH. exists x. rewrite Heq. assumption.
  - unfold sc. intros H. unfold Exists. unfold For_all in H. exists p. split.
    + apply add_spec. intuition.
    + apply H. apply add_spec. intuition.
Qed.

(* Specifically, a proof of a single formula means that the formula is semantically valid *)
Corollary sound : forall i p, empty >> singleton p -> semantics i p.
Proof.
  intros i p H. apply (sound_sc _ _ i) in H. unfold sc in H.
  destruct H.
  - unfold For_all. intros. apply empty_spec in H. contradiction.
  - destruct H as [Hin Hx]. apply singleton_spec in Hin. subst. assumption.
Qed.

(* Now we want to define a prover, but first we need some executable helper functions *)

Fixpoint member (x : nat) (xs : list nat) : bool :=
  match xs with
  | [] => false
  | y :: ys => if x =? y then true else member x ys
  end.

Fixpoint common (a b : list nat) : bool :=
  match b with
  | [] => false
  | m :: ms => if member m a then true else common a ms
  end.

(* We also need a notion of size for formulas and lists of formulas
   for our termination proofs *)
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

(* We can specialize this function to a prover for a single formula *)
Definition prover (p : form) : bool := mp [] [] [] [p].

(* We now want to prove that the prover is sound and complete with regards
   to the semantics. *)

(* To do this, we first take a detour to specify a prover that returns counterexamples,
   since we will need more information than just a boolean value to actually prove
   completeness. *)

(* We thus define a prover that returns the information necessary to build counterexamples *)
Equations? mu (a b : list nat) (c d : list form) : list (list nat)
  by wf (forms_size c + forms_size d) lt :=
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

(* Before we can prove soundness and completeness, we need to prove a
   few properties about sets and our proof system *)
Lemma set_in_add : forall x s, In x s -> exists s', Equal s (x [+] s').
Proof.
  intros x s H. exists (remove x s). unfold Equal. intros a. split.
  - intros H'. apply add_spec. rewrite remove_spec.
    destruct (Form_As_DT.eq_dec a x) as [e | n].
    + unfold Form_As_DT.eq in e. intuition.
    + unfold Form_As_DT.eq in n. intuition.
  - rewrite add_spec. rewrite remove_spec. intros H'. destruct H'.
    + subst. assumption.
    + intuition.
Qed.

Lemma shared_proven : forall x l r, In x l -> In x r -> l >> r.
Proof.
  intros x l r Hl Hr. apply set_in_add in Hl. apply set_in_add in Hr.
  destruct Hl as [l' Hl']. destruct Hr as [r' Hr'].
  apply (Set_L (add x l')); try assumption.
  apply (Set_R (add x r')); try assumption.
  apply Basic.
Qed.

Lemma member_In : forall x xs, member x xs = true <-> List.In x xs.
Proof.
  intros x xs. split; intros H.
  - induction xs as [ | x' xs' IH].
    + inversion H.
    + simpl in *. destruct (x =? x') eqn: Heq.
      * apply Nat.eqb_eq in Heq. intuition.
      * intuition.
  - induction xs as [| x' xs' IH].
    + inversion H.
    + inversion H as [Heq | Hin].
      * subst. simpl. rewrite Nat.eqb_refl. reflexivity.
      * specialize (IH Hin). simpl. rewrite IH. destruct (x =? x'); intuition.
Qed.

Lemma common_spec : forall a b, common a b = true -> exists x, List.In x a /\ List.In x b.
Proof.
  intros a b H. induction b as [ | b' bs IH].
  - inversion H.
  - destruct a as [ | a' as' ].
    + simpl in *. specialize (IH H). destruct IH as [_ [contra _]]. contradiction.
    + destruct (b' =? a') eqn:Hab.
      * exists a'. apply Nat.eqb_eq in Hab. subst. intuition.
      * simpl in H. rewrite Hab in H. destruct (member b' as') eqn: Hmem.
        -- exists b'. apply member_In in Hmem. split; intuition.
        -- specialize (IH H). destruct IH as [x []]. exists x. intuition.
Qed.

Lemma In_set : forall x b, List.In x b -> In x (of_list b).
Proof.
  intros x b H. induction b.
  - inversion H.
  - simpl. apply add_spec. destruct H; intuition.
Qed.

Lemma in_set_map : forall f : nat -> elt, forall x b, List.In x b -> In (f x) (of_list (map f b)).
Proof.
  intros. apply In_set. apply in_map. assumption.
Qed.

Lemma of_list_comm : forall a b n, Equal (of_list (a ++ n :: b)) (of_list (n :: a ++ b)).
Proof.
  intros a b n. induction a as [| a' as' IH].
  - fsetdec.
  - split.
    + intros. simpl in *. rewrite add_add. rewrite <- IH. assumption.
    + intros H. simpl in *. rewrite add_add in H. rewrite IH. assumption.
Qed.

Lemma set_add_comm : forall x y A, eq (x [+] y [+] A) (y [+] x [+] A).
  intros. unfold eq. unfold Equal. split.
  - intros H. apply add_spec in H. destruct H as [ | H].
    + apply add_spec. right. apply add_spec. intuition.
    + apply add_spec in H. destruct H.
      * apply add_spec. intuition.
      * apply add_spec. right. apply add_spec. intuition.
  - intros H. apply add_spec in H. destruct H as [ | H].
    + apply add_spec. right. apply add_spec. intuition.
    + apply add_spec in H. destruct H.
      * apply add_spec. intuition.
      * apply add_spec. right. apply add_spec. intuition.
Qed.

Lemma weaken : forall l r f, l >> r -> l >> f [+] r.
Proof.
  intros l r f H. induction H as [ | p q X Y | p q X Y | X X' Y | Y X Y' H Hf Heq | p X Y ].
  - apply Fls_L.
  - apply Imp_L.
    + apply (Set_R (add f (add p Y))); try assumption; apply set_add_comm.
    + assumption.
  - apply (Set_R (add (Imp p q) (add f Y))); try apply set_add_comm.
    apply Imp_R. apply (Set_R (add f (add q Y))); try assumption; apply set_add_comm.
  - apply (Set_L X); try assumption.
  - apply (Set_R (add f Y)); try assumption. unfold eq. unfold Equal. intros. split.
    + intros H'. apply add_spec in H'. destruct H'.
      * subst. apply add_spec. intuition.
      * apply add_spec. right. unfold eq in Heq. unfold Equal in Heq. apply Heq. assumption.
    + intros H'. apply add_spec in H'. destruct H'.
      * subst. apply add_spec. intuition.
      * apply add_spec. right. unfold eq in Heq. unfold Equal in Heq. apply Heq. assumption.
  - apply (Set_R (add p (add f Y))); try apply set_add_comm. apply Basic.
Qed.

(* We are now ready to prove the soundness of our counterexample-producing prover *)
Lemma proven : forall a b c d, mu a b c d = [] -> SC (of_list (c ++ map Pro a)) (of_list (d ++ map Pro b)).
Proof.
  intros a b c d Hmu. funelim (mu a b c d).
  - simpl. simp mu in Hmu.
    assert (Hc: common a b = true).
    { destruct (common a b); congruence. }
    apply common_spec in Hc. destruct Hc as [x [Hxa Hxb]].
    apply (in_set_map Pro) in Hxa. apply (in_set_map Pro) in Hxb.
    apply (shared_proven (Pro x)); assumption.
  - simpl. simp mu in Hmu. apply (Set_R (of_list (d ++ Pro n :: map Pro b))).
    + apply (H a (n :: b) [] d); intuition.
    + rewrite of_list_comm. simpl. unfold eq. fsetdec.
  - simpl in *. simp mu in Hmu. apply weaken. apply (H a b [] d); intuition.
  - simpl in *. simp mu in Hmu. apply Imp_R. apply (H a b [p] (q :: d)); intuition.
  - simpl in *. simp mu in Hmu. apply (Set_L (of_list (c ++ Pro n :: map Pro a))).
    + apply (H (n :: a) b c []); intuition.
    + rewrite of_list_comm. simpl. unfold eq. fsetdec.
  - simpl in *. simp mu in Hmu. apply (Set_R (of_list (d ++ map Pro (n :: b)))).
    + apply (H a (n :: b) (Pro m :: c) d); intuition.
    + simpl. rewrite of_list_comm. unfold eq. simpl. fsetdec.
  - simpl in *. simp mu in Hmu. apply weaken. specialize (H a b (Pro n :: l) d); intuition.
  - simpl in *. simp mu in Hmu. apply Imp_R. specialize (H a b (p :: Pro n :: l) (q :: d)); intuition.
  - apply Fls_L.
  - apply Fls_L.
  - apply Fls_L.
  - apply Fls_L.
  - simpl in *. simp mu in Hmu.
    assert (mu a b c [p] = [] /\ mu a b (q :: c) [] = []). { apply app_eq_nil. assumption. }
    destruct Hmu. apply Imp_L. 
    + apply (H a b c [p]); intuition.
    + apply (H0 a b (q :: c) []); intuition.
  - simpl in *. simp mu in Hmu. apply (Set_R (of_list (d ++ map Pro (n :: b)))).
    + apply (H a (n :: b) (Imp p q :: l) d); intuition.
    + simpl. rewrite of_list_comm. simpl. unfold eq. fsetdec.
  - simpl in *. simp mu in Hmu. apply weaken. apply (H a b (Imp p q :: l) d); intuition.
  - simpl in *. simp mu in Hmu. apply Imp_R. apply (H a b (p :: Imp r s :: c) (q :: d)); intuition.
Qed.

Corollary mu_sound : forall a b c d,
    mu a b c d = [] -> forall i, sc (of_list (c ++ map Pro a)) (of_list (d ++ map Pro b)) i.
Proof.
  intros. apply sound_sc. apply proven. assumption.
Qed.

(* To transfer these results to our boolean prover, we need an equivalence between mu and mp *)
Lemma mu_mp_eq : forall a b c d, mu a b c d = [] <-> mp a b c d = true.
Proof.
  split.
  - intros H. funelim (mu a b c d); simp mp; simp mu in *.
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
    + intuition.
    + specialize (H a (n :: b) (Falsity :: l) d). intuition.
    + specialize (H a b (Falsity :: l) d). intuition.
    + specialize (H a b (p :: Falsity :: l) (q :: d)). intuition.
    + assert (Hempty: mu a b c [p] = [] /\ mu a b (q :: c) [] = []).
      { apply app_eq_nil. assumption. }
      destruct Hempty. specialize (H a b c [p]). specialize (H0 a b (q :: c) []). intuition.
      rewrite H. assumption.        
    + specialize (H a (n :: b) (Imp p q :: l) d). intuition.
    + specialize (H a b (Imp p q :: l) d). intuition.
    + specialize (H a b (p :: Imp r s :: c) (q :: d)). intuition.
  - intros H. funelim (mp a b c d); simp mu; simp mp in *.
    + rewrite H. intuition.
    + specialize (H a (n :: b) [] d). intuition.
    + specialize (H a b [] d). intuition.
    + specialize (H a b [p] (q :: d)). intuition.
    + specialize (H (n :: a) b c []). intuition.
    + specialize (H a (n :: b) (Pro m :: c) d). intuition.
    + specialize (H a b (Pro n :: l) d). intuition.
    + specialize (H a b (p :: Pro n :: l) (q :: d)). intuition.
    + intuition.
    + specialize (H a (n :: b) (Falsity :: l) d). intuition.
    + specialize (H a b (Falsity :: l) d). intuition.
    + specialize (H a b (p :: Falsity :: l) (q :: d)). intuition.
    + assert (Htrue: mp a b (q :: c) [] = true /\ mp a b c [p] = true).
      { destruct (mp a b (q :: c) []); destruct (mp a b c [p]); intuition. }
      destruct Htrue. specialize (H a b c [p]). specialize (H0 a b (q :: c) []).
      intuition. rewrite H. rewrite H0. reflexivity.
    + specialize (H a (n :: b) (Imp p q :: l) d). intuition.
    + specialize (H a b (Imp p q :: l) d). intuition.
    + specialize (H a b (p :: Imp r s :: c) (q :: d)). intuition.
Qed.

(* Completeness *)

(* We define an interpretation that checks for membership in a given set *)
Definition counter_sem (ns : list nat) : (nat -> bool) :=
  fun n => member n ns.

(* To prove completeness, we need a number of intermediate lemmas *)
Lemma member_app : forall x xs extra, member x xs = true -> member x (extra ++ xs) = true.
Proof.
  intros x xs. induction xs as [| x' xs' IH].
  - intros extra H. inversion H.
  - intros. destruct (x =? x') eqn:Heq.
    + apply member_In. apply Nat.eqb_eq in Heq. subst. intuition.
    + simpl in H. rewrite Heq in H.
      replace (extra ++ x' :: xs') with ((extra ++ [x']) ++ xs') by (rewrite <- app_assoc; intuition).
      apply (IH (extra ++ [x']) H).
Qed.

Lemma counter_lhs : forall a extra, For_all (semantics (counter_sem (extra ++ a))) (of_list (map Pro a)).
Proof.
  unfold For_all. intros a. induction a as [| a' as' IH].
  - intros extra x H. inversion H.
  - intros extra x H. simpl in *. apply add_spec in H. destruct H.
    + subst. simpl in *. unfold counter_sem in *. apply member_app.
      simpl. rewrite Nat.eqb_refl. reflexivity.
    + replace (extra ++ a' :: as') with ((extra ++ [a']) ++ as').
      * apply IH. assumption.
      * rewrite <- app_assoc. reflexivity.
Qed.

Lemma drop_falsity : forall a b i, sc a (Falsity [+] b) i -> sc a b i.
Proof.
  unfold sc. intros a b i Hsc Ha. unfold Exists in *. specialize (Hsc Ha).
  destruct Hsc as [x [Hin Hx]]. exists x. intuition.
  apply add_spec in Hin. destruct Hin.
  - subst. contradiction.
  - assumption.
Qed.

Lemma sc_of_list_comm_right : forall x y z w i,
    sc x (add z (of_list (y ++ w))) i -> sc x (of_list (y ++ z :: w)) i.
Proof.
  unfold sc. unfold Exists. intros x y z w i Hsc Hx. specialize (Hsc Hx).
  destruct Hsc as [a [Hin Ha]]. exists a. split.
  - apply of_list_comm. assumption.
  - assumption.
Qed.

Lemma sc_of_list_comm_left : forall x y z w i,
    sc (add x (of_list (y ++ z))) w i -> sc (of_list (y ++ x :: z)) w i.
Proof.
  unfold sc. unfold For_all. intros x y z w i Hsc Hall. apply Hsc.
  intros. apply Hall. apply of_list_comm. assumption.
Qed.

Lemma complete_imp_r : forall p q x y i, sc x (add (Imp p q) y) i -> sc (add p x) (add q y) i.
Proof.
  unfold sc. unfold Exists. unfold For_all. intros p q x y i Hsc Hall. destruct (semantics_dec i q).
  - exists q. intuition.
  - assert (Hasm: forall x0, In x0 x -> semantics i x0). { intros. apply Hall. apply add_spec. intuition. }
    destruct (Hsc Hasm) as [e [Hin He]].
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
  - intros Hall. destruct (semantics_dec i p).
    + exists p. intuition.
    + destruct (semantics_dec i (Imp p q)) as [ | Hsem].
      * assert (Hasm: forall x0, In x0 (add (Imp p q) x) -> semantics i x0).
        { intros a Ha. apply add_spec in Ha. destruct Ha.
          - subst. assumption.
          - intuition. }
        specialize (H Hasm). destruct H as [a [Hin Ha]].
        exists a. intuition.
      * simpl in Hsem. intuition.
  - intros Hall. destruct (semantics_dec i q).
    + destruct (semantics_dec i (Imp p q)) as [ | Hsem].
      * assert (Hasm: forall x0, In x0 x -> semantics i x0). { intros. apply Hall. intuition. }
        apply H. intros a Ha. apply add_spec in Ha. destruct Ha.
        -- subst. assumption.
        -- intuition.
      * simpl in Hsem. intuition.
    + intuition.
Qed.

Lemma member_common : forall a x y, member a x = true -> member a y = true -> common x y = true.
Proof.
  intros a x y. induction y as [| a' as' IH ].
  - intros. inversion H0.
  - intros Hx Hy. simpl. destruct (a =? a') eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. rewrite Hx. reflexivity.
    + simpl in Hy. rewrite Heq in Hy. specialize (IH Hx Hy).
      rewrite IH. destruct (member a' x); intuition.
Qed.

Lemma in_of_list_member : forall x xs, In (Pro x) (of_list (map Pro xs)) -> member x xs = true.
Proof.
  intros x xs H. induction xs as [| x' xs' IH].
  - inversion H.
  - simpl. destruct (x =? x') eqn:Heq.
    + reflexivity.
    + apply IH. simpl in H. apply add_spec in H. destruct H.
      * apply Nat.eqb_neq in Heq. inversion H. contradiction.
      * assumption.
Qed.

Lemma in_map_inversion : forall x xs, In x (of_list (map Pro xs)) -> exists y, x = Pro y /\ List.In y xs.
Proof.
  intros x xs H. induction xs as [| x' xs' IH].
  - inversion H.
  - simpl in H. apply add_spec in H. destruct H.
    + exists x'. intuition.
    + specialize (IH H). destruct IH as [y [Hxy Hin]].
      exists y. intuition.
Qed.

(* Under the interpretation defined above, the prover returns counterexamples
   if it returns a non-empty list *)
Lemma counter : forall a b c d (xs : list nat),
    List.In xs (mu a b c d) ->
    ~ sc (of_list (c ++ map Pro a)) (of_list (d ++ map Pro b)) (counter_sem xs).
Proof.
  intros a b c d xs Hin. funelim (mu a b c d).
  - simpl in *. simp mu in Hin. destruct (common a b) eqn:Hab.
    + inversion Hin.
    + inversion Hin as [H | H].
      * subst. unfold sc. unfold not. intros. specialize (H (counter_lhs xs [])).
        unfold Exists in H. destruct H as [x [Hin' Hx]].
        assert (exists x', x = Pro x').
        { apply in_map_inversion in Hin'. destruct Hin' as [y [Hxy Hin']]. exists y. intuition. }
        destruct H as [x' Hx']. subst. simpl in *.
        apply in_of_list_member in Hin'.
        assert (common xs b = true). apply (member_common x'); assumption.
        congruence.
      * contradiction.
  - simpl in *. simp mu in Hin. specialize (H xs Hin). unfold not. intros.
    apply H. apply sc_of_list_comm_right. assumption.
  - simpl in *. simp mu in Hin. specialize (H xs Hin). unfold not. intros Hsc.
    apply drop_falsity in Hsc. intuition.
  - simpl in *. simp mu in Hin. specialize (H xs Hin). unfold not. intros.
    apply H. apply complete_imp_r. assumption.
  - simpl in *. simp mu in Hin. specialize (H xs Hin). unfold not. intros.
    apply H. apply sc_of_list_comm_left. assumption.
  - simpl in *. simp mu in Hin. specialize (H xs Hin). unfold not. intros.
    apply H. apply sc_of_list_comm_right. assumption.
  - simpl in *. simp mu in Hin. specialize (H xs Hin). unfold not. intros Hsc.
    apply drop_falsity in Hsc. intuition.
  - simpl in *. simp mu in Hin. specialize (H xs Hin). unfold not. intros.
    apply H. apply complete_imp_r. assumption.
  - simp mu in Hin. inversion Hin.
  - simpl in *. simp mu in Hin. specialize (H xs Hin). unfold not. intros.
    apply H. apply sc_of_list_comm_right. assumption.
  - simpl in *. simp mu in Hin. specialize (H xs Hin). unfold not. intros Hsc.
    apply drop_falsity in Hsc. intuition.
  - simpl in *. simp mu in Hin. specialize (H xs Hin). unfold not. intros.
    apply H. apply complete_imp_r. assumption.
  - simpl in *. simp mu in Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + specialize (H xs Hin). unfold not. intros Hsc. apply H. apply complete_imp_l in Hsc. intuition.
    + specialize (H0 xs Hin). unfold not. intros Hsc. apply H0. apply complete_imp_l in Hsc. intuition.
  - simpl in *. simp mu in Hin. specialize (H xs Hin). unfold not. intros.
    apply H. apply sc_of_list_comm_right. assumption.
  - simpl in *. simp mu in Hin. specialize (H xs Hin). unfold not. intros Hsc.
    apply drop_falsity in Hsc. intuition.
  - simpl in *. simp mu in Hin. specialize (H xs Hin). unfold not. intros.
    apply H. apply complete_imp_r. assumption.
Qed.

(* Thus the prover must return an empty list for any valid formula *)
Lemma mu_complete : forall a b c d,
    (forall i, sc (of_list (c ++ map Pro a)) (of_list (d ++ map Pro b)) i) -> mu a b c d = [].
Proof.
  intros a b c d H. destruct (mu a b c d) eqn:He.
  - reflexivity.
  - exfalso. specialize counter. intros counter.
    specialize (counter a b c d l). unfold not in counter. apply counter.
    + rewrite He. apply in_eq.
    + apply H.
Qed.

(* Using the equivalence and the results until now, we reach our main theorem:
   The boolean prover returns true exactly when the sequent is provable. *)
Theorem sound_complete' : forall a b c d,
    (forall i, sc (of_list (c ++ map Pro a)) (of_list (d ++ map Pro b)) i) <-> mp a b c d = true.
Proof.
  unfold prover. split.
  - intros. apply mu_mp_eq. apply mu_complete. assumption.
  - intros H. apply mu_mp_eq in H. apply mu_sound. assumption.
Qed.

(* We can also specialize this to single formulas: *)
Lemma sc_semantics : forall i p,
    sc (of_list ([] ++ map Pro [])) (of_list ([p] ++ map Pro [])) i -> semantics i p.
Proof.
  intros i p H. simpl in H. unfold sc in H. unfold Exists in H. unfold For_all in H.
  assert (Hempty: forall x, In x empty -> semantics i x). { intros. inversion H0. }
  specialize (H Hempty). destruct H as [x [Hadd Hx]]. apply add_spec in Hadd. destruct Hadd.
  - subst. assumption.
  - inversion H.
Qed.

(* We thus reach our main result for the final prover:
   The prover for single formulas returns true exactly when the given formula is valid. *)
Corollary sound_complete : forall p, (forall i, semantics i p) <-> prover p = true.
Proof.
  intros p. split.
  - intros H. apply sound_complete'. intros i. unfold sc. simpl.
    intros Hall. unfold For_all in Hall. unfold Exists. exists p; intuition.
  - intros H i. unfold prover in H. apply sc_semantics. apply sound_complete'. assumption.
Qed.

(* We can now extract our final prover to Haskell to integrate it into an application *)
Extraction Language Haskell.

(* To fit into Haskell easily, we translate the Coq definitions of standard concepts
   into the native Haskell equivalents.
   Concretely, we translate list into Haskell lists, bool into Haskell booleans and
   nat into the Int type in Haskell.
   All of this can be set up by importing the following standard translation packages:
 *)
Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInt.

(* We then extract the prover function into a Haskell library module: *)
Extraction "prover/MicroProver.hs" prover.
