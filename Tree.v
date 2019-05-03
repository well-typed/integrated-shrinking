(*
 * Proofs of the laws for Applicative and Monad for trees.
 *
 * Edsko de Vries <edsko@well-typed.com>, 2019
 *)

Require Import List.

Set Implicit Arguments.

(*
 * Preliminaries
 *)

Definition o (A B C : Set) (g : B -> C) (f : A -> B) (x : A) := g (f x).

Fact eq_concat : forall (A : Set) (xs xs' ys ys' zs zs' : list A),
  xs = xs' ->
  ys = ys' ->
  zs = zs' ->
  xs ++ ys ++ zs = xs' ++ ys' ++ zs'.
Proof.
  intros A xs xs' ys ys' zs zs' Hxs Hys Hzs.
  rewrite Hxs ; rewrite Hys ; rewrite Hzs ; auto.
Qed.


(*
 * Tree data type proper
 *)

Unset Elimination Schemes.
Inductive Tree (A : Set) : Set :=
  Node : A -> list (Tree A) -> Tree A.
Set Elimination Schemes.

(*
 * Custom induction principle
 *
 * Since Tree does contain Tree subterms immediately,
 * the derived induction principle is not useful.
 *)

Fixpoint Tree_ind
    (A      : Set)
    (P      : Tree A -> Prop)
    (Q      : list (Tree A) -> Prop)
    (HQnil  : Q nil)
    (HQcons : forall (t : Tree A) (ts : list (Tree A)),
                P t -> Q ts -> Q (cons t ts))
    (HP     : forall (x : A) (xs : list (Tree A)),
                Q xs -> P (Node x xs))
    (t      : Tree A) : P t :=
  match t with
  | Node x xs =>
      HP x xs (
        (fix inner_ind (l : list (Tree A)) : Q l :=
           match l with
           | nil        => HQnil
           | cons t' l' => HQcons t' l' (Tree_ind P Q HQnil HQcons HP t') (inner_ind l')
           end) xs)
  end.

Corollary Tree_ind' :
  forall
    (A  : Set)
    (P  : Tree A -> Prop)
    (HP : forall (x : A) (ts : list (Tree A)),
            (forall (t' : Tree A), (In t' ts -> P t')) -> P (Node x ts))
    (t  : Tree A), P t.
Proof.
  intros A P HP.
  apply Tree_ind with (Q := fun ts =>
    forall (t' : Tree A), In t' ts -> P t') ; auto.
(* Case for nil *)
  intros t' Ht' ; inversion Ht'.
(* Case for cons *)
  intros t' ts Ht' IH t'' Ht''.
  inversion Ht'' as [Hin |] ; auto.
  rewrite <- Hin ; auto.
Qed.

Corollary Tree_ind_eq :
  forall
    (A B : Set)
    (f g : Tree A -> Tree B)
    (H : forall (x : A) (xs : list (Tree A)),
      map f xs = map g xs -> f (Node x xs) = g (Node x xs)),
    forall (t : Tree A), f t = g t.
Proof.
  intros A B f g H.
  apply Tree_ind' ; intros x ts Hts.
  apply H ; apply map_ext_in ; auto.
Qed.

Corollary Tree_ind_eq_id :
  forall
    (A : Set)
    (f : Tree A -> Tree A)
    (H : forall (x : A) (xs : list (Tree A)),
      map f xs = xs -> f (Node x xs) = Node x xs),
    forall (t : Tree A), f t = t.
Proof.
  intros A f H.
  change (forall t : Tree A, f t = id t).
  apply Tree_ind_eq ; intros x xs Hxs.
  change (f (Node x xs) = Node x xs).
  apply H.
  rewrite <- map_id.
  apply Hxs.
Qed.

(*
 * Functions on trees
 *)

Fixpoint fmap (A B : Set) (f : A -> B) (t : Tree A) : Tree B :=
  match t with
    Node x xs => Node (f x) (map (fmap f) xs)
  end.

Definition singleton (A : Set) (x : A) : Tree A := Node x nil.

Fixpoint join (A : Set) (t : Tree (Tree A)) : Tree A :=
  match t with
    Node (Node x xs) xss => Node x (xs ++ map (@join A) xss)
  end.

Fixpoint ap (A B : Set) (fs : Tree (A -> B)) : Tree A -> Tree B :=
  match fs with
    Node f fs' => fix ap_inner (xs : Tree A) :=
      match xs with
        Node x xs' => Node (f x) (
                map (fun f' => ap f' xs) fs'
             ++ map ap_inner xs'
          )
      end
  end.

(* Definition with inner fix is a bit confusing. This fact clarifies. *)
Fact ap_def : forall
    (A B : Set)
    (f : A -> B) (fss : list (Tree (A -> B)))
    (x : A)      (xss : list (Tree A)),
    ap (Node f fss) (Node x xss)
  = Node (f x) (map (fun f' => ap f' (Node x xss)) fss
             ++ map (fun x' => ap (Node f fss) x') xss).
Proof.
  auto.
Qed.

(*
 * Examples
 *)

Example t1 : Tree nat := Node 1 (Node 2 nil :: Node 3 nil :: nil).
Example t2 : Tree nat := Node 4 (Node 5 nil :: Node 6 nil :: nil).
Example t3 : Tree (nat * nat) := ap (fmap (fun x y => (x, y)) t1) t2.

Compute t3.

(*
 * Proofs about singleton
 *)

Lemma singleton_fmap : forall (A B : Set) (f : A -> B) (x : A),
  fmap f (singleton x) = singleton (f x).
Proof.
  intros ; simpl ; auto.
Qed.

(*
 * Proofs about fmap
 *)

Lemma fmap_id : forall (A : Set) (t : Tree A),
  fmap id t = t.
Proof.
  intro A ; apply Tree_ind_eq_id ; intros x xs Hxs ; simpl.
  rewrite Hxs ; auto.
Qed.

(*
 * Proofs about join
 *)

Lemma join_singleton : forall (A : Set) (t : Tree A),
  join (@singleton (Tree A) t) = t.
Proof.
  destruct t as [x xs] ; simpl.
  rewrite <- app_nil_end ; auto.
Qed.

Lemma join_fmap_singleton : forall (A : Set) (t : Tree A),
  join (fmap (@singleton A) t) = t.
Proof.
  intros A ; apply Tree_ind_eq_id ; intros x xs Hxs ; simpl.
  rewrite map_map.
  rewrite Hxs ; auto.
Qed.

Lemma join_join : forall (A : Set) (t : Tree (Tree (Tree A))),
  @join A (@join (Tree A) t) = @join A (fmap (@join A) t).
Proof.
  intros A ; apply Tree_ind_eq ; intros [[x xs] xss] xsss Hxs ; simpl.
  rewrite map_app ; rewrite <- app_assoc ; repeat rewrite map_map.
  rewrite Hxs ; auto.
Qed.

(*
 * To illustrate that the monad laws do not pin down the ordering,
 * we define a variant on join that uses the opposite ordering and
 * prove the laws again.
 *)

Fixpoint join' (A : Set) (t : Tree (Tree A)) : Tree A :=
  match t with
    Node (Node x xs) xss => Node x (map (@join' A) xss ++ xs)
  end.

Lemma join'_singleton : forall (A : Set) (t : Tree A),
  join' (@singleton (Tree A) t) = t.
Proof.
  destruct t ; auto.
Qed.

Lemma join'_fmap_singleton : forall (A : Set) (t : Tree A),
  join' (fmap (@singleton A) t) = t.
Proof.
  intros A ; apply Tree_ind_eq_id ; intros x xs Hxs ; simpl.
  rewrite map_map ; rewrite <- app_nil_end.
  rewrite Hxs ; auto.
Qed.

Lemma join'_join' : forall (A : Set) (t : Tree (Tree (Tree A))),
  @join' A (@join' (Tree A) t) = @join' A (fmap (@join' A) t).
Proof.
  intros A ; apply Tree_ind_eq ; intros [[x xs] xss] xsss Hxs ; simpl.
  rewrite map_app ; rewrite <- app_assoc ; repeat rewrite map_map.
  rewrite Hxs ; auto.
Qed.

(*
 * Proofs about ap
 *)

Lemma ap_singleton_left : forall (A B : Set) (f : A -> B) (xs : Tree A),
  ap (singleton f) xs = fmap f xs.
Proof.
  intros A B f ; apply Tree_ind_eq ; intros x xs Hxs ; simpl.
  rewrite <- Hxs ; auto.
Qed.

Lemma ap_singleton_right : forall (A B : Set) (x : A) (fs : Tree (A -> B)),
  ap fs (singleton x) = fmap (fun f => f x) fs.
Proof.
  intros A B x ; apply Tree_ind_eq ; intros f fs Hfs ; simpl.
  rewrite <- app_nil_end.
  rewrite <- Hfs ; auto.
Qed.

Lemma ap_homomorphism : forall (A B : Set) (f : A -> B) (x : A),
  ap (singleton f) (singleton x) = singleton (f x).
Proof.
  intros ; repeat rewrite ap_singleton_left.
  rewrite singleton_fmap ; auto.
Qed.

Lemma ap_id : forall (A : Set) (t : Tree A),
  ap (singleton (@id A)) t = t.
Proof.
  intros ; rewrite ap_singleton_left.
  rewrite fmap_id ; auto.
Qed.

Lemma ap_interchange : forall (A B : Set) (fs : Tree (A -> B)) (x : A),
  ap fs (singleton x) = ap (singleton (fun f' => f' x)) fs.
Proof.
  intros.
  rewrite ap_singleton_left.
  rewrite ap_singleton_right.
  auto.
Qed.

Lemma ap_composition :
  forall (B C : Set) (gs : Tree (B -> C)),
  forall (A : Set) (fs : Tree (A -> B)),
  forall (xs : Tree A),
  ap (ap (fmap (@o A B C) gs) fs) xs = ap gs (ap fs xs).
Proof.
  intros B C gs.
  eapply Tree_ind' with (t := gs) ; intros g gss Hgss A fs.
  eapply Tree_ind' with (t := fs) ; intros f fss Hfss xs.
  eapply Tree_ind' with (t := xs) ; intros x xss Hxss.
(* Simplify RHS *)
  rewrite (ap_def f).
  rewrite (ap_def g).
(* Simplify LHS *)
  simpl fmap.
  rewrite (ap_def (o g)).
  rewrite (ap_def (o g f)).
(* Root of the tree now simple *)
  f_equal ; auto.
(* Remains to show the subtrees are the same *)
  repeat rewrite map_app.
  repeat rewrite map_map.
  rewrite <- app_assoc.
  rewrite <- ap_def.
  apply eq_concat ; apply map_ext_in.
(* First sublist *)
  intros gs' Hgs' ; apply Hgss ; apply Hgs'.
(* Second sublist *)
  intros fs' Hfs' ; apply Hfss ; apply Hfs'.
(* Third sublist *)
  intros xs' Hxs'.
  rewrite <- Hxss ; auto.
  simpl fmap.
  rewrite ap_def ; rewrite map_map ; auto.
Qed.

Lemma ap_composition' : forall (A B C : Set) (u : Tree (B -> C)) (v : Tree (A -> B)) (w : Tree A),
  ap (ap (ap (singleton (@o A B C)) u) v) w = ap u (ap v w).
Proof.
  intros.
  rewrite ap_singleton_left.
  apply ap_composition.
Qed.

(*
 * Just like join, ap is free to change the order as well
 *)

Fixpoint ap' (A B : Set) (fs : Tree (A -> B)) : Tree A -> Tree B :=
  match fs with
    Node f fs' => fix ap_inner (xs : Tree A) :=
      match xs with
        Node x xs' => Node (f x) (
                map ap_inner xs'
             ++ map (fun f' => ap' f' xs) fs'
          )
      end
  end.

(* Definition with inner fix is a bit confusing. This fact clarifies. *)
Fact ap'_def : forall
    (A B : Set)
    (f : A -> B) (fss : list (Tree (A -> B)))
    (x : A)      (xss : list (Tree A)),
    ap' (Node f fss) (Node x xss)
  = Node (f x) (map (fun x' => ap' (Node f fss) x') xss
             ++ map (fun f' => ap' f' (Node x xss)) fss).
Proof.
  auto.
Qed.

Lemma ap'_singleton_left : forall (A B : Set) (f : A -> B) (xs : Tree A),
  ap' (singleton f) xs = fmap f xs.
Proof.
  intros A B f ; apply Tree_ind_eq ; intros x xs Hxs ; simpl.
  rewrite <- app_nil_end.
  rewrite <- Hxs ; auto.
Qed.

Lemma ap'_singleton_right : forall (A B : Set) (x : A) (fs : Tree (A -> B)),
  ap' fs (singleton x) = fmap (fun f => f x) fs.
Proof.
  intros A B x ; apply Tree_ind_eq ; intros f fs Hfs ; simpl.
  rewrite <- Hfs ; auto.
Qed.

Lemma ap'_homomorphism : forall (A B : Set) (f : A -> B) (x : A),
  ap' (singleton f) (singleton x) = singleton (f x).
Proof.
  intros ; repeat rewrite ap'_singleton_left.
  rewrite singleton_fmap ; auto.
Qed.

Lemma ap'_id : forall (A : Set) (t : Tree A),
  ap' (singleton (@id A)) t = t.
Proof.
  intros ; rewrite ap'_singleton_left.
  rewrite fmap_id ; auto.
Qed.

Lemma ap'_interchange : forall (A B : Set) (fs : Tree (A -> B)) (x : A),
  ap' fs (singleton x) = ap' (singleton (fun f' => f' x)) fs.
Proof.
  intros.
  rewrite ap'_singleton_left.
  rewrite ap'_singleton_right.
  auto.
Qed.

Lemma ap'_composition :
  forall (B C : Set) (gs : Tree (B -> C)),
  forall (A : Set) (fs : Tree (A -> B)),
  forall (xs : Tree A),
  ap' (ap' (fmap (@o A B C) gs) fs) xs = ap' gs (ap' fs xs).
Proof.
  intros B C gs.
  eapply Tree_ind' with (t := gs) ; intros g gss Hgss A fs.
  eapply Tree_ind' with (t := fs) ; intros f fss Hfss xs.
  eapply Tree_ind' with (t := xs) ; intros x xss Hxss.
(* Simplify RHS *)
  rewrite (ap'_def f).
  rewrite (ap'_def g).
(* Simplify LHS *)
  simpl fmap.
  rewrite (ap'_def (o g)).
  rewrite (ap'_def (o g f)).
(* Root of the tree now simple *)
  f_equal ; auto.
(* Remains to show the subtrees are the same *)
  repeat rewrite map_app.
  repeat rewrite map_map.
  rewrite <- app_assoc.
  rewrite <- ap'_def.
  apply eq_concat ; apply map_ext_in.
(* First sublist *)
  intros xs' Hxs'.
  rewrite <- Hxss ; auto.
  simpl fmap.
  rewrite ap'_def ; rewrite map_map ; auto.
(* Second sublist *)
  intros fs' Hfs' ; apply Hfss ; apply Hfs'.
(* Third sublist *)
  intros gs' Hgs' ; apply Hgss ; apply Hgs'.
Qed.

Lemma ap'_composition' : forall (A B C : Set) (u : Tree (B -> C)) (v : Tree (A -> B)) (w : Tree A),
  ap' (ap' (ap' (singleton (@o A B C)) u) v) w = ap' u (ap' v w).
Proof.
  intros.
  rewrite ap'_singleton_left.
  apply ap'_composition.
Qed.
