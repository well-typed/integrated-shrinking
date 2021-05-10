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

(* fmap *)

Fixpoint fmap (A B : Set) (f : A -> B) (t : Tree A) : Tree B :=
  match t with
    Node x xs => Node (f x) (map (fmap f) xs)
  end.

Lemma fmap_id : forall (A : Set) (t : Tree A),
  fmap id t = t.
Proof.
  intro A ; apply Tree_ind_eq_id ; intros x xs Hxs ; simpl.
  rewrite Hxs ; auto.
Qed.

(* singleton *)

Definition singleton (A : Set) (x : A) : Tree A := Node x nil.

Lemma singleton_fmap : forall (A B : Set) (f : A -> B) (x : A),
  fmap f (singleton x) = singleton (f x).
Proof.
  intros ; simpl ; auto.
Qed.


(* join *)

Fixpoint plug (A : Set) (t : Tree A) (ys : list (Tree A)) : Tree A :=
  match t with
    Node x xs => Node x (map (fun t' => plug t' ys) xs  ++ ys)
  end.

Lemma plug_nil : forall (A : Set) (t : Tree A), plug t nil = t.
Proof.
  intro A.
  apply Tree_ind_eq.
  intros x ts Hts.
  simpl.
  rewrite <- app_nil_end.
  rewrite Hts.
  rewrite map_id; auto.
Qed.

Fixpoint join (A : Set) (t : Tree (Tree A)) : Tree A :=
  match t with
    Node (Node x xs) xss => plug (Node x xs) (map (@join A) xss)
  end.

Lemma join_singleton : forall (A : Set) (t : Tree A),
  join (@singleton (Tree A) t) = t.
Proof.
  destruct t as [x xs] ; simpl.
  rewrite <- app_nil_end.
  replace (map (fun t' => plug t' nil) xs) with (map (fun t' => t') xs).
  - rewrite map_id; auto.
  - apply map_ext.
    intro a; rewrite plug_nil; auto.
Qed.

Lemma join_fmap_singleton : forall (A : Set) (t : Tree A),
  join (fmap (@singleton A) t) = t.
Proof.
  intros A ; apply Tree_ind_eq_id ; intros x xs Hxs ; simpl.
  rewrite map_map.
  rewrite Hxs ; auto.
Qed.


Definition plug_plug_join_eq A (x : Tree A) (ys zs : list (Tree (Tree A))) :=
  plug (plug x (map (@join A) ys)) (map (@join A)  zs)
  = plug x (map (fun y => join (plug y zs)) ys ++ map (@join A) zs).

Definition join_plug_eq A (t : Tree (Tree A)) (ts : list (Tree (Tree A))) :=
  join (plug t ts)
  = plug (join t) (map (@join A) ts).

Lemma plug_plug_map : forall A (x : Tree A) ys zs,
    (forall a, In a ys -> join_plug_eq a zs) ->
    plug_plug_join_eq x ys zs.
Proof.
  intros A f.
  apply (@Tree_ind' A (fun (x : Tree A) => forall ys zs, _ -> plug_plug_join_eq x ys zs)).
  intros x xs Hxs ys zs Hyszs.
  unfold plug_plug_join_eq in *; simpl.
  apply f_equal.
  repeat rewrite app_assoc; rewrite app_inv_tail_iff.
  repeat rewrite map_app.
  repeat rewrite map_map.
  apply f_equal2.
  - apply map_ext_in. intros a Ha. rewrite Hxs; auto.
  - apply map_ext_in. intros a Ha.
    rewrite Hyszs; auto.
Qed.

Lemma join_plug : forall (A : Set) (t : Tree (Tree A)) (ts : list (Tree (Tree A))),
   join (plug t ts) = plug (join t) (map (@join A) ts).
Proof.
  intro A.
  apply (@Tree_ind' (Tree A) (fun (t : Tree (Tree A)) => forall ts, join_plug_eq t ts)).
  intros x xs Hxs ts.
  unfold join_plug_eq; simpl.
  destruct x; simpl; apply f_equal.
  repeat rewrite map_app.
  repeat rewrite map_map.
  repeat rewrite app_assoc.
  apply f_equal2; auto.
  apply f_equal2.
  - apply map_ext_in. intros a0 Ha0.
    rewrite plug_plug_map; auto.
  - apply map_ext_in; intros a0 Ha0.
    unfold join_plug_eq in *.
    apply Hxs; auto.
Qed.

Lemma join_join : forall (A : Set) (t : Tree (Tree (Tree A))),
  @join A (@join (Tree A) t) = @join A (fmap (@join A) t).
Proof.
  intro A; apply Tree_ind_eq ; intros [[x xs] xss] xsss Hxs.
  simpl join in *.
  apply f_equal.
  repeat rewrite map_app.
  repeat rewrite map_map.
  repeat rewrite <- Hxs.
  rewrite app_assoc; apply f_equal2; auto.
  apply f_equal2; apply map_ext_in; intro a.
  - replace (map (fun (t : Tree (Tree (Tree A))) => join (join t)) xsss)
      with (map (@join A) (map (@join (Tree A)) xsss)).
      2: ( rewrite map_map; apply map_ext; auto ).
      rewrite plug_plug_map; auto.
      intros a0 Ha0; apply join_plug.
  - rewrite join_plug.
    rewrite map_map; auto.
Qed.

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

