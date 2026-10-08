From mathcomp Require Import all_ssreflect.
Require Import preamble.
From mathcomp Require boolp.
Require Import hierarchy monad_lib  fail_lib state_lib.
Require Import monad_transformer symfingraph.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Section extra_rules.
Variable M : unionFailMonad.
Local Notation I := hierarchy.UnionFind.I.

Lemma findunionl i j : (find i >>= union ^~ j) ≈ @union M i j.
Proof. by setoid_rewrite union_sym; rewrite findunion. Qed.

Lemma finddup A i m :
  (find i >>= fun x => find x >>= m x : M A) ≈ find i >>= fun x => m x x.
Proof.
rewrite -findfind.
rewrite -[eqvLHS](findfind _ i (fun i1 i2 => find i2 >>= m i1)).
rewrite [eqvRHS]findC.
rewrite -{3}(bindskipf (find i)) -(union_refl i) -findunionfind !bindA.
setoid_rewrite union_refl.
setoid_rewrite bindretf.
rewrite findC.
by setoid_rewrite (findC _ i _ m).
Qed.

Lemma uniondup i j : @union M i j >> union i j ≈ union i j.
Proof.
  setoid_rewrite <-findunionl at 2.
  setoid_rewrite <-bindA.
  rewrite unionfind  bindA.
  setoid_rewrite findunionl.
  setoid_rewrite union_refl.
  by rewrite bindmskip. 
Qed.

Lemma union_eq a i j: @find M a ≈ find j -> @union M i a ≈ union i j.
Proof. by rewrite -findunion -findunion; apply: bindmeqv. Qed.

Lemma find_lookup A i (m : M A) : (find i >> m) ≈ m.
Proof. by rewrite -(bindskipf m) -{2}(findskip i) bindA. Qed.

End extra_rules.

Section equivLaws.
Variable M : unionFailMonad.
Local Notation I := hierarchy.UnionFind.I.

(* TODO M more generic + move into lib*)
Lemma bind_eqv_guard [A : UU0] [b : bool] [m1 m2 : M A]:
  (b -> m1 ≈ m2) -> guard b >> m1 ≈ guard b >> m2.
Proof.
  case: b => H.
  - by rewrite guardT !bindskipf H.
  - by rewrite guardF !bindfailf.
Qed.
End equivLaws.

Section correction_proof.
Variable  M : unionFailMonad.
Local Notation I := hierarchy.UnionFind.I.

Section findchk.
Definition findchk A a a' (k : _ -> M A) : M A :=
  find a >>= fun x => guard (a' == x) >> k x.

Import Morphisms.
#[global] Add Parametric Morphism A : (@findchk A) with signature
  eq ==> eq ==> (Morphisms.pointwise_relation nat (@eqvM M A)) ==> (@eqvM M A)
  as findchk_mor_eqvM.
Proof.
move => x y f g Hfg; rewrite /findchk.
apply: bindfeqv => a.
by setoid_rewrite (Hfg a).
Qed.
End findchk.

Lemma remember_find  B (a : I) (k : I-> M B) :
  (find a >>= k) ≈ (find a >>= fun a' => findchk a a' (fun=> k a')).
Proof.
  by rewrite findfind; apply: bindfeqv => {}a'; rewrite eqxx guardT bindskipf.
Qed.

Lemma guardfindC A b a (f: I -> M A): 
  @guard M b >> (find a >>= f) ≈
  find a >>= fun x => guard b >> f x.
Proof.
case: b.
- rewrite guardT bindskipf.
  by under [eqvRHS]eq_bind do rewrite bindskipf.
- rewrite guardF !bindfailf.
  under [eqvRHS]eq_bind do rewrite bindfailf.
  by rewrite find_lookup.
Qed.

Lemma findchkfindC B a a' b (k : I -> I-> M B) :
  (findchk a a' (fun x => find b >>= k ^~ x)) ≈
  (find b >>= fun v => findchk a a' (k v)).
Proof.
by rewrite [eqvLHS](bindfeqv (fun a => guardfindC (a' == a) b _)) findC.
Qed.

Lemma guardC A b1 b2 (m : M A) :
  guard b1 >> (guard b2 >> m) ≈ guard b2 >> (guard b1 >> m).
Proof. by rewrite -!bindA -guard_and andbC guard_and. Qed.

Lemma findchkfind A a a' (k : I -> M A) :
  findchk a a' (fun=> find a' >>= k) ≈ findchk a a' k.
Proof.
transitivity (findchk a a' (fun x => find x >>= k)).
  by apply: bindfeqv => x; apply: bind_eqv_guard => /eqP ->.
rewrite [eqvLHS](bindfeqv (fun x => guardfindC _ _ _)).
rewrite -(findfind _ _ (fun x y => _ >>= fun z => guard (a' == x) >> _)).
by rewrite (bindfeqv (fun x => finddup _ _)) findfind.
Qed.

Ltac normalize_bindA :=
  rewrite ?(bindA,bindretf);
  try (under eq_bind => ?; [normalize_bindA; over |]).

Lemma add_neqfind A a a' i i' (m : M A) : 
  a' != i' ->
  findchk a a' (fun=> findchk i i' (fun=> m)) ≈
  findchk a a' (fun=> findchk i i' (fun=> neqfind a' i' >> m)).
Proof.
move=> Hdiff.
symmetry.
rewrite /findchk neqfindE.
normalize_bindA.
setoid_rewrite (findchkfindC i).
rewrite [eqvLHS]findchkfind.
apply: bindfeqv => r.
apply: bind_eqv_guard => /eqP <-.
rewrite findchkfind.
apply: bindfeqv => i1.
apply: bind_eqv_guard => /eqP <-.
by rewrite /comp Hdiff guardT bindskipf.
Qed.

Lemma findchkC A a a' j j' (k : I -> I -> M A) :
  findchk a a' (fun x => findchk j j' (k x)) ≈
  findchk j j' (fun y => findchk a a' (k ^~ y)).
Proof.
rewrite [eqvLHS](bindfeqv (fun x => guardfindC (a' == x) _ _)) findC.
apply: bindfeqv => j0.
case: (j' == j0).
  rewrite guardT !bindskipf.
  apply: bindfeqv => a0.
  by rewrite bindskipf.
symmetry.
rewrite guardF !bindfailf -{1}(find_lookup a fail).
apply: bindfeqv => a0.
case: (a' == a0).
- by rewrite guardT bindskipf bindfailf.
- by rewrite guardF bindfailf.
Qed.

Lemma findchk_neqfindC A i i' a j (m : M A) :
  findchk i i' (fun=> neqfind a j >> m) ≈
  neqfind a j >> findchk i i' (fun=> m).
Proof.
  rewrite neqfindE.
  normalize_bindA.
  symmetry.
  normalize_bindA.
  setoid_rewrite (guardfindC _ i).
  setoid_rewrite (findC _ _ i).
  rewrite findC.
  apply: bindfeqv => i0.
  do 2 (rewrite guardfindC; apply: bindfeqv => ?).
  by rewrite guardC.
Qed.

Lemma union_axiom_neqcase a' a b' b i' i j' j : 
  a' != b' -> a' != i' -> a' != j' ->
  findchk b b' (fun=> findchk a a'
   (fun=> findchk j j' (fun=> findchk i i' (fun=> union i' j' >> Ret false)))) ≈
  findchk b b' (fun=> findchk a a'
    (fun=> findchk j j' (fun=> findchk i i' (fun=> union i' j' >>
       (find b' >>= fun y => find a' >>= fun x => Ret (x == y)))))).
Proof.
  move=> Hab Hai Haj.
  setoid_rewrite (findchkC a a' j j').
  setoid_rewrite (add_neqfind a i _ Hai).
  do 2 setoid_rewrite (findchkC j j').
  setoid_rewrite (findchkC a a' i i').
  do 2 setoid_rewrite findchk_neqfindC.
  setoid_rewrite (add_neqfind a j _ Haj).
  (*use neqfind to exchange find and union*)
  do 2 setoid_rewrite <-findchk_neqfindC.
  setoid_rewrite (findC _ b' a').
  symmetry.
  rewrite -3![X in findchk j j' (fun=> X)]bindA.
  setoid_rewrite findunion_neq.
  rewrite !bindA.
  (* supress neqfind once used*)
  do 8 setoid_rewrite findchk_neqfindC.
  do 2 apply: bindfeqv => _.
  (* reunite find a and find a' *)
  setoid_rewrite (findchkC a).
  setoid_rewrite findchkfind.
  (*case analysis*)
  case Hb: ( (b' == i') || (b' == j')).
  - case/orP: Hb => [/eqP Hbi | /eqP Hbj].
    + rewrite Hbi.
      apply: bindfeqv => b0.
      apply: bind_eqv_guard => _ {b0}.
      (*test to see*)
      do 2 setoid_rewrite (findchkC i).
      setoid_rewrite (findchkC j).
      apply: bindfeqv => a0.
      apply: bind_eqv_guard => /eqP <- {a0}.
      setoid_rewrite <-(findunion_eq i' j').
      normalize_bindA.
      setoid_rewrite (findC _ i' j').
      symmetry.
      normalize_bindA.
      setoid_rewrite (findC _ i' j').
      setoid_rewrite (findchkC j).
      setoid_rewrite (findchkfind j j').
      setoid_rewrite (findchkfindC j).
      rewrite !findchkfind.
      apply: bindfeqv => i1.
      apply: bind_eqv_guard => /eqP <- {i1}.
      apply: bindfeqv => j1.
      apply: bind_eqv_guard => /eqP <- {j1}.
      apply: bindfeqv => _.
      setoid_rewrite guardfindC.
      rewrite findfind.
      apply: bindfeqv => i2.
      apply: bind_eqv_guard => /orP[] /eqP <-.
      - by rewrite (negbTE Hai).
      - by rewrite (negbTE Haj).
    + rewrite Hbj.
      apply: bindfeqv => b0.
      apply: bind_eqv_guard => _ {b0}.
      do 2 setoid_rewrite (findchkC i).
      setoid_rewrite (findchkC j).
      apply: bindfeqv => a0.
      apply: bind_eqv_guard => /eqP <- {a0}.
      setoid_rewrite union_sym.
      setoid_rewrite <-(findunion_eq j' i').
      normalize_bindA.
      symmetry.
      normalize_bindA.
      setoid_rewrite (findchkC j).
      setoid_rewrite (findchkfind j j').
      setoid_rewrite (findchkfindC j).
      rewrite !findchkfind.
      apply: bindfeqv => i1.
      apply: bind_eqv_guard => /eqP <- {i1}.
      apply: bindfeqv => j1.
      apply: bind_eqv_guard => /eqP <- {j1}.
      apply: bindfeqv => _.
      setoid_rewrite guardfindC.
      rewrite findfind.
      apply: bindfeqv => j2.
      apply: bind_eqv_guard=> /orP[] /eqP <-.
      - by rewrite (negbTE Haj).
      - by rewrite (negbTE Hai).
  - case/norP: Hb => Hbi Hbj.
    setoid_rewrite (findchkC j).
    (* now we do the same as we did with a in the first part of the proof but with b*)
    do 2 setoid_rewrite (findchkC i).
    do 2 setoid_rewrite (findchkC b).
    apply: bindfeqv => a0.
    apply: bind_eqv_guard => /eqP <-.
    setoid_rewrite (add_neqfind  _ _ _ Hbi).
    do 3 setoid_rewrite findchk_neqfindC.
    setoid_rewrite (findchkC b).
    do 2 setoid_rewrite (findchkC j).
    setoid_rewrite (add_neqfind _ _ _ Hbj).
    do 3 setoid_rewrite <-(findchk_neqfindC _ _ b' i').
    rewrite -3![X in findchk j j' (fun=> X)]bindA.
    setoid_rewrite findunion_neq.
    rewrite !bindA.
    do 6 setoid_rewrite findchk_neqfindC.
    do 2 apply: bindfeqv => _.
    setoid_rewrite (findchkC b).
    setoid_rewrite findchkfind.
    apply: bindfeqv => i0.
    apply: bind_eqv_guard => _ {i0}.
    apply: bindfeqv => j0.
    apply: bind_eqv_guard => _ {j0}.
    apply: bindfeqv => b0.
    apply: bind_eqv_guard => /eqP <-.
    by rewrite (negbTE Hab).
Qed.

Lemma union_classes (i j a b : I):
 union i j >> eqfind M a b ≈
 find a >>= fun a' => find b >>= fun b' =>
 find i >>= fun i' => find j >>= fun j' => union i' j' >>
 Ret ((a' == b') || ((a' == i') && (b' == j')) || ((a' == j') && (b' == i'))).
Proof.
  setoid_rewrite <-(findunionl M i j).
  have -> : find i >>= union^~ j ≈ find i >>= fun i' => find j >>= union i'
    by move=>*; apply: bindfeqv => i'; rewrite findunion.
  rewrite bindA.
  setoid_rewrite (findC _ b i).
  setoid_rewrite (findC _ a i).
  rewrite [in eqvLHS](remember_find i) [in eqvRHS](remember_find i).
  apply: bindfeqv => i'.
  rewrite !bindA.
  setoid_rewrite (findC _ b j).
  setoid_rewrite (findC _ a j).
  do 2 (rewrite findchkfindC (remember_find j);symmetry).
  apply: bindfeqv=>{}j'.
  rewrite -bindA.
  setoid_rewrite <-findunionfind.
  rewrite bindA.
  do 2 setoid_rewrite (findchkfindC _ _ a).
  under eq_bind do rewrite bindA.
  transitivity
    (@find M a >>= fun a1 => findchk j j'
      (fun x => findchk i i' (fun y => union i' j' >>
      (find b >>= fun b' => find a1 >>= fun a' => Ret (a' == b'))))).
    by setoid_rewrite (findC _ b).
  under eq_bind do rewrite -bindA.
  setoid_rewrite <-findunionfind.
  normalize_bindA.
  do 2 setoid_rewrite (findchkfindC _ _ b).
  rewrite [in eqvLHS]remember_find [in eqvRHS]remember_find.
  apply: bindfeqv => a'.
  rewrite /(findchk a).
  setoid_rewrite guardfindC.
  rewrite !(findC _ _ b).
  rewrite [in eqvLHS]remember_find [in eqvRHS]remember_find.
  apply: bindfeqv => b'.
  rewrite -!/(findchk a a' _).
  case Hb: ((a' == b') || (a' == i') && (b' == j') || (a' == j') && (b' == i')).
  - do 4 (apply: bindfeqv => ?; apply: bind_eqv_guard => _).
    case /orP: Hb => [/orP[] |].
    + move/eqP ->.
      apply: bindfeqv => _.
      rewrite findfind.
      under eq_bind do rewrite eqxx.
      by rewrite find_lookup.
    + case/andP => /eqP -> /eqP ->.
      rewrite -bindA -unionfind bindA.
      apply: bindfeqv => _.
      rewrite findfind.
      under eq_bind do rewrite eqxx.
      by rewrite find_lookup.
    + case/andP => /eqP -> /eqP ->.
      rewrite -bindA unionfind bindA.
      apply: bindfeqv => _.
      rewrite findfind.
      under eq_bind do rewrite eqxx.
      by rewrite find_lookup.
  - case /norP: Hb => /norP [Hb0].
    case /boolP: (a' == i') => Hai /= Hbj;
    case /boolP : (a' == j') => Haj /= Hbi.
    + rewrite !(findchkC b b' a a' _).
      rewrite union_axiom_neqcase //; last by rewrite eq_sym.
      setoid_rewrite (findC _ b' a' _).
      do 11 apply/bindfeqv => ?.
      by rewrite eq_sym.
    + have Ha2 : (b' != i') by move /eqP in Hai;rewrite -Hai eq_sym.
      rewrite !(findchkC b b' a a' _).
      rewrite union_axiom_neqcase //; last by rewrite eq_sym.
      setoid_rewrite (findC _ b' a' _).
      do 11 apply/bindfeqv => ?.
      by rewrite eq_sym.    
    + have Hb3 : (b' != j') by move /eqP in Haj;rewrite -Haj eq_sym.
      rewrite !(findchkC b b' a a' _).
      rewrite union_axiom_neqcase //; last by rewrite eq_sym.
      setoid_rewrite (findC _ b' a' _).
      do 11 apply/bindfeqv => ?.
      by rewrite eq_sym.
    + by rewrite union_axiom_neqcase.
Qed.

Definition union_iter (l : seq (I*I)) : M unit :=
  foldM (fun _  p => union p.1 p.2) tt l.


Lemma foldM_rcons R T (f : R -> T -> M R) x s z :
  foldM f x (rcons s z) = foldM f x s >>= f ^~ z.
Proof.
elim: s x => [|y s IH] /= x.
  by rewrite bindmret bindretf.
rewrite bindA; exact: eq_bind.
Qed.

(*
Definition find_pairs (l : seq (I * I)) : M (seq (I * I)) :=
  foldM (fun l '(a,b) =>
           find a >>= fun a' => find b >>= fun b' => Ret (rcons l (a',b')))
        nil l.

Lemma size_find_pairs l :
  find_pairs l = find_pairs l >>= assert (fun l' => size l' == size l).
Proof.
rewrite /find_pairs.
rewrite -{3}(cats0 l).
elim: l nil => [| [i j] l IH] nl /=.
  by rewrite bindretf assertE eqxx bindretf.
rewrite !bindA.
apply: eq_bind => i'.
rewrite !bindA.
apply: eq_bind => j'.
rewrite !bindretf [LHS]IH.
apply: eq_bind => l'.
by rewrite !assertE !size_cat size_rcons addnS.
Qed.
*)

Fixpoint mapM_tuple (s : monad) A B n (f : A -> s B) (l : n.-tuple A) :
  s (n.-tuple B).
revert l; case n.
  move=> _.
  exact (Ret [tuple]).
move=> m [] [] // a l /= Hsz.
refine (f a >>= fun b => mapM_tuple s A B m f (Tuple Hsz) >>= fun l' => _).
exact (Ret [tuple of b :: l']).
Defined.

Lemma mapM_tuple_cat (s : monad) A B n m (f : A -> s B) (l1 : n.-tuple A) (l2 : m.-tuple A) :
  (mapM_tuple f [tuple of l1 ++ l2]) =
  (do l1' <- mapM_tuple f l1; do l2' <- mapM_tuple f l2;
                              Ret [tuple of l1' ++ l2'])%Do.
Proof.
elim: n l1 => [[] [] //= H0 | n IH [] [] // a' l1 Hl].
  rewrite bindretf /=.
  under eq_bind => l2'. rewrite (_ : Ret _ = Ret l2'); first over.
    congr Ret. exact: val_inj.
  rewrite bindmret.
  congr mapM_tuple; exact: val_inj.
have Hl' : size l1 == n by [].
have -> : [tuple of Tuple Hl ++ l2] = [tuple of a' :: Tuple Hl' ++ l2].
  exact: val_inj.
rewrite /= bindA.
apply: eq_bind => b' /=.
rewrite bindA.
under [RHS]eq_bind do rewrite bindretf.
rewrite (_ : Tuple _ = [tuple of Tuple Hl' ++ l2]); last by exact: val_inj.
rewrite IH bindA /=.
under eq_bind do rewrite bindA.
under eq_bind do under eq_bind do rewrite bindretf /=.
congr (mapM_tuple _ _ >>= _).
  exact: val_inj.
apply: boolp.funext => l1'.
apply: eq_bind => l2'.
congr Ret; exact: val_inj.
Qed.

Lemma mapM_tuple_rcons (s : monad) A B n (f : A -> s B) (l : n.-tuple A) a :
  (mapM_tuple f [tuple of rcons l a]) =
  (do l' <- mapM_tuple f l; do b <- f a; Ret [tuple of rcons l' b])%Do.
Proof.
Abort.

Definition find_pairs n : n.-tuple (I * I) -> M (n.-tuple (I * I)) :=
  mapM_tuple (fun '(i,j) => do i' <- find i; do j' <- find j; Ret (i',j'))%Do.

Lemma find_pairsC A n a (l : n.-tuple _) (k : _ -> _ -> M A) :
  (find a >>= fun a' => find_pairs l >>= k a') ≈
  (find_pairs l >>= fun l' => find a >>= k ^~ l').
Proof.
rewrite /find_pairs.
elim: n l k => [[] [] //= H0 | n IH [] [] //= [i j] l Hl] k.
  rewrite bindretf.
  by under eq_bind do rewrite bindretf.
normalize_bindA.
rewrite findC.
setoid_rewrite (findC _ a).
setoid_rewrite IH.
symmetry.
by normalize_bindA.
Qed.

Lemma find_pairs_dup A n (l : n.-tuple _) (k : _ -> _ -> M A) :
  (find_pairs l >>= fun l' => find_pairs l' >>= k l') ≈
  (find_pairs l >>= fun l' => k l' l').
Proof.
rewrite /find_pairs.
elim: n l k => [[] [] //= H0 | n IH [] [] //= [i j] l Hl] k.
  by rewrite !bindretf.
normalize_bindA.
rewrite -!/(find_pairs _).
do 2 setoid_rewrite <-find_pairsC.
rewrite findC.
setoid_rewrite finddup.
rewrite findC.
setoid_rewrite finddup.
rewrite -!/(@find_pairs n) /= in IH *.
under eq_bind do under eq_bind do under eq_bind => l' do
  have -> : Tuple (valP l') = l' by exact: val_inj.
apply: bindfeqv => i'.
normalize_bindA.
symmetry.
normalize_bindA.
apply: bindfeqv => j'.
by rewrite -(IH (Tuple Hl) (fun x y => k [tuple of _ :: x] [tuple of _ :: y])).
Qed.

Lemma find_union_iter_find (l : seq (I * I)) u :
  (find u >>= fun v => union_iter l >> find v) ≈ (union_iter l >> find u).
Proof.
elim/last_ind: l => [| l [i j] IH].
  rewrite /union_iter /= bindretf.
  under eq_bind do rewrite bindretf.
  have := finddup u (fun x y => Ret y : M I).
  rewrite bindmret => Hdup.
  rewrite -[eqvRHS]Hdup.
  apply: bindfeqv => v.
  by rewrite bindmret.
rewrite /union_iter /= foldM_rcons /= !bindA.
under eq_bind do rewrite bindA.
setoid_rewrite <-findunionfind.
rewrite -[eqvRHS]bindA -IH.
rewrite bindA.
apply: bindfeqv => v.
by rewrite bindA.
Qed.

Lemma union_iteration n (l : n.-tuple (I*I)) a b :
  (union_iter l >> eqfind M a b) ≈
  (find_pairs l >>= fun l => find a >>= fun a' => find b >>= fun b' =>
   union_iter l >> Ret (exists_path l a' b')).
Proof.
elim: n l a b => [[] [] //= H0 | n IH [l Hl]] a b /=.
  rewrite /union_iter bindretf /exists_path.
  normalize_bindA.
  apply: bindfeqv => a'.
  apply: bindfeqv => b'.
  rewrite (_ : [exists _, _] = (a' == b')) //.
  apply/existsP => /=.
  case: ifP => ab.
    by exists [::].
  case => -[] [] //=.
  by rewrite /is_path_witness /= ab.
case: l Hl => // c l.
(* reverse *)
rewrite (lastI c l) -cats1 -addn1 => Hl.
rewrite /union_iter.
rewrite {1}cats1 foldM_rcons -/(union_iter _) bindA.
setoid_rewrite union_classes.
have Hl' : size (belast c l) == n by rewrite cats1 size_rcons addn1 in Hl.
(* a' == b' *)
setoid_rewrite <-(findfind _ b
  (fun b' b1 => _ >>= fun i' => _ >>= fun j' =>
    union i' j' >> Ret ((_ == b') || _ && (b1 == _) || _ && (b1 == _)))).
setoid_rewrite <-(findfind _ a
  (fun a' a1 => _ >>= fun b' => _ >>= fun b1 => _ >>= fun i' => _ >>= fun j' =>
    union i' j' >> Ret ((a' == _) || (a1 == _) && _ || (a1 == _) && _))).
setoid_rewrite (findC _ a b).
under eq_bind do under eq_bind => a' do under eq_bind => b' do
  rewrite -(bindretf (a' == b')
    (fun e => _ >>= fun a1 => _ >>= fun b1 => _ >>= fun i' => _ >>= fun j' =>
       _ >> Ret (e || _ || _))).
rewrite -bindA.
under eq_bind do rewrite -bindA.
rewrite -bindA.
rewrite [X in X >>= _]bindA.
rewrite (IH (Tuple Hl')).
normalize_bindA.
(* a' == i' *)
setoid_rewrite <-(findfind _ a
  (fun a1 a2 => _ >>= fun b1 => _ >>= fun i' => _ >>= fun j' =>
    union i' j' >> Ret (_ || (a1 == _) && _ || (a2 == _) && _))).
set i := (last c l).
setoid_rewrite <-(findfind _  i.1
  (fun i1 i2 => _ >>= fun j' =>
    union i2 j' >> Ret (_ || (_ == i1) && _ || _ && (_ == i2)))).
do 2 setoid_rewrite (findC _ _ i.1).
under eq_bind do under eq_bind do under eq_bind do under eq_bind do
  under eq_bind => a' do under eq_bind => i1 do
  rewrite -(bindretf (a' == i1)
    (fun e => _ >>= fun a1 => _ >>= fun b1 => _ >>= fun i' => _ >>= fun j' =>
       _ >> Ret (_ || e && _ || _))).
under eq_bind => l'. under eq_bind => a'. under eq_bind => b'.
  rewrite -bindA.
  under eq_bind do rewrite -bindA.
  rewrite -bindA.
  rewrite [X in X >>= _]bindA.
over. over. over.
setoid_rewrite (IH _ a i.1).
normalize_bindA.
do ! setoid_rewrite find_pairsC.
rewrite find_pairs_dup.
setoid_rewrite (findC _ b a).
setoid_rewrite findfind.
(* a' == j' *)
setoid_rewrite <-(findfind _  i.2
  (fun j1 j2 => union _ j2 >> Ret (_ || _ && (_ == j2) || (_ == j1) && _))).
do 2 setoid_rewrite (findC _ _ i.2).
under eq_bind do under eq_bind do under eq_bind do under eq_bind do
  under eq_bind do under eq_bind => a' do under eq_bind => j1 do
  rewrite -(bindretf (a' == j1)
    (fun e => _ >>= fun b1 => _ >>= fun i' => _ >>= fun j' =>
      _ >> Ret (_ || _ || e && _ ))).
under eq_bind => l'. under eq_bind => a'. under eq_bind => b'.
under eq_bind => i'.
  rewrite -bindA.
  under eq_bind do rewrite -bindA.
  rewrite -bindA.
  rewrite [X in X >>= _]bindA.
over. over. over. over.
setoid_rewrite (IH _ a i.2).
normalize_bindA.
do ! setoid_rewrite find_pairsC.
rewrite find_pairs_dup.
do 2 setoid_rewrite (findC _ _ a).
setoid_rewrite findfind.
(* b' == i' *)
setoid_rewrite <-(findfind _ b
  (fun b1 b2 => _ >>= fun i' => _ >>= fun j' =>
    union i' j' >> Ret (_ || _ && (b2 == _) || _ && (b1 == _)))).
setoid_rewrite <-(findfind _  i.1
  (fun i1 i2 => _ >>= fun j' => union i2 j' >> Ret (_ || _ || _ && (_ == i1)))).
setoid_rewrite (findC _ b i.1 (fun _ _ => find i.1 >>= _)).
under eq_bind do under eq_bind do under eq_bind do under eq_bind do
  under eq_bind do under eq_bind do under eq_bind => b' do under eq_bind => i1
  do rewrite -(bindretf (b' == i1)
    (fun e => _ >>= fun b1 => _ >>= fun i' => _ >>= fun j' =>
      _ >> Ret (_ || _ || _ && e))).
under eq_bind => l'. under eq_bind => a'. under eq_bind => b'.
under eq_bind => i1. under eq_bind => j2.
  rewrite -bindA.
  under eq_bind do rewrite -bindA.
  rewrite -bindA.
  rewrite [X in X >>= _]bindA.
over. over. over. over. over.
setoid_rewrite (IH _ b i.1).
normalize_bindA.
do ! setoid_rewrite find_pairsC.
rewrite find_pairs_dup.
setoid_rewrite (findC _ i.2 b).
setoid_rewrite (findC _ i.1 b).
setoid_rewrite findfind.
setoid_rewrite (findC _ i.2 i.1).
setoid_rewrite findfind.
(* b' == j' *)
setoid_rewrite <-(findfind _ i.2
  (fun j1 j' => union _ j' >> Ret (_ || _ && (_ == j1) || _))).
setoid_rewrite (findC _ i.1 i.2 (fun _ _ => find i.2 >>= _)).
under eq_bind do under eq_bind do under eq_bind do under eq_bind do
  under eq_bind do under eq_bind do under eq_bind => b' do under eq_bind => j1
  do rewrite -(bindretf (b' == j1)
    (fun e => _ >>= fun i' => _ >>= fun j' => _ >> Ret (_ || _ && e || _))).
under eq_bind => l'. under eq_bind => a'. under eq_bind => b'.
under eq_bind => i1. under eq_bind => j2.
  rewrite -bindA.
  under eq_bind do rewrite -bindA.
  rewrite -bindA.
  rewrite [X in X >>= _]bindA.
over. over. over. over. over.
setoid_rewrite (IH _ b i.2).
normalize_bindA.
do ! setoid_rewrite find_pairsC.
rewrite find_pairs_dup.
setoid_rewrite (findC _ i.2 b).
setoid_rewrite (findC _ i.1 b).
setoid_rewrite findfind.
setoid_rewrite findfind.
under eq_bind do under eq_bind do under eq_bind do under eq_bind do
  under eq_bind do rewrite -bindA.
setoid_rewrite <- find_union_iter_find.
normalize_bindA.
setoid_rewrite (findC _ i.2 i.1).
setoid_rewrite findfind.
setoid_rewrite (findC _ _ _ (fun x y => union x y >> _)).
under eq_bind do under eq_bind do under eq_bind do under eq_bind do
  under eq_bind do rewrite -bindA.
setoid_rewrite <- find_union_iter_find.
normalize_bindA.
setoid_rewrite findfind.
under eq_bind do under eq_bind do under eq_bind do under eq_bind do
  under eq_bind do under eq_bind do under eq_bind do rewrite -bindA.
setoid_rewrite findunionl.
under eq_bind do under eq_bind do under eq_bind do under eq_bind do
  under eq_bind do under eq_bind do rewrite -bindA.
setoid_rewrite findunion.
under eq_bind do under eq_bind do under eq_bind do under eq_bind do
  under eq_bind do rewrite -bindA.
do ! setoid_rewrite (findC _ _ i.2).
do ! setoid_rewrite (findC _ _ i.1).
rewrite /find_pairs.
have -> : Tuple Hl = [tuple of Tuple Hl' ++ [tuple last c l]].
  exact: val_inj.
rewrite mapM_tuple_cat /= -/(@find_pairs n) bindA -/i.
rewrite [in eqvRHS](surjective_pairing i).
apply: bindfeqv => l'.
rewrite !bindA.
apply: bindfeqv => i'.
rewrite !bindA.
apply: bindfeqv => j'.
rewrite !bindretf.
rewrite /= {1}cats1 foldM_rcons /= -/(union_iter l').
apply: bindfeqv => a'.
apply: bindfeqv => b'.
apply: bindfeqv => _.
(* Now just need to solve the graph problem *)
by rewrite exists_path_split.
Qed.
End correction_proof.
