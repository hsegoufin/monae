From mathcomp Require Import all_ssreflect.
Require Import preamble.
From mathcomp Require boolp.
Require Import hierarchy monad_lib  fail_lib state_lib.
Require Import monad_transformer.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope monae_scope.

Arguments bindfeqv {s A B f g d}.

Section extra_rules.
Variable M : unionFailMonad.
Local Notation I := hierarchy.UnionFind.I.

Lemma findunionl i j : (find i >>= union ^~ j) ≈ @union M i j.
Proof. by setoid_rewrite union_sym; rewrite findunion. Qed.

Lemma finddup A i m : (find i >>= fun x => find x >>= m  : M A) ≈ find i >>= m.
Proof.
  rewrite -{2}(bindskipf (find i)) -(union_refl i) -findunionfind !bindA.
  apply: bindfeqv => a.
  by rewrite -{1}(bindskipf (find a)) -(union_refl i).
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
Lemma bind_ext_guard_equiv [A : UU0] [b : bool] [m1 m2 : M A]:
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

Lemma remember_find  B (a:I) (m :I-> M B): 
  (find a >>= fun a' => m a') ≈
  (find a >>= fun a0 => find a >>= fun a1 => guard (a0 == a1)>> m a0).
Proof.
  by rewrite findfind; apply: bindfeqv => {}a0; rewrite eqxx guardT bindskipf.
Qed.

Notation eqvLHS := (_ : eqvM ^~ _).
Notation eqvRHS := (_ : [eta eqvM _]).

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

Lemma pushfind B a a' b (m : I ->I-> M B): 
  (find a >>= fun x => guard (a' == x) >> (find b >>= fun v => m v x)) ≈
  (find b >>= fun v => find a >>= fun x => guard (a' == x) >> m v x).
Proof. by rewrite (bindfeqv (fun a => guardfindC (a' == a) b _)) findC. Qed.

Lemma guardC A b1 b2 (m : M A) : 
  guard b1 >> (guard b2 >> m) ≈ 
  guard b2 >> (guard b1 >> m).
Proof.
  case: b1.
    by rewrite guardT !bindskipf.
  rewrite guardF !bindfailf .
  case: b2.
  - by rewrite guardT bindskipf.
  - by rewrite guardF bindfailf.
Qed.

Lemma finddupguard A a a' (m : I -> M A) :
  find a >>= (fun a0 => guard (a' == a0) >> (find a' >>= m)) ≈
  find a >>= (fun a0 => guard (a' == a0) >> m a0).
Proof.
  transitivity (find a >>= fun a0 => guard (a' == a0) >> (find a0 >>= m)).
    apply: bindfeqv=> {}a0.
    by apply bind_ext_guard_equiv => /eqP H; rewrite H.
  by rewrite (bindfeqv (fun x => guardfindC (a' == x) x _))
    -(findfind  _ _ (fun x y => find y >>= fun z => guard (a' == x) >> m z))
    (bindfeqv (fun x => finddup a (fun y => guard (a' == x) >> m y)))
    findfind.
Qed.

Ltac normalize_bindA :=
  rewrite ?bindA;
  try (under eq_bind => ?; [normalize_bindA; over |]).

Lemma add_neqfind A a a' i i' (m : M A) : 
  a' != i' ->
  find a >>= (fun x => guard (a' == x) >> (find i >>= fun j => guard (i' == j) >> m)) ≈
  find a >>= (fun x => guard (a' == x) >> (find i >>= fun j => guard (i' == j) >> (neqfind a' i' >> m))).
Proof.
  move=> Hdiff.
  symmetry.
  rewrite neqfindE.
  normalize_bindA.
  setoid_rewrite (pushfind i).
  rewrite finddupguard.
  apply: bindfeqv => r.
  apply: bind_ext_guard_equiv => /eqP <-.
  rewrite finddupguard.
  apply: bindfeqv => i1.
  apply: bind_ext_guard_equiv => /eqP <-.
  by rewrite Hdiff guardT bindskipf.
Qed.

Lemma find_guard_exch A a a' j j' (m : I -> I -> M A) :
  find a >>= (fun x => guard (a' == x) >> (find j >>= fun y => guard (j' == y) >> m x y)) ≈
  find j >>= (fun y => guard (j' == y) >> (find a >>= fun x => guard (a' == x) >> m x y)).
Proof.
  rewrite (bindfeqv (fun x => guardfindC (a' == x) _ _)).
  rewrite findC.
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

Lemma findgard_neqfindC A i i' a j (m : M A) :
  find i >>= (fun i1 => guard (i' == i1) >> (neqfind a j >> m)) ≈
  neqfind a j >> (find i >>= fun i1 => guard (i' == i1) >> m).
Proof.
  rewrite neqfindE.
  normalize_bindA.
  symmetry.
  normalize_bindA.
  setoid_rewrite (guardfindC _ i).
  rewrite (bindfeqv (fun=>findC _ _ i _)) findC.
  apply: bindfeqv => i0.
  do 2 (rewrite guardfindC; apply: bindfeqv => ?).
  by rewrite guardC.
Qed.

Definition findchk a a' : M unit :=
  find a >>= fun a0 => guard (a' == a0).

Lemma union_axiom_neqcase a' a b' b i' i j' j : 
  a' != b' -> a' != i' -> a' != j' ->
  findchk b b' >> (findchk a a' >> (findchk j j' >> (findchk i i' >> (union i' j' >> fail)))) ≈
  findchk b b' >> (findchk a a' >> (findchk j j' >> (findchk i i' >> (union i' j' >> (find b' >>= fun y => find a' >>= fun x => guard (x == y)))))).
Proof.
  move=> Hab Hai Haj.
  rewrite /findchk ! bindA. 
  (* first add neqfinds for a*)
  rewrite -!(bindA (find b))  !(bindfeqv (fun _ => find_guard_exch a a' j j' _)) !bindA.
  setoid_rewrite (add_neqfind a i _ Hai).
  do 2 (rewrite -bindA;symmetry).
  rewrite !(bindfeqv (fun _ => find_guard_exch j j' _ _ _)).
  rewrite -!(bindA (find a) _ _).
  rewrite !(bindfeqv (fun _ => (bindfeqv (fun _ => find_guard_exch j j' i i' _)))).
  under eq_bind do rewrite bindA.
  under [eqvRHS]eq_bind do rewrite bindA.
  rewrite !(bindfeqv (fun => find_guard_exch a a' i i' _ )).
  do 2 setoid_rewrite findgard_neqfindC.
  setoid_rewrite (add_neqfind a j _ Haj).
  (*use neqfind to exchange find and union*)
  do 2 setoid_rewrite <-findgard_neqfindC.
  setoid_rewrite (findC _ b' a').
  symmetry.
  do 8 rewrite -bindA.
  under eq_bind do do 2 rewrite -bindA.
  setoid_rewrite findunion_neq.
  rewrite !bindA.
  (* supress neqfind once used*)
  do 8 setoid_rewrite findgard_neqfindC.
  do 2 apply: bindfeqv => _.
  (* reunite find a and find a' *)
  rewrite -3!bindA.
  rewrite (bindfeqv (fun=>find_guard_exch  a _ j _ _)).
  rewrite -2!bindA.
  rewrite (bindfeqv (fun=>finddupguard _ _ _)).
  rewrite !bindA. under eq_bind do rewrite !bindA.
  (*case analysis*)
  case Hb: ( (b' == i') || (b' == j')).
  - case/orP: Hb => [/eqP Hbi | /eqP Hbj].
    + rewrite Hbi.
      apply: bindfeqv => b0.
      apply: bind_ext_guard_equiv => _ {b0}.
      (*test to see*)
      rewrite (find_guard_exch i).
      rewrite -bindA (bindfeqv (fun=> find_guard_exch j _ _ _ _)) bindA.
      rewrite  (find_guard_exch i i' a a' _).
      apply: bindfeqv => a0.
      apply: bind_ext_guard_equiv => /eqP <- {a0}.
      setoid_rewrite <-(findunion_eq i' j').
      normalize_bindA.
      setoid_rewrite (findC _ i' j').
      symmetry.
      normalize_bindA.
      setoid_rewrite (findC _ i' j').
      setoid_rewrite (finddupguard j j').
      setoid_rewrite (pushfind j).
      rewrite !finddupguard.
      apply: bindfeqv => i1.
      apply: bind_ext_guard_equiv => /eqP <- {i1}.
      apply: bindfeqv => j1.
      apply: bind_ext_guard_equiv => /eqP <- {j1}.
      apply: bindfeqv => _.
      rewrite (bindfeqv (fun x0 => guardfindC _ _ _)) findfind.
      apply: bindfeqv => i2.
      apply: bind_ext_guard_equiv => /orP[] /eqP <-.
      - by rewrite (negbTE Hai).
      - by rewrite (negbTE Haj).
    + rewrite Hbj.
      apply: bindfeqv => b0.
      apply: bind_ext_guard_equiv => _ {b0}.
      rewrite (find_guard_exch i).
      setoid_rewrite ( find_guard_exch j j' _ _ _).
      rewrite  (find_guard_exch i i' a a' _).
      apply: bindfeqv => a0.
      apply: bind_ext_guard_equiv => /eqP <- {a0}.
      setoid_rewrite union_sym.
      setoid_rewrite <-(findunion_eq j' i').
      normalize_bindA.
      symmetry.
      normalize_bindA.
      setoid_rewrite (finddupguard j j').
      setoid_rewrite (pushfind j).
      rewrite !finddupguard.
      apply: bindfeqv => i1.
      apply: bind_ext_guard_equiv => /eqP <- {i1}.
      apply: bindfeqv => j1.
      apply: bind_ext_guard_equiv => /eqP <- {j1}.
      apply: bindfeqv => _.
      rewrite (bindfeqv (fun x0 => guardfindC _ _ _)) findfind.
      apply: bindfeqv => j2.
      apply: bind_ext_guard_equiv=> /orP[] /eqP <-.
      - by rewrite (negbTE Haj).
      - by rewrite (negbTE Hai).
  - case/norP: Hb => Hbi Hbj.
    rewrite -3!bindA.
    rewrite (bindfeqv (fun=>find_guard_exch j j' a a' _)) !bindA.
    (* now we do the same as we did with a in the first part of the proof but with b*)
    rewrite -!(bindA (find b)).
    rewrite !(bindfeqv (fun=>find_guard_exch i i' a a' _)).
    rewrite !bindA.
    rewrite !(find_guard_exch b b').
    apply: bindfeqv => a0.
    apply: bind_ext_guard_equiv => /eqP <-.
    rewrite -!(bindA (find b)).
    rewrite !(bindfeqv (fun=>find_guard_exch i i' j j' _)).
    rewrite !(bindA (find b)) !(find_guard_exch b b' j j').
    setoid_rewrite (add_neqfind  _ _ _ Hbi).
    do 3 setoid_rewrite findgard_neqfindC.
    rewrite -2!bindA.
    rewrite -2![in eqvRHS]bindA.
    rewrite -(bindfeqv (fun=>find_guard_exch i i' b b' _)).
    rewrite !bindA.
    setoid_rewrite (find_guard_exch j j').
    rewrite -2!bindA.
    rewrite (bindfeqv (fun=>find_guard_exch j j' _ _ _)).
    rewrite !bindA.
    setoid_rewrite (add_neqfind _ _ _ Hbj).
    do 3 setoid_rewrite <-(findgard_neqfindC _ _ b' i').
    rewrite -7!bindA.
    under eq_bind do rewrite -2!bindA.
    rewrite (bindfeqv (fun=>findunion_neq _ _ _ _ _)).
    normalize_bindA.
    do 6 setoid_rewrite findgard_neqfindC.
    do 2 apply: bindfeqv => _.
    rewrite -bindA.
    rewrite (bindfeqv (fun=>find_guard_exch _ _ _ _ _)).
    setoid_rewrite finddupguard.
    rewrite !bindA.
    rewrite (find_guard_exch b b').
    rewrite (find_guard_exch i i').
    apply: bindfeqv => j0.
    apply: bind_ext_guard_equiv => _ {j0}.
    rewrite find_guard_exch.
    apply: bindfeqv => b0.
    apply: bind_ext_guard_equiv => /eqP <-.
    by rewrite (negbTE Hab).
Qed.

Lemma union_classes (i j a b: I):
(union i j >> find a >>= fun a' => find b >>= fun b' => @guard M (a' == b') )≈
find a >>= fun a' => find b >>= fun b' => find i >>= fun i' => find j >>= fun j' => 
union i' j' >> guard ((a' == b') || ((a' == i') && (b' == j')) || ((a' == j') && (b' == i'))).
Proof.
  setoid_rewrite <-(findunionl M i j).
  have ->: find i >>= union^~ j ≈ find i >>= fun i' => find j >>= union i'
    by move=>*;apply: bindfeqv=>{}i'; symmetry;exact: findunion.
  rewrite bindA.
  setoid_rewrite (findC _ b i).
  setoid_rewrite (findC _ a i).
  rewrite bindA.
  rewrite remember_find.
  symmetry. rewrite (remember_find i);symmetry.
  apply: bindfeqv=>{}i'.
  rewrite !bindA.
  setoid_rewrite (findC _ b j).
  setoid_rewrite (findC _ a j).
  do 2 (rewrite pushfind (remember_find j);symmetry).
  apply: bindfeqv=>{}j'.
  rewrite -bindA.
  setoid_rewrite <-findunionfind.
  rewrite bindA.
  do 2 setoid_rewrite (pushfind _ _ a).
  under eq_bind do rewrite bindA.
  have : 
  find a >>= (fun a1 : I => find j >>= (fun x : I => guard (j' == x) >> (find i >>= (fun x0 : I => guard (i' == x0) >> (union i' j' >> (find a1 >>= (fun a' : I => find b >>= (fun b' : I => guard (a' == b'))))))))) ≈
  find a >>= (fun a1 : I => find j >>= (fun x : I => guard (j' == x) >> (find i >>= (fun x0 : I => guard (i' == x0) >> (union i' j' >> (find b >>= (fun b' : I => find a1 >>= (fun a' : I => guard (a' == b'))))))))).
    by move=> t;
    apply: bindfeqv=>a0;
    apply: bindfeqv=>x;
    apply: bindfeqv=>_;
    apply: bindfeqv=>x0;
    apply: bindfeqv=>_;
    apply: bindfeqv=>_;
    rewrite findC.
  move=>->.
  under eq_bind do rewrite -bindA.
  setoid_rewrite <-findunionfind.
  under eq_bind do rewrite !bindA.
  do 2 setoid_rewrite (pushfind _ _ b).
  do 2 (rewrite remember_find; symmetry).
  apply: bindfeqv=>{}a'.
  rewrite !(bindfeqv (fun a1 => guardfindC (a' == a1) b _)).
  rewrite !(findC _ _ b).
  do 2 (rewrite remember_find;symmetry).
  apply: bindfeqv=>{}b'.
  case Hb : ((a' == b') || (a' == i') && (b' == j') || (a' == j') && (b' == i')).
  - do 4 (apply: bindfeqv=>?;
    apply bind_ext_guard_equiv=>_).
    case /orP: Hb => Hb.
    case /orP: Hb => Hb.
    + move/eqP in Hb; rewrite Hb.
      rewrite bindA.
      apply: bindfeqv=>{}_.
      rewrite findfind.
      under eq_bind do rewrite eqxx.
      by rewrite guardT find_lookup.
    + move /andP in Hb. 
      case Hb => [/eqP Hi' /eqP Hj'].
      rewrite Hi' Hj'.
      rewrite -unionfind bindA.
      apply: bindfeqv=>{}_.
      rewrite findfind.
      under eq_bind do rewrite eqxx.
      by rewrite guardT find_lookup.
    + move /andP in Hb. 
      case Hb => [/eqP Hj' /eqP Hi'].
      rewrite Hi' Hj'.
      rewrite unionfind bindA.
      apply: bindfeqv=>{}_.
      rewrite findfind.
      under eq_bind do rewrite eqxx.
      by rewrite guardT find_lookup.
  - rewrite !bindA. 
    case /norP: Hb => /norP [Hb0].
    case /boolP: (a' == i') => Hai /= Hbj; case /boolP : (a' == j') => Haj /= Hbi.
    + rewrite !(find_guard_exch b b' a a' _).
      rewrite -!(bindA (find _)) union_axiom_neqcase //; last by rewrite eq_sym.
      setoid_rewrite (findC _ b' a' _).
      do 7 apply/bindfeqv=>?.
      by rewrite eq_sym.
    + have Ha2 : (b' != i') by move /eqP in Hai;rewrite -Hai eq_sym.
      rewrite !(find_guard_exch b b' a a' _).
      rewrite -!(bindA (find _)) union_axiom_neqcase //; last by rewrite eq_sym.
      setoid_rewrite (findC _ b' a' _).
      do 7 apply/bindfeqv=>?.
      by rewrite eq_sym.    
    + have Hb3 : (b' != j') by move /eqP in Haj;rewrite -Haj eq_sym.
      rewrite !(find_guard_exch b b' a a' _).
      rewrite -!(bindA (find _)) union_axiom_neqcase //; last by rewrite eq_sym.
      setoid_rewrite (findC _ b' a' _).
      do 7 apply/bindfeqv=>?.
      by rewrite eq_sym.
    + by rewrite -!(bindA (find _)) union_axiom_neqcase.
Qed.

Definition union_iter  (l : seq (I*I)) : M unit  := 
  foldM (fun _  p => union p.1 p.2) tt l.

Definition lookup_vertex  n (l :n.-tuple (I*I)) (p : 'I_n*bool) :=
  let p' := tnth l p.1 in if p.2 then p'.1 else p'.2.

Definition exist_path n (l : n.-tuple (I*I)) a b (p: n.-bseq ('I_n*bool)) (p0 : 'I_n*bool) :=
(a == b) || (a == lookup_vertex l p0) && path (fun r s => lookup_vertex l s == lookup_vertex l (r.1, negb r.2)) p0 p && (b == lookup_vertex l (last p0 p)). 

Lemma union_iteration n (l : n.-tuple (I*I)) a b p p0:
(union_iter l >> find a >>= fun a' => find b >>= fun b' => Ret (a' == b') : M bool) ≈
find a >>= fun a' => find b >>= fun b' => union_iter l >> Ret ( exist_path l a' b' p p0).
Proof.
Abort.
End correction_proof.
