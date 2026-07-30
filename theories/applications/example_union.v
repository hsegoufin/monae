From mathcomp Require Import all_ssreflect.
Require Import preamble.
From mathcomp Require boolp.
Require Import hierarchy monad_lib  fail_lib state_lib.
Require Import monad_transformer.


Local Open Scope monae_scope.

Arguments bindfeqv {s A B f g d}.

Section extra_rules.
Context (M: unionFailMonad).
Local Notation I := hierarchy.UnionFind.I.

Lemma findunionl i j : (find i >>= union ^~ j) ≈ @union M i j.
Proof. 
  by setoid_rewrite union_sym;  rewrite findunion.
Qed.

Lemma finddup A i m : (find i >>= fun x => find x >>= m  : M A) ≈ find i >>= m.
Proof.
  rewrite -{2}(bindskipf (find i)) -(union_refl i) -findunionfind !bindA.
  apply: bindfeqv => a.
  by rewrite -{1}(bindskipf (find a)) -(union_refl i).
Qed.

Lemma uniondup i j : union i j >> union i j ≈ (union i j : M unit).
Proof.
  setoid_rewrite <-findunionl at 2.
  setoid_rewrite <-bindA.
  rewrite unionfind  bindA.
  setoid_rewrite findunionl.
  setoid_rewrite union_refl.
  by rewrite bindmskip. 
Qed.

Lemma union_eq a i j: find a ≈ (find j :M I) -> (union i a : M unit) ≈ union i j.
Proof. by rewrite -findunion -findunion; apply: bindmeqv. Qed.

Lemma find_lookup A i (m : M A) : (find i >> m) ≈ m.
Proof. by rewrite -(bindskipf m) -{2}(findskip i) bindA. Qed.

End extra_rules.

Section equivLaws.
Context (M: unionFailMonad ).
Local Notation I := hierarchy.UnionFind.I.

(* TODO M more generic + move into lib*)
Lemma bind_ext_guard_equiv [A : UU0] [b : bool] [m1 m2 : M A]:
(b -> m1 ≈ m2) -> guard b >> m1 ≈ guard b >> m2.
Proof.
  case b => H.
  by rewrite guardT !bindskipf; apply H.
  by rewrite guardF !bindfailf.
Qed.
End equivLaws.

Section correction_proof.
Context  (M: unionFailMonad).
Local Notation I := hierarchy.UnionFind.I.

Lemma remember_find  B (a:I) (m :I-> M B): 
find a >>= (fun a' => m a') ≈
find a >>= (fun a0 => find a >>= fun a1 => guard (a0 == a1)>> m a0).
Proof.
  by rewrite findfind;
  apply: bindfeqv=>{}a0;
  rewrite eqxx guardT bindskipf.
Qed.

Lemma guardfindC A b a (f: I -> M A): 
  (guard b >> (find a >>= f) : M A) ≈
  find a >>=(fun x => guard b >> f x).
Proof.
  case b.
  - rewrite guardT bindskipf.
    by symmetry; under eq_bind do rewrite bindskipf.
  - rewrite guardF !bindfailf.
    symmetry; under eq_bind do rewrite bindfailf.
    by rewrite find_lookup.
Qed.

Lemma pushfind B a a' b (m : I ->I-> M B): 
find a >>= (fun x : I => ((guard (a' == x) >> (find b >>= (fun v : I => m v x))))) ≈
find b >>= fun v => (find a >>= (fun x : I => (guard (a' == x) >> m v x))).
Proof.
  rewrite (bindfeqv (fun a => guardfindC _ (a' == a) b _) ).
  by rewrite findC.
Qed.

Lemma guardC A b1 b2 (m : M A) : 
guard b1 >> (guard b2 >> m) ≈ 
guard b2 >> (guard b1 >> m).
Proof.
  case b1.
    by rewrite guardT !bindskipf.
  rewrite guardF !bindfailf .
  case b2.
  by rewrite guardT bindskipf.
  by rewrite guardF bindfailf.
Qed.

Lemma finddupguard A a a'(m : I -> M A): 
find a >>=(fun a0 : I => (guard (a' == a0) >> (find a' >>= m))) ≈
find a >>=(fun a0 : I => (guard (a' == a0) >> m a0 )).
Proof.
  have : find a >>= (fun a0 : I => (guard (a' == a0) >> (find a' >>= m))) ≈  find a >>= (fun a0 : I => (guard (a' == a0) >> (find a0 >>= m))).
    apply: bindfeqv=>{}a0.
    by apply bind_ext_guard_equiv => /eqP H; rewrite H.
    move=> ->.
    by rewrite (bindfeqv (fun x => guardfindC _ (a' == x) x _))
    -(findfind  _ _ (fun x0 x1 => find x1 >>= (fun r : I => guard (a' == x0) >> m r) ))
    (bindfeqv (fun r => finddup _ _ _ a (fun r0 : I => guard (a' == r) >> m r0))) findfind.
Qed.

Lemma add_neqfind A a a' i i' (m : M A) : 
a' != i' -> 
(find a >>= (fun x1 : I => guard (a' == x1) >>  (find i >>=  (fun i1 => guard (i' == i1 ) >> m))) ≈
(find a >>= (fun x1 : I => guard (a' == x1) >>  (find i >>=  (fun i1 => guard (i' == i1 ) >> (neqfind a' i' >> m)))))).
Proof.
  move=> Hdiff.
  symmetry.
  rewrite neqfindE.
    under eq_bind=>x0. 
  under eq_bind=>u. 
  under eq_bind=>i1. rewrite !bindA. 
  under eq_bind do under eq_bind do rewrite !bindA.
  1,2,3: over.
  setoid_rewrite (pushfind _ i).
  rewrite finddupguard.
  apply: bindfeqv=>{}r.
  apply bind_ext_guard_equiv=>/eqP Ha.
  rewrite finddupguard.
  apply: bindfeqv=>{}i1.
  apply bind_ext_guard_equiv=>/eqP Hi.
  by rewrite -Ha -Hi Hdiff guardT bindskipf. 
Qed.

Lemma find_guard_exch A a a' j j' m:
(find a >>= (fun x : I => guard (a' == x) >> (find j >>= (fun x0 : I => guard (j' == x0)>> m x x0))) : M A) ≈
find j >>= (fun x0 : I => guard (j' == x0) >> (find a >>= (fun x : I => guard (a' == x) >> m x x0))).
Proof.
  rewrite (bindfeqv (fun x => guardfindC _ (a' == x) _ _)).
  rewrite findC.
  apply: bindfeqv=>{}j0.
  case (j' == j0).
  -rewrite guardT !bindskipf.
    apply: bindfeqv=>{}a0.
    apply bind_ext_guard_equiv=>_.
    by rewrite bindskipf.
  symmetry.
  rewrite guardF !bindfailf -{1}(find_lookup _ _ _ a fail).
  apply: bindfeqv=>a0.
  case (a' == a0).
  by rewrite guardT bindskipf bindfailf.
  by rewrite guardF bindfailf.
Qed.

Lemma findgard_neqfindC A i i' a j (m : M A): 
(find i >>= (fun i1 : I => (guard (i' == i1) >> (neqfind a j >> m)))) ≈
( neqfind a j >> (find i >>= (fun i1 : I => (guard (i' == i1) >> m)))).
Proof.
  rewrite neqfindE !bindA.
  under eq_bind do under eq_bind do under eq_bind do rewrite !bindA.
  symmetry.
  under eq_bind do rewrite !bindA.
  rewrite (bindfeqv (fun a0 => bindfeqv (fun x => guardfindC _ (a0 != x) i _))).
  rewrite  (bindfeqv (fun=>findC _ _ i _)) findC.
  apply:bindfeqv=>{}i0.
  do 2 (rewrite guardfindC;apply: bindfeqv=>?).
  by rewrite guardC.
Qed.

Definition findchk a a' : M unit :=
  find a >>= fun a0 => guard (a' == a0).

Lemma union_axiom_neqcase a' a b' b i' i j' j : 
a' != b' -> a' != i' -> a' != j' ->
(findchk b b' >> (findchk a a' >> (findchk j j' >> (findchk i i' >> (union i' j' >> @fail M _))))) ≈ 
(findchk b b' >> (findchk a a' >> (findchk j j' >> (findchk i i' >> (union i' j' >> (find b' >>= (fun b'0 : I => find a' >>= (fun a'0 : I => guard (a'0 == b'0))))))))).
Proof.
  move=> Hab Hai Haj.
  rewrite /findchk ! bindA. 
  (* first add neqfinds for a*)
  rewrite -!(bindA (find b))  !(bindfeqv (fun _ => find_guard_exch _ a a' j j' _)) !bindA.
  setoid_rewrite (add_neqfind _ a a' i i' _ Hai).
  do 2 (rewrite -bindA;symmetry).
  rewrite !(bindfeqv (fun _ => find_guard_exch _ j j' _ _ _)).
  rewrite -!(bindA (find a) _ _).
  rewrite !(bindfeqv (fun _ => (bindfeqv (fun _ => find_guard_exch _ j j' i i' _)))).
  under eq_bind do rewrite bindA.
  symmetry;under eq_bind do rewrite bindA;symmetry.
  rewrite !(bindfeqv (fun =>  find_guard_exch _ a a' i i' _ )).
  do 2 setoid_rewrite findgard_neqfindC.
  setoid_rewrite (add_neqfind _ a a' j j' _ Haj).
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
  do 2 apply: bindfeqv=>_.
  (* reunite find a and find a' *)
  do 3 rewrite -bindA.
  rewrite (bindfeqv (fun=>find_guard_exch _ a a' j j' _)).
  do 2 rewrite -bindA.
  rewrite (bindfeqv (fun=>finddupguard _ _ _ _)).
  rewrite !bindA. under eq_bind do rewrite !bindA.
  (*case analysis*)
  case Hb: ( (b' == i') || (b' == j')).
  -
    move/orP in Hb.
    case Hb => [/eqP Hbi | /eqP Hbj].  
      + rewrite Hbi.
      apply:bindfeqv=>b0.
      apply bind_ext_guard_equiv=>/eqP Hb0.
      (*test to see*)
      rewrite (find_guard_exch _ i).
      rewrite -bindA (bindfeqv (fun=> find_guard_exch _ j j' _ _ _)) bindA.
      rewrite  (find_guard_exch _ i i' a a' _).
      apply:bindfeqv=>a0.
      apply bind_ext_guard_equiv=>/eqP Ha0.
      setoid_rewrite <-(findunion_eq i' j').
      rewrite !bindA.
      under eq_bind=>?.
      under eq_bind=>?.
      under eq_bind=>?.
      under eq_bind=>?.
      under eq_bind=>?.
      rewrite !bindA.
      under eq_bind=>?.
      rewrite bindA.
      under eq_bind=>?.
      rewrite bindA.
      1, 2, 3, 4, 5, 6, 7 : over.
      setoid_rewrite (findC _ i' j' (fun u1 u2 => union i' j' >> (find i' >>=(fun r : I =>guard ((u1 == r) || (u2 == r)) >>_)))).

      symmetry.
      under eq_bind=>?.
      under eq_bind=>?.
      under eq_bind=>?.
      under eq_bind=>?.
      under eq_bind=>?.
      rewrite !bindA.
      under eq_bind=>?.
      rewrite bindA.
      under eq_bind=>?.
      rewrite bindA.
      1, 2, 3, 4, 5, 6, 7 : over.
      setoid_rewrite (findC _ i' j' (fun u1 u2 => union i' j' >> (find i' >>= (fun x0 : I =>guard ((u1 == x0) || (u2 == x0)) >> guard false)))).
      setoid_rewrite (finddupguard _ j j').
      setoid_rewrite (pushfind _ j).
      rewrite !finddupguard.
      apply: bindfeqv=>{}i1.
      apply bind_ext_guard_equiv=>/eqP Hi1.
      apply: bindfeqv=>{}j1.
      apply bind_ext_guard_equiv=>/eqP Hj1.
      apply: bindfeqv=>_.
      rewrite (bindfeqv (fun x0 => guardfindC _ _ _ _)) findfind.
      apply: bindfeqv=>{}i2.
      apply bind_ext_guard_equiv=> /orP H.
      have Hab': (a' == b') = false by apply /eqP /eqP.
      have Haj': (a' == j') = false by apply /eqP /eqP.
      case: H => /eqP H; subst.
      by rewrite Hab'.
      by rewrite Haj'.
      + rewrite Hbj.
      apply:bindfeqv=>b0.
      apply bind_ext_guard_equiv=>/eqP Hb0.
      rewrite (find_guard_exch _ i).
      setoid_rewrite ( find_guard_exch _ j j' _ _ _).
      rewrite  (find_guard_exch _ i i' a a' _).
      apply:bindfeqv=>a0.
      apply bind_ext_guard_equiv=>/eqP Ha0.
      setoid_rewrite union_sym.
      setoid_rewrite <-(findunion_eq j' i').
      rewrite !bindA.
      under eq_bind=>?.
      under eq_bind=>?.
      under eq_bind=>?.
      under eq_bind=>?.
      under eq_bind=>?.
      rewrite !bindA.
      under eq_bind=>?.
      rewrite bindA.
      under eq_bind=>?.
      rewrite bindA.
      1, 2, 3, 4, 5, 6, 7 : over.
      symmetry.
      under eq_bind=>?.
      under eq_bind=>?.
      under eq_bind=>?.
      under eq_bind=>?.
      under eq_bind=>?.
      rewrite !bindA.
      under eq_bind=>?.
      rewrite bindA.
      under eq_bind=>?.
      rewrite bindA.
      1, 2, 3, 4, 5, 6, 7 : over.
      setoid_rewrite (finddupguard _ j j').
      setoid_rewrite (pushfind _ j).
      rewrite !finddupguard.
      apply: bindfeqv=>{}i1.
      apply bind_ext_guard_equiv=>/eqP Hi1.
      apply: bindfeqv=>{}j1.
      apply bind_ext_guard_equiv=>/eqP Hj1.
      apply: bindfeqv=>_.
      rewrite (bindfeqv (fun x0 => guardfindC _ _ _ _)) findfind.
      apply: bindfeqv=>{}j2.
      apply bind_ext_guard_equiv=> /orP H.
      have Hab': (a' == b') = false by apply /eqP /eqP.
      have Hai': (a' == i') = false by apply /eqP /eqP.
      case: H => /eqP H; subst.
      by rewrite Hab'.
      by rewrite Hai'.
  - move /norP in Hb.
    case: Hb=>[/eqP /eqP Hbi /eqP /eqP Hbj].
    do 3 rewrite -bindA.
    rewrite (bindfeqv (fun=>find_guard_exch _ j j' a a' _)) !bindA.
    under eq_bind do rewrite !bindA.
    (* now we do the same as we did with a in the first part of the proof but with b*)
    rewrite -!(bindA (find b)).
    rewrite !(bindfeqv (fun=>find_guard_exch _ i i' a a' _)).
    rewrite !bindA.
    rewrite  !(find_guard_exch _ b b').
    apply: bindfeqv=>{}a0.
    apply bind_ext_guard_equiv=>/eqP <-.
    rewrite -!(bindA (find b)).
    rewrite  !(bindfeqv (fun=>find_guard_exch _ i i' j j' _)).
    rewrite !(bindA (find b)) !(find_guard_exch _ b b' j j').
    setoid_rewrite (add_neqfind _  _ _ _ _ _ Hbi).
    do 3 setoid_rewrite findgard_neqfindC.
    do 2 rewrite -bindA.
    symmetry; do 2 rewrite -bindA;symmetry.
    rewrite -(bindfeqv (fun=>find_guard_exch _ i i' b b' _)).
    rewrite !bindA.
    setoid_rewrite (find_guard_exch _ j j').
    do 2 rewrite -bindA.
    rewrite (bindfeqv (fun=>find_guard_exch _ j j' _ _ _)).
    rewrite !bindA.
    setoid_rewrite (add_neqfind _  _ _ _ _ _ Hbj).
    do 3 setoid_rewrite <-(findgard_neqfindC _ _ _ b' i').
    do 7 rewrite -bindA.
    under eq_bind do do 2 rewrite -bindA.
    rewrite (bindfeqv (fun=>findunion_neq _ _ _ _ _)).
    under eq_bind do rewrite !bindA.
    rewrite !bindA.
    under eq_bind do rewrite !bindA.
    under eq_bind do under eq_bind do under eq_bind do rewrite !bindA.
    do 6 setoid_rewrite findgard_neqfindC.
    do 2 apply: bindfeqv=>_.
    rewrite -bindA.
    rewrite (bindfeqv (fun=>find_guard_exch _ _ _ _ _ _)).
    setoid_rewrite finddupguard.
    rewrite !bindA.
    rewrite (find_guard_exch _ b b').
    rewrite (find_guard_exch _ i i').
    apply: bindfeqv=>j0.
    apply bind_ext_guard_equiv=>_.
    rewrite find_guard_exch.
    apply: bindfeqv=>b0.
    apply bind_ext_guard_equiv=>/eqP <-.
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
  symmetry. rewrite (remember_find _ i);symmetry.
  apply: bindfeqv=>{}i'.
  rewrite !bindA.
  setoid_rewrite (findC _ b j).
  setoid_rewrite (findC _ a j).
  rewrite pushfind.
  rewrite (remember_find _ j).
  symmetry.
  rewrite pushfind.
  rewrite (remember_find _ j).
  symmetry.
  apply: bindfeqv=>{}j'.
  rewrite -bindA.
  setoid_rewrite <-findunionfind.
  rewrite bindA.
  do 2 setoid_rewrite (pushfind _ _ _ a).
  under eq_bind do rewrite bindA.
  have : 
  find a >>= (fun a1 : I => find j >>= (fun x : I => guard (j' == x) >> (find i >>= (fun x0 : I => guard (i' == x0) >> (union i' j' >> (find a1 >>= (fun a' : I => find b >>= (fun b' : I => guard (a' == b'))))))))) ≈
  find a >>= (fun a1 : I => find j >>= (fun x : I => guard (j' == x) >> (find i >>= (fun x0 : I => guard (i' == x0) >> (union i' j' >> (find b >>= (fun b' : I => find a1 >>= (fun a' : I => guard (a' == b'))))))))).
  by move=>T t;
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
  do 2 setoid_rewrite (pushfind _ _ _ b).
  do 2 (rewrite remember_find; symmetry).
  apply: bindfeqv=>{}a'.
  rewrite !(bindfeqv (fun a1 => guardfindC _ (a' == a1) b _)).
  rewrite !(findC _ _ b).
  do 2 (rewrite remember_find;symmetry).
  apply: bindfeqv=>{}b'.
  case Hb : ((a' == b') || (a' == i') && (b' == j') || (a' == j') && (b' == i')).
  -  apply: bindfeqv=>{}b0.
    apply bind_ext_guard_equiv=>H_b0.
    apply: bindfeqv=>{}a0.
    apply bind_ext_guard_equiv=>H_a0.
    apply: bindfeqv=>{}j0.
    apply bind_ext_guard_equiv=>H_j0.
    apply: bindfeqv=>{}i0.
    apply bind_ext_guard_equiv=>H_i0.
    move /orP in Hb;case: Hb => Hb.
    move /orP in Hb; case: Hb => Hb.
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
    + rewrite !(find_guard_exch _ b b' a a' _).
      rewrite -!(bindA (find _)) union_axiom_neqcase //; last by rewrite eq_sym.
      setoid_rewrite (findC _ b' a' _).
      do 7 apply/bindfeqv=>?.
      by rewrite eq_sym.
    + have Ha2 : (b' != i') by move /eqP in Hai;rewrite -Hai eq_sym.
      rewrite !(find_guard_exch _ b b' a a' _).
      rewrite -!(bindA (find _)) union_axiom_neqcase //; last by rewrite eq_sym.
      setoid_rewrite (findC _ b' a' _).
      do 7 apply/bindfeqv=>?.
      by rewrite eq_sym.    
    + have Hb3 : (b' != j') by move /eqP in Haj;rewrite -Haj eq_sym.
      rewrite !(find_guard_exch _ b b' a a' _).
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
(a == b) || (a == lookup_vertex n l p0) && path (fun r s => lookup_vertex n l s == lookup_vertex n l (r.1, negb r.2)) p0 p && (b == lookup_vertex n l (last p0 p)). 

Lemma union_iteration n (l : n.-tuple (I*I)) a b p p0:
(union_iter l >> find a >>= fun a' => find b >>= fun b' => Ret (a' == b') : M bool) ≈
find a >>= fun a' => find b >>= fun b' => union_iter l >> Ret ( exist_path n l a' b' p p0).
Proof.
Abort.
End correction_proof.