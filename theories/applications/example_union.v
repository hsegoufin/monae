From mathcomp Require Import all_ssreflect.
Require Import preamble.
From mathcomp Require boolp.
Require Import hierarchy monad_lib  fail_lib state_lib.
Require Import monad_transformer.


Local Open Scope monae_scope.

Arguments bindfeqv {s A B f g d}.

Section extra_rules.
Context (S:UU0) (M: unionFailMonad S).
Local Notation I := hierarchy.UnionFind.I.

Lemma findunionl i j : (find i >>= union ^~ j) ≈ @union S M i j.
Proof. 
  by setoid_rewrite unionSymm;  rewrite findunion.
Qed.

Lemma finddup A i m : (find i >>= fun x => find x >>= m  : M A) ≈ find i >>= m.
Proof.
  rewrite -{2}(bindskipf (find i)) -(union_id i) -findunionfind !bindA.
  apply: bindfeqv => a.
  by rewrite -{1}(bindskipf (find a)) -(union_id i).
Qed.

Lemma uniondup i j : union i j >> union i j ≈ (union i j : M unit).
Proof.
  setoid_rewrite <-findunionl at 2.
  setoid_rewrite <-bindA.
  rewrite unionfind  bindA.
  setoid_rewrite findunionl.
  setoid_rewrite union_id.
  by rewrite bindmskip. 
Qed.

Lemma union_eq : forall a i j, find a ≈ (find j :M I) -> (union i a : M unit) ≈ union i j.
Proof.
  move=> a i j Hfind.
  rewrite -findunion -findunion.
  by apply: bindmeqv.
Qed.

(* not sure it is the right way to go *)
Lemma find_eq a i :  find a ≈ (find i : M I) -> neqfind a i ≈ (fail : M unit).
Proof.
  move=> Heq.
  rewrite neqfindE Heq findfind.
  under eq_bind => x.
  have H := @erefl I x.
  move/eqP in H; rewrite H=>/=.
  rewrite guardF.
  over.
  by rewrite find_lookup.
Qed.
End extra_rules.

Section equivLaws.
Context (S:UU0) (M: unionFailMonad S).
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
Context (S:UU0) (M: unionFailMonad S).
Local Notation I := hierarchy.UnionFind.I.

Lemma remember_find  B (a:I) (m :I-> M B): 
find a >>= (fun a' => m a') ≈
find a >>= (fun a0 => find a >>= fun a1 => guard (a0 == a1)>> m a0).
Proof.
  by rewrite findfind;
  apply: bindfeqv=>{}a0;
  rewrite eqxx guardT bindskipf.
Qed.

Lemma rewrite_under A B C (d1 d2 : M B) (f : M C) (g : B -> M A) : 
  d1 ≈ (d2 : M B) -> 
  (f >>= fun x => d1 >>= g : M A) ≈ f >>= fun x => d2 >>= g.
Proof.
  by move=> Heq;
  apply: bindfeqv=>_;
  apply: bindmeqv. 
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
  rewrite guardF !bindfailf -{1}(find_lookup _ a fail).
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
  (* reapeat use of findC and guardfindC *)
Admitted. 

Lemma find_neqfindC A i a j (m : I -> M A): 
(find i >>= (fun i1  => (neqfind a j >> m i1))) ≈
( neqfind a j >> (find i >>= m)).
Proof.
    rewrite neqfindE !bindA.
    under eq_bind=>i1.
    rewrite !bindA.
    under eq_bind=>x.
    rewrite !bindA.
    1,2 : over.
    rewrite (findC _ i a).
    apply: bindfeqv=>{}a1.
    rewrite (findC _ i j).
    rewrite !bindA.
    apply: bindfeqv=>{}j1.
    case (a1 != j1 ).
    - rewrite guardT !bindskipf.
      apply: bindfeqv=>{}i1.
      by rewrite bindskipf.
    - rewrite guardF !bindfailf.
    rewrite -(find_lookup _ i fail).
    apply: bindfeqv=>{}i1.
    by rewrite bindfailf.
Qed.

Lemma new_law i j: 
(union i j : M unit) ≈
find i >>= fun i' => find j >>= fun j' => union i j >> find i >>= fun i0=>  guard ( (i' == i0) || (j' == i0) ).
Proof.
Admitted.

Lemma union_axiom_neqcase a' a b' b i' i j' j : 
a' != b' -> a' != i' -> a' != j' ->
(find b >>= (fun a1=> guard (b' == a1) >> (find a >>= (fun x=> guard (a' == x) >> (find j >>= (fun x0=> guard (j' == x0) >> (find i >>= (fun x1=> guard (i' == x1) >> (union i' j' >> guard false)))))))) : M unit) ≈ 
(find b >>= (fun a1=> guard (b' == a1) >> (find a >>= (fun x=> guard (a' == x) >> (find j >>= (fun x0=> guard (j' == x0) >> (find i >>= (fun x1=> guard (i' == x1) >> (union i' j' >> (find b' >>= (fun b'0 : I => find a' >>= (fun a'0 : I => guard (a'0 == b'0))))))))))))).
Proof.
  move=> Hab Hai Haj. 
  (* first add neqfinds for a*)
  rewrite -!(bindA (find b))  !(bindfeqv (fun _ => find_guard_exch _ a a' j j' _)).
  do 2 rewrite -bindA.
  symmetry;do 2 rewrite -bindA;symmetry.
  setoid_rewrite (add_neqfind _ a a' i i' _ Hai).
  rewrite !bindA -bindA.
    symmetry;rewrite -bindA;symmetry.
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
  setoid_rewrite unionfind_neq.
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
      rewrite -bindA.
      rewrite (bindfeqv (fun=> find_guard_exch _ j j' _ _ _)).
      rewrite bindA.
      rewrite  (find_guard_exch _ i i' a a' _).
      apply:bindfeqv=>a0.
      apply bind_ext_guard_equiv=>/eqP Ha0.
      do 3 rewrite -bindA.
      symmetry; do 3 rewrite -bindA; symmetry.
      have H := bindfeqv (fun=> bindmeqv _ _ _ _ _ (new_law i' j')).
      rewrite !H !bindA.
      clear H.
      under eq_bind=>x. under eq_bind=>u. under eq_bind=>u1. rewrite !bindA.
      under eq_bind=>u2. rewrite !bindA. 
      1, 2, 3, 4: over.
      under eq_bind do rewrite !bindA.
      setoid_rewrite (findC _ i' j' (fun u1 u2 => union i' j' >> (find i' >>=(fun x0 : I =>guard ((u1 == x0) || (u2 == x0)) >>_)))).
      symmetry.
      under eq_bind=>x. under eq_bind=>u. under eq_bind=>u1. rewrite !bindA.
      under eq_bind=>u2. rewrite !bindA. 
      1, 2, 3, 4: over.
      under eq_bind do rewrite !bindA.
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
      do 3 rewrite -bindA.
      symmetry; do 3 rewrite -bindA; symmetry.
      have H := bindfeqv (fun=> bindmeqv _ _ _ _ _ (new_law j' i')).
      setoid_rewrite unionSymm.
      rewrite !H !bindA.
      clear H.
      under eq_bind=>x. under eq_bind=>u. under eq_bind=>u1. rewrite !bindA.
      under eq_bind=>u2. rewrite !bindA. 
      1, 2, 3, 4: over.
      under eq_bind do rewrite !bindA. 
      symmetry.
      under eq_bind=>x. under eq_bind=>u. under eq_bind=>u1. rewrite !bindA.
      under eq_bind=>u2. rewrite !bindA. 
      1, 2, 3, 4: over.
      under eq_bind do rewrite !bindA.
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
    rewrite (bindfeqv (fun=>unionfind_neq _ _ _ _ _)).
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

Lemma union_axiom  (i j a b: I):
(union i j >> find a >>= fun a' => find b >>= fun b' => guard (a' == b'): M unit )≈
find a >>= fun a' => find b >>= fun b' => find i >>= fun i' => find j >>= fun j' => 
union i' j' >> guard ((a' == b') || ((a' == i') && (b' == j')) || ((a' == j') && (b' == i'))).
Proof.
(* ### Seaction i & j ###*)
    setoid_rewrite <-(findunionl S M i j).
  have : (find i >>= union^~ j ≈ (find i >>=(fun i'=> find j >>= union i'):M unit)).
  - apply: bindfeqv=>{}i'; symmetry;exact: findunion.
  move=>H.
  setoid_rewrite H.
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
  -  rewrite !bindA. 
    case /norP: Hb => [Hb0 /nandP Hb1].
    case /norP: Hb0 => Hb0 Hb2.
    case: Hb1 => Hb1.
    move: Hb2.
    case /boolP : (a' == i') => Ha1 /= Hbj; last first.
    +  by rewrite union_axiom_neqcase.
    + have Ha2 : (b' != i') by move /eqP in Ha1;rewrite -Ha1 eq_sym.
      rewrite !(find_guard_exch _ b b' a a' _).
      rewrite union_axiom_neqcase.
      setoid_rewrite (findC _ b' a' _).
      apply:bindfeqv=>a1.
      apply bind_ext_guard_equiv=>H1.
      apply:bindfeqv=>b1.
      apply bind_ext_guard_equiv=>H2.
      apply:bindfeqv=>j1.
      apply bind_ext_guard_equiv=>Hj.
      apply:bindfeqv=>i1.
      apply bind_ext_guard_equiv=>Hi.
      apply:bindfeqv=>_.
      apply:bindfeqv=>a2.
      apply:bindfeqv=>b2.
      case Hyp : (a2 == b2);by rewrite eq_sym in Hyp; rewrite Hyp.
      2, 3: by [].
      by apply /eqP /nesym /eqP.
    case /nandP: Hb2 => Hb2. (* symmetric of first bullet, rewrite to be better *)
    + case Ha1 : (a' == j'). 
      * have Hb3 : (b' != j') by move /eqP in Ha1;rewrite -Ha1 eq_sym.
      rewrite !(find_guard_exch _ b b' a a' _).
      rewrite union_axiom_neqcase.
      setoid_rewrite (findC _ b' a' _).
      apply:bindfeqv=>a1.
      apply bind_ext_guard_equiv=>H1.
      apply:bindfeqv=>b1.
      apply bind_ext_guard_equiv=>H2.
      apply:bindfeqv=>j1.
      apply bind_ext_guard_equiv=>Hj.
      apply:bindfeqv=>i1.
      apply bind_ext_guard_equiv=>Hi.
      apply:bindfeqv=>_.
      apply:bindfeqv=>a2.
      apply:bindfeqv=>b2.
      case Hyp : (a2 == b2);by rewrite eq_sym in Hyp; rewrite Hyp.
      2, 3: by [].
      by apply /eqP /nesym /eqP.
      * move/eqP /eqP in Ha1.
        by rewrite union_axiom_neqcase.
    +  rewrite !(find_guard_exch _ b b' a a' _).
      rewrite union_axiom_neqcase.
      setoid_rewrite (findC _ b' a' _).
      apply:bindfeqv=>a1.
      apply bind_ext_guard_equiv=>H1.
      apply:bindfeqv=>b1.
      apply bind_ext_guard_equiv=>H2.
      apply:bindfeqv=>j1.
      apply bind_ext_guard_equiv=>Hj.
      apply:bindfeqv=>i1.
      apply bind_ext_guard_equiv=>Hi.
      apply:bindfeqv=>_.
      apply:bindfeqv=>a2.
      apply:bindfeqv=>b2.
      case Hyp : (a2 == b2);by rewrite eq_sym in Hyp; rewrite Hyp.
      2, 3: by [].
      by apply /eqP /nesym /eqP.
Qed. (* todo factorize similar proof in a lemma*)


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