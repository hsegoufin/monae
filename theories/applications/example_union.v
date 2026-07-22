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
  (guard b >> find a >>= f : M A) ≈
  find a >>=(fun x => guard b >> f x).
Proof.
  case b.
  - rewrite guardT bindskipf.
    by symmetry; under eq_bind do rewrite bindskipf.
  - rewrite guardF !bindfailf.
    symmetry; under eq_bind do rewrite bindfailf.
    by rewrite find_lookup.
Qed.

Lemma pushfind B a a' b (m : I -> M B): 
find a >>= (fun x : I => ((guard (a' == x) >> find b) >>= (fun v : I => m v))) ≈
find b >>= fun v => (find a >>= (fun x : I => ((guard (a' == x) >> m v)))).
Proof.
  rewrite (bindfeqv (fun a => guardfindC _ (a' == a) b _) ).
  by rewrite findC.
Qed.

Lemma guardC A b1 b2 (m : unit -> M A) : 
guard b1 >> guard b2 >>= m ≈ 
guard b2 >> guard b1 >>= m.
Proof.
  case b1.
  by rewrite guardT bindskipf bindmskip.
  rewrite guardF bindfailf bindA bindfailf.
  case b2.
  by rewrite guardT bindskipf.
  by rewrite guardF bindfailf.
Qed.

Lemma finddupguard A a a'(m : I -> M A): 
find a >>=(fun a0 : I => (guard (a' == a0) >> find a' >>= m)) ≈
find a >>=(fun a0 : I => (guard (a' == a0) >> m a0 )).
Proof.
  have : find a >>= (fun a0 : I => (guard (a' == a0) >> find a')) ≈  find a >>= (fun a0 : I => (guard (a' == a0) >> find a0)).
    move=> T t.
    apply: bindfeqv=>{}a0.
    by apply bind_ext_guard_equiv => /eqP H; rewrite H.
    rewrite -bindA=> ->.
    by rewrite !bindA (bindfeqv (fun x => guardfindC _ (a' == x) x _)) 
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
  under eq_bind=>i1. rewrite !bindA -bindA. under eq_bind do rewrite !bindA.
  over. over. over.
  under eq_bind do under eq_bind do under eq_bind do rewrite -(bindA _ (fun _ => find a')).
  setoid_rewrite pushfind.
  under eq_bind do rewrite -(bindA _ (fun _ => find a')).
  rewrite  finddupguard.
  apply: bindfeqv=>{}r.
  case Ha: (a' == r);move/eqP in Ha.
  2: by rewrite guardF !bindfailf.
  rewrite guardT !bindskipf !bindA.
  under eq_bind do rewrite -(bindA _ (fun _ => find i')).
  rewrite finddupguard.
  apply: bindfeqv=>{}i1.
  case Hi: (i' == i1); move/eqP in Hi.
  2: by rewrite guardF !bindfailf.
  rewrite guardT !bindskipf.
  by rewrite -Ha -Hi Hdiff guardT bindskipf. 
Qed.

Lemma find_guard_exch A a a' j j' m:
(find a >>= (fun x : I => guard (a' == x) >> (find j >>= (fun x0 : I => guard (j' == x0)>> m x x0))) : M A) ≈
find j >>= (fun x0 : I => guard (j' == x0) >> (find a >>= (fun x : I => guard (a' == x) >> m x x0))).
Proof.
  under eq_bind do rewrite -bindA.
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

Lemma find_guard_eq A B a a' (m : M B) (n :I-> M A): 
find a >>= (fun v => guard (a' == v)>> find a'>>= n) ≈
find a >>= (fun v => guard (a' == v)>> n v).
Proof.
  have : find a >>= (fun v => guard (a' == v)>> find a'>>= n) ≈  find a >>= (fun v => guard (a' == v)>> find v>>= n).
    apply: bindfeqv=>{}a0.
    case H: (a' == a0); move /eqP in H.
    by rewrite H.
    by rewrite guardF !bindfailf.
  move => ->.
  by rewrite (bindfeqv  (fun x => guardfindC _ (a' == x) x _))
      -(findfind _ a (fun x1 => fun x2 => find x2>>=(fun x3 => guard (a' == x1)>> n x3)))
      (bindfeqv (fun x => (finddup _ _ _ a (fun x0 : I => guard (a' == x) >> n x0) ))) findfind.
Qed.

Lemma findgard_neqfindC A i i' a j (m : M A): 
(find i >>= (fun i1 : I => (guard (i' == i1) >> (neqfind a j >> m)))) ≈
( neqfind a j >> (find i >>= (fun i1 : I => (guard (i' == i1) >> m)))).
Proof.
  rewrite neqfindE !bindA.
  (* reapeat use of findC and guardfindC *)
Admitted. 

Lemma find_neqfindC A i a j (m : I -> M A): 
(find i >>= (fun i1  => (neqfind a j >> m i1))) ≈
( neqfind a j >> (find i >>= m)).
Proof.
    rewrite neqfindE !bindA.
Admitted.

Lemma union_axiome_neqcase a' a b' b i' i j' j : 
a' != b' -> a' != i' -> a' != j' ->
(find b >>= (fun a1 : I => guard (b' == a1) >> (find a >>= (fun x : I => (guard (a' == x) >> (find j >>= (fun x0 : I => guard (j' == x0) >>  (find i >>= (fun x1 : I => guard (i' == x1) >> (union i' j' >> guard false))))))))) : M unit) ≈ 
 find b >>= (fun a1 : I => guard (b' == a1) >> (find a >>= (fun x : I => guard (a' == x) >> (find j >>= (fun x0 : I => guard (j' == x0) >> (find i >>= (fun x1 : I => guard (i' == x1) >> (union i' j' >> (find b' >>= (fun b'0 : I => find a' >>= (fun a'0 : I => guard (a'0 == b'0)))))))))))).
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
  under eq_bind do under eq_bind do rewrite -bindA.
  rewrite (bindfeqv (fun=>finddupguard _ _ _ _)).
  rewrite !bindA. under eq_bind do rewrite !bindA.
  (*case analysis*)
  case Hbi: (b' == i').
  - move/eqP in Hbi; rewrite Hbi.
  admit.
  case Hbj: (b' == j').
  - move/eqP in Hbj; rewrite Hbj.
  (*same case as previous*) admit.
  - move /eqP /eqP in Hbi.
    move /eqP /eqP in Hbj.
    do 3 rewrite -bindA.
    rewrite (bindfeqv (fun=>find_guard_exch _ j j' a a' _)) !bindA.
    under eq_bind do rewrite !bindA.
    (* now we do the same as we did with a in the first part of the proof but with b*)
    rewrite -!(bindA (find b)).
    rewrite !(bindfeqv (fun=>find_guard_exch _ i i' _ _ _)).
    rewrite !(bindA (find b)) !(find_guard_exch _ b b' _ _).
    apply: bindfeqv=>{}a0.
    apply bind_ext_guard_equiv=>/eqP Ha0.
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
    do 2 rewrite -bindA.
    under eq_bind do under eq_bind do rewrite -bindA.
    setoid_rewrite finddupguard.
    rewrite !bindA.
    rewrite find_guard_exch.
    rewrite (find_guard_exch _ i i').
    apply: bindfeqv=>j0.
    apply bind_ext_guard_equiv=>_.
    rewrite find_guard_exch.
    apply: bindfeqv=>b0.
    apply bind_ext_guard_equiv=>/eqP Hb0.
    have : a'==b' = false by apply /eqP /eqP.
    by rewrite -Hb0 -Ha0=>->.
    (* plan : add neqfind for a, then swap union and find A, 
    then case analysis on b0 : either i' j' or neither 
    case i' of by Hai (resp j' and Haj)
    case neither : rewrite neqfin and swap as well then use Hab
  *)
Abort.



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
  under eq_bind=>a1.
  rewrite -(bindA (guard (i' == a1)) (fun _ => find j) _).
  over.
  rewrite pushfind.
  rewrite (remember_find _ j).
  symmetry.
  under eq_bind do rewrite -bindA.
  rewrite pushfind.
  rewrite (remember_find _ j).
  symmetry.
  apply: bindfeqv=>{}j'.
  rewrite -bindA.
  setoid_rewrite <-findunionfind.
  rewrite bindA.
  under eq_bind=>a1.
  under eq_bind=>u.
  under eq_bind=>x.
  rewrite -(bindA (guard (i' == x)) ). 
  over. over. over.
  setoid_rewrite pushfind.
  under eq_bind do rewrite -bindA.
  setoid_rewrite pushfind.
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
  under eq_bind=>a0. under eq_bind=>x. under eq_bind=>u.
  under eq_bind do rewrite -(bindA _ (fun _ => find b) _).
  over. over. over. 
  setoid_rewrite pushfind.

  under eq_bind=>a0.
  under eq_bind do rewrite -bindA.
  over.
  setoid_rewrite pushfind.
  rewrite remember_find.

  symmetry.

  under eq_bind=>a0.
  under eq_bind=>u0.
  under eq_bind do rewrite -bindA.
  over. over.
  setoid_rewrite pushfind.
  under eq_bind do rewrite -bindA.
  setoid_rewrite pushfind.
rewrite remember_find;symmetry.
  apply: bindfeqv=>{}a'.
  under eq_bind do rewrite -bindA.
  symmetry; (under eq_bind do rewrite -bindA); symmetry.
  do 2 rewrite (bindfeqv (fun a1 => guardfindC _ (a' == a1) _ _)).
  symmetry.
  under eq_bind do under eq_bind do under eq_bind do under eq_bind do under eq_bind do rewrite -bindA.
  setoid_rewrite pushfind.
  under eq_bind do under eq_bind do rewrite -bindA.
  rewrite -(@bindfeqv _ _ _ _ _ (find a) (fun a0 => @bindfeqv _ _ _ _ _ (find j) (fun j1 => guardC _ (j' == j1) (a' == a0)  _))).
  under eq_bind do under eq_bind do rewrite bindA.
  under eq_bind do under eq_bind do under eq_bind do rewrite -bindA.
  setoid_rewrite (bindfeqv (fun _ => guardfindC _ _ _ _)).
  under eq_bind do under eq_bind do rewrite -bindA.
  setoid_rewrite guardfindC.
  do 2 setoid_rewrite (findC _ _ b).
  rewrite (findC _ a b).
  rewrite remember_find.
  symmetry; rewrite remember_find; symmetry.
  apply: bindfeqv=>{}b'.
  case Hb : ((a' == b') || (a' == i') && (b' == j') || (a' == j') && (b' == i')).
  -  apply: bindfeqv=>{}b0.
    case H_b0: (b' == b0).
    2: by rewrite guardF  !bindfailf.
    rewrite guardT !bindskipf.
    apply: bindfeqv=>{}a0.
    case H_a0: (a' == a0); last first.
    + rewrite guardF !bindfailf.
      rewrite -{2}(find_lookup _ j fail).
      apply: bindfeqv=>{}j1.
      case (j' == j1).
      by rewrite guardT bindskipf. 
      by rewrite  guardF bindfailf. 
    + rewrite guardT !bindskipf.
    symmetry.

    apply: bindfeqv=>{}j0.
    case H_j0: (j' == j0).
    2: by rewrite guardF !bindfailf.
    rewrite guardT !bindskipf.
    apply: bindfeqv=>{}i0.
    case H_i0: (i' == i0).
    2: by rewrite guardF !bindfailf.
    rewrite guardT !bindskipf.
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
  -  move /orP /orP /norP in Hb.
    case Hb => [Hb0 /nandP Hb1].
    move /orP /orP /norP in Hb0.
    case: Hb0 => Hb0 /nandP Hb2.
    case: Hb1 => Hb1.
    case: Hb2 => Hb2.
    + admit. (* ok when lemmma proven *)
    + case Ha1 : (a' == i'). 
      * have Ha2 : (b' != i') by move /eqP in Ha1;rewrite -Ha1 eq_sym.
        (* back to first case*) admit.
      * (* back to first case*) admit.   
    case: Hb2 => Hb2. (* symmetric of first bullet*)
    +  admit.
    + admit.
Abort.


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