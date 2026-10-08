From mathcomp Require Import all_ssreflect.
Require Import preamble.
From mathcomp Require boolp.
Require Import hierarchy monad_lib  fail_lib state_lib.
Require Import monad_transformer.

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

Definition adjacent (l : seq (I * I)) a b :=
  ((a,b) \in l) || ((b,a) \in l).

Section expath.
Variables (n : nat) (l : n.-tuple (I * I)).
Definition lookup_vertex (p : 'I_n * bool) :=
  let p' := tnth l p.1 in if p.2 then p'.1 else p'.2.

Definition redge (v : 'I_n * bool) := (v.1, ~~ v.2).

(*
Definition vertex_adj r s :=
  lookup_vertex s == lookup_vertex (redge r).

Definition exist_path a b :=
  (a == b) ||
  [exists p0 : 'I_n * bool, [exists p : n.-bseq ('I_n * bool),
   (a == lookup_vertex p0) && path vertex_adj p0 p &&
   (b == lookup_vertex (redge (last p0 p)))]].
*)

Definition is_path_witness a b (p : seq ('I_n * bool)) :=
  path (adjacent l) a (map lookup_vertex p) &&
  (last a (map lookup_vertex p) == b).

Definition exists_path a b :=
  [exists p : (n*2).-bseq ('I_n * bool), is_path_witness a b p].

Lemma is_path_witness_cat (a b c : I) p1 p2 :
  is_path_witness a b p1 -> is_path_witness b c p2 ->
  is_path_witness a c (p1 ++ p2).
Proof.
case/andP => Hp1 /eqP Lp1 /andP[Hp2 Lp2].
by rewrite /is_path_witness map_cat cat_path Hp1 Lp1 Hp2 last_cat Lp1 Lp2.
Qed.

Lemma adjacent_vertex (a b : I) :
  adjacent l a b ->
  exists a', lookup_vertex a' = a.
Proof.
rewrite /lookup_vertex.
case/orP => /tnthP[i Hi].
- by exists (i, true) => /=; rewrite -Hi.
- by exists (i, false) => /=; rewrite -Hi.
Qed.

Lemma is_path_witness_ord (a b : I) p :
  is_path_witness a b p -> size p > 0 ->
  exists a' b',
    lookup_vertex a' = a /\
    path (relpre lookup_vertex (adjacent l)) a' p /\ last a' p = b'.
Proof.
case/andP.
case: p => //= c p /andP[Ha Hp] Lp ab.
case: (adjacent_vertex Ha) => a' Ha'.
exists a', (last c p).  
rewrite Ha' Ha /=.
do! split => //.
by rewrite -path_map.
Qed.

Lemma adjacent_sym (a b : I) :
  adjacent l a b = adjacent l b a.
Proof. by rewrite /adjacent orbC. Qed.

Lemma is_path_witness_rev (a b : I) p :
  is_path_witness a b p ->
  exists p', is_path_witness b a p'.
Proof.
elim: p a => [| c p IH] a /=.
  move/eqP<-.
  rewrite /is_path_witness.
  by exists nil => /=.
case/andP => /= /andP[ac Hp] Lp.
case: (IH (lookup_vertex c)).
  by rewrite /is_path_witness Hp.
move=> bc /andP[Hbc /eqP Lbc].
case: (adjacent_vertex ac) => a' Ha'.
exists (rcons bc a').
rewrite -cats1 /is_path_witness map_cat cat_path Hbc /= Lbc Ha'.
by rewrite adjacent_sym ac last_cat /=.
Qed.

Lemma is_path_witness_exists a b p :
  is_path_witness a b p -> exists_path a b.
Proof.
pose m := size p.
have : size p <= m by [].
clearbody m.
elim/ltn_ind: m p => m IH p Hsz Hp.
case: (leqP (size p) (n * 2)) => Hszp.
  by apply/existsP; exists (Bseq Hszp).
case: (is_path_witness_ord Hp).
  apply: leq_trans Hszp.
  by rewrite ltnS.
move=> a' [b'] [Ha] [Hp'] Lp'.
case/andP: Hp => Hp.
rewrite -{1}Ha last_map => Hb.
case: (shortenP Hp') Hb Lp' => /= p' {}Hp' Hu _ Hb Lp'.
move: (max_card (mem p')) => /=.
have /card_uniqP -> : uniq p' by case/andP: Hu.
rewrite card_prod /= card_ord card_bool => Hszp'.
apply/existsP; exists (Bseq Hszp') => /=.
by rewrite /is_path_witness -Ha path_map Hp' last_map Hb.
Qed.

Lemma exists_path_sym a b :
  exists_path a b = exists_path b a.
Proof.
apply/(sameP idP)/(iffP idP);
by case/existsP => /= p /is_path_witness_rev [p'] /is_path_witness_exists.
Qed.

(*
Lemma last_take A a i (s : seq A) :
  0 < i -> i < size s -> last a (take i s) = nth a s i.-1.
Proof.
move=> Hi Hsz. rewrite (last_nth a) size_take Hsz. -[RHS]nth_take.
 elim: s i => //= b s IH i.
*)

Definition is_edges_path a b p0 p :=
  (a == lookup_vertex (redge p0))
  && path (fun r s => lookup_vertex r == lookup_vertex (redge s)) p0 p
  && (b == lookup_vertex (last p0 p)).

Lemma is_edges_path_uniq a b p0 p :
  is_edges_path a b p0 p -> a != b ->
  exists q0 q, is_edges_path a b q0 q && uniq (unzip1 (q0 :: q)).
Proof.
rewrite /is_edges_path.
elim: p a p0 => /=[| p1 p IH] a p0.
  move=> Hp ab.
  by exists p0, nil => /=; rewrite Hp.
case/andP=> /andP[Ha] /andP[Hp1] Hp Hb ab.
case/boolP: (lookup_vertex p0 == b) => Hb0.
  exists p0, nil.
  by rewrite Ha /= eq_sym Hb0.
case: (IH (lookup_vertex p0) p1) => //.
  by rewrite Hp1 Hp.
move=> q0 [q] /andP[] /andP[] /andP[Hp0] Hq Hqb Hu.
case/boolP: (p0.1 \in unzip1 (q0 :: q)) => Hmem; last first.
  exists p0, (q0 :: q).
  by rewrite Ha Hqb Hmem [uniq _]Hu /= Hp0 Hq.
move: (Hmem); rewrite -index_mem.
set i := index p0.1 _.
rewrite size_map => Hi.
pose pi := nth p0 (q0 :: q) i.
have p0pi1 : p0.1 == pi.1.
  by rewrite /pi -(nth_map p0 p0.1 fst) // -/(unzip1 _) /i nth_index.
case/andP: Hu => Hup0 Hu.
case/boolP: (p0.2 == pi.2) => p0pi2.
  have p0pi : p0 = pi.
    rewrite (surjective_pairing p0) (eqP p0pi1) (eqP p0pi2).
    by rewrite -surjective_pairing.
  exists p0; exists (drop i q).
  rewrite Ha /=.
  move: Hq.
  case/boolP: (i == 0) => [/eqP|] Hi0.
    have p0q0 : p0 = q0 by rewrite p0pi /pi Hi0.
    by rewrite Hi0 drop0 p0q0 Hup0 Hu Hqb => ->.
  move: Hqb Hu.
  rewrite -{1 2 3}(cat_take_drop i q) cat_path last_cat.
  rewrite [unzip1 _]map_cat cat_uniq.
  rewrite (_ : last q0 _ = last q0 (take i.+1 (q0 :: q))) //.
  rewrite (take_nth p0) // last_rcons -/pi -p0pi.
  move=> -> /andP[_] /andP[Hu0 ->] /andP[_] -> /=.
  move: Hu0; rewrite -all_predC.
  move/allP/(_ p0.1).
  case: (p0.1 \in _) => //= /(_ isT).
  rewrite p0pi.
  rewrite -lt0n in Hi0.
  rewrite -{1}(prednK Hi0) (take_nth p0) ?prednK // map_rcons mem_rcons.
  by rewrite in_cons /pi -{1}(prednK Hi0) /= eqxx.
have p0pi : pi = redge p0.
  rewrite (surjective_pairing pi) (surjective_pairing p0).
  rewrite (eqP p0pi1) /redge /=.
  by case: p0.2 pi.2 p0pi2 => -[].
case/boolP: (i == size q) => Hiq.
  by move: ab; rewrite (eqP Ha) (eqP Hqb) (last_nth p0) -(eqP Hiq) -p0pi eqxx.
rewrite /= ltnS leq_eqVlt (negbTE Hiq) /= in Hi.
exists (nth p0 q i), (drop i.+1 q).
rewrite (eqP Ha).
move: (Hq) Hu.
rewrite -{1 2}(cat_take_drop i q) cat_path => /andP[_].
rewrite (drop_nth p0) //= => /andP[] /eqP <- ->.
rewrite (_ : last q0 _ = last q0 (take i.+1 (q0 :: q))) //.
rewrite (take_nth p0) 1?ltnW // last_rcons -/pi p0pi eqxx.
rewrite [unzip1 _]map_cat cat_uniq /= => /andP[_] /andP[_] /andP[-> ->].
rewrite -(last_cons p0) -drop_nth //.
by rewrite (eqP Hqb) -{1}(cat_take_drop i q) last_cat (drop_nth p0 Hi) eqxx.
Qed.

Lemma adjacent_lookup_vertex v :
  adjacent l (lookup_vertex v) (lookup_vertex (redge v)).
Proof.
rewrite /adjacent /lookup_vertex.
by case: v => i [] /=; rewrite -surjective_pairing mem_tnth // orbT.
Qed.

Definition exists_edges_path a b :=
  (a == b) ||
  [exists p0, [exists p : (n*2).-bseq ('I_n * bool), is_edges_path a b p0 p]].

Lemma exists_edges_pathP a b : exists_path a b = exists_edges_path a b.
Proof.
rewrite /exists_path /exists_edges_path.
case/boolP: (a == b) => /= ab.
  by apply/existsP; exists [bseq].
apply/(sameP idP)/(iffP idP).
  case/existsP => /= [p0] /existsP /= [p].
  case/andP => /andP[/eqP Ha] Hp Hb.
  have : is_path_witness a b (p0 :: p).
    rewrite /is_path_witness Ha last_map [_ == _]/= eq_sym Hb andbT.
    rewrite path_map /= adjacent_sym adjacent_lookup_vertex /=.
    move: Hp; clear.
    elim: (val p) p0 => //= v {}p IH w /andP[] /eqP ->.
    rewrite adjacent_sym adjacent_lookup_vertex /=.
    exact: IH.
  exact: is_path_witness_exists.
case/existsP => /= p.
rewrite /is_path_witness => Hp.
suff: exists p0 p', is_edges_path a b p0 p' /\ size p' <= size p.
  case=> p0 [p'] [Hp'] Hsz.
  apply/existsP; exists p0.
  have Hszp' : size p' <= n * 2 by rewrite (leq_trans Hsz) // size_bseq.
  by apply/existsP; exists (Bseq Hszp').
elim: (val p) a b ab Hp => /= [|c {}p IH] a b ab.
  by rewrite (negbTE ab).
case/andP => /andP[Ha Hp] Lp.
case/boolP: (lookup_vertex c == b) => cb.
  rewrite /is_edges_path.
  case/orP: Ha => /tnthP[i] Hi; [exists (i,false) | exists (i,true)];
    by exists nil; rewrite /= /lookup_vertex /= -Hi /= eqxx eq_sym cb.
move: (IH _ _ cb); rewrite Hp Lp => /(_ isT).
case=> [e] [p'] [Hp' Hsz].
case/orP: Ha => /tnthP [i] Hi; [exists (i,false) | exists (i,true)];
  exists (e::p') => /=; rewrite ltnS Hsz; case/andP: Hp' => /andP[] Hc Hp' Hb;
  by rewrite /is_edges_path /= Hb {1 2}/lookup_vertex /= -Hi /= eqxx Hc Hp'.
Qed.

Lemma is_edges_path_exists a b p0 p :
  is_edges_path a b p0 p -> uniq p -> exists_edges_path a b.
Proof.
move=> Hp /card_uniqP Hu.
move: (max_card (mem p)) => /=.
rewrite Hu card_prod /= card_ord card_bool => Hsz.
apply/orP; right; apply/existsP; exists p0.
by apply/existsP; exists (Bseq Hsz).
Qed.
End expath.

Definition shift_path n m (p : seq ('I_n * bool)) :=
  [seq (lshift m v.1, v.2) | v <- p].

Lemma is_path_witness_weaken n m (l : n.-tuple _) (l' : m.-tuple _) a b p :
  is_path_witness l a b p ->
  is_path_witness [tuple of l ++ l'] a b (shift_path m p).
Proof.
rewrite /is_path_witness => /andP[Hp Lp].
rewrite (_ : map _ _ =  map (lookup_vertex l) p); last first.
  rewrite -map_comp (eq_map (g:=lookup_vertex l)) // /comp => -[x y].
  rewrite /lookup_vertex /=.
  by case: y; rewrite tnth_lshift.
rewrite Lp andbT (sub_path _ Hp) //= => x y.
by case/orP => Hxy; apply/orP; [left | right]; rewrite mem_cat Hxy.
Qed.

Lemma lookup_vertex_lshift n m (l1 : n.-tuple _) (l2 : m.-tuple _) v d :
  lookup_vertex [tuple of l1 ++ l2] (lshift m v, d) = lookup_vertex l1 (v, d).
Proof. by rewrite /lookup_vertex /= tnth_lshift. Qed.

Lemma is_edges_path_weaken n (l : n.-tuple (I * I)) (ij : I * I) a b p0 p :
  is_edges_path [tuple of l ++ [tuple ij]] a b p0 p ->
  uniq (rshift n ord0 :: unzip1 (p0 :: p)) ->
  exists q0 q,
    p0 :: p = [seq (lshift 1 v.1, v.2) | v <- q0 :: q] /\
    is_edges_path l a b q0 q.
Proof.
move=> Hp Hu.
pose q := pmap (fun v : 'I_(n+1) * bool =>
                   if split v.1 is inl k then Some (k,v.2) else None)
               (p0 :: p).
have Hu0 : rshift n ord0 \notin unzip1 (p0 :: p) by case/andP: Hu.
have pq : map (fun v => (lshift 1 v.1, v.2)) q = p0 :: p.
  move: Hu0; clear; subst q.
  elim: (p0 :: p) => //= -[v d] {p0 p}p /= IH.
  rewrite in_cons negb_or => /andP[nv Hu].
  case: (splitP v) => /= j vj.
    rewrite IH //.
    congr ((_,_) :: _).
    by apply/val_inj; rewrite /= vj /=.
  case: j vj => -[] // Hj /= => vn.
  elim: (negP nv).
  by apply/eqP/val_inj; rewrite /= vn.
case: q pq => // q0 q [] p0q0 pq.
exists q0, q; split.
  by rewrite -p0q0 -pq.
rewrite /is_edges_path.
case/andP: Hp => /andP[].
rewrite -p0q0 lookup_vertex_lshift => ->.
rewrite -pq path_map.
rewrite (eq_path
           (e':=fun r s => lookup_vertex l r == lookup_vertex l (redge s)));
  last first.
  move=> v w /=.
  by rewrite !lookup_vertex_lshift /= -/(redge w) -surjective_pairing.
move->.
by rewrite /=last_map lookup_vertex_lshift -surjective_pairing.
Qed.

Lemma exists_path_split n (l : n.-tuple (I * I)) (i j a b : I) :
  exists_path l a b || exists_path l a i && exists_path l b j
  || exists_path l a j && exists_path l b i
  = exists_path [tuple of l ++ [:: (i, j)]] a b.
Proof.
set l' := [tuple of _].
case/boolP: (exists_path l a b) => /=.
  case/existsP => /= p Hp.
  symmetry.
  move: (is_path_witness_weaken [:: (i,j)] Hp).
  exact: is_path_witness_exists.
move=> Hab.
case/boolP: (_ && _) => /=.
  case/andP => Hai Hbj.
  symmetry.
  case/existsP: Hai => /= pai Hpai.
  case/existsP: Hbj => /= pbj Hpbj.
  move/(is_path_witness_weaken [tuple (i,j)]) in Hpai.
  move/(is_path_witness_weaken [tuple (i,j)]): Hpbj.
  case/is_path_witness_rev => pjb Hpjb.
  have Hpij : is_path_witness l' i j [:: (rshift n ord0, false)].
     rewrite /is_path_witness /= /lookup_vertex /= tnth_rshift /= eqxx.
     by rewrite /adjacent mem_cat mem_seq1 eqxx orbT.
  have : is_path_witness l' a b
               (shift_path 1 pai ++ [:: (rshift n ord0, false)] ++ pjb).
    exact/is_path_witness_cat/is_path_witness_cat/Hpjb/Hpij.
  exact: is_path_witness_exists.
move => aibj.
case/boolP: (_ && _) => /=.
  case/andP => Haj Hbi.
  symmetry.
  case/existsP: Haj => /= paj Hpaj.
  case/existsP: Hbi => /= pbi Hpbi.
  move/(is_path_witness_weaken [tuple (i,j)]) in Hpaj.
  move/(is_path_witness_weaken [tuple (i,j)]): Hpbi.
  case/is_path_witness_rev => pib Hpib.
  have Hpji : is_path_witness l' j i [:: (rshift n ord0, true)].
     rewrite /is_path_witness /= /lookup_vertex /= tnth_rshift /= eqxx.
     by rewrite /adjacent orbC mem_cat mem_seq1 eqxx orbT.
  have : is_path_witness l' a b
               (shift_path 1 paj ++ [:: (rshift n ord0, true)] ++ pib).
    exact/is_path_witness_cat/is_path_witness_cat/Hpib/Hpji.
  exact: is_path_witness_exists.
move=> ajbi.
symmetry.
apply/negbTE/negP; rewrite exists_edges_pathP.
case/boolP: (a == b) => ab.
  elim: (negP Hab).
  by apply/existsP; exists [bseq].
case/orP => [ab'|].
  by rewrite ab' in ab.
case/existsP => /=[p0] /existsP /=[p].
case/is_edges_path_uniq => // q0 [q] /andP[Hq Hu].
case/boolP: (rshift n ord0 \in unzip1 (q0 :: q)) => Hru; last first.
  case: (is_edges_path_weaken Hq).
    by rewrite [q0::q]lock /= -lock Hru Hu.
  move=> q0' [q'] [qq'] Hq'. 
  elim: (negP Hab).
  rewrite exists_edges_pathP.
  apply: (is_edges_path_exists Hq').
  move: Hu; rewrite qq' -[unzip1 _]map_comp /= => /andP[_].
  exact: map_uniq.
case/mapP: Hru => /= -[v d] Hi /= Hv; subst v.
move: (Hi); rewrite -index_mem.
set pij := index _ _ => Hpij.
case/andP: Hq Hu => /andP[].
rewrite -(cat_take_drop pij q) cat_path last_cat => Ha /andP[Hq1 Hq2] Hb.
rewrite -cat1s catA [unzip1 _]map_cat -!/(unzip1 _) cat_uniq.
case/andP => Hu1 /andP[Hu12 Hu2].
have Hq0 : last q0 (take pij q) = (rshift n ord0, d).
  have <- := nth_index q0 Hi.
  rewrite -/pij (last_nth q0) size_takel //.
  rewrite -{2}(cat_take_drop pij q) -[in RHS]cat1s catA nth_cat /=.
  by rewrite size_takel //= leqnn.
suff : exists_edges_path l a (lookup_vertex l' (rshift n ord0, ~~ d)) &&
       exists_edges_path l b (lookup_vertex l' (rshift n ord0, d)).
  clear -aibj ajbi.
  case: d; rewrite /lookup_vertex /= tnth_rshift /= -!exists_edges_pathP => Hab.
    by rewrite Hab in ajbi.
  by rewrite Hab in aibj.
apply/andP; split.
  case/boolP: (pij == 0) => pij0.
    move: Hq0; rewrite (eqP pij0) take0 /= => Hq0.
    rewrite /exists_edges_path.
    by rewrite (eqP Ha) Hq0 /redge /lookup_vertex /= tnth_rshift eqxx.
  set j' := lookup_vertex _ _.
  move: Hq1 Hu1 {Hu12 Hu2 Hq2}.
  rewrite -lt0n in pij0.
  rewrite -{1 2}(prednK pij0) (take_nth q0) ?prednK //.
  rewrite index_mem in Hpij.
  rewrite (_ : nth _ _ _ = nth q0 (q0 :: q) pij.-1.+1) // prednK //.
  rewrite [[:: q0]]lock.
  rewrite (nth_index q0 Hpij) -cats1 cat_path /= andbT => Hq Hu.
  have : is_edges_path l' a j' q0 (take pij.-1 q).
    by rewrite /is_edges_path Ha /= eq_sym.
  case/is_edges_path_weaken.
    move: Hu.
    rewrite catA [unzip1 _]map_cat cat_uniq => /andP[].
    rewrite -lock /= => ->.
    by rewrite negb_or !andbT.
  move=> q0' [q'] [qq'] Hq'.
  apply: (is_edges_path_exists Hq').
  move: Hu; rewrite -lock /= [unzip1 _]map_cat cat_uniq => /andP[_] /andP[].
  by move: qq' => /= [] _ -> /map_uniq /map_uniq.
rewrite -exists_edges_pathP exists_path_sym exists_edges_pathP.
set i' := lookup_vertex _ _.
case/boolP: (i' == b) => bi; first by rewrite /exists_edges_path bi.
have [qh [qt Hqht]] : exists qh qt, drop pij q = qh :: qt.
  move: Hb; rewrite Hq0; clear -bi.
  case: (drop pij q) => [| qh qt] /=; last by exists qh, qt.
  by rewrite eq_sym (negbTE bi).
have Hq : is_edges_path [tuple of l ++ [:: (i, j)]] i' b qh qt.
  rewrite /is_edges_path.
  move: Hq2 Hb; rewrite Hqht /= Hq0 => /andP[].
  by rewrite -/i' => -> -> ->.
case: (is_edges_path_weaken Hq).
  rewrite -Hqht /= Hu2 andbT.
  apply: contra Hu12 => Hu0.
  apply/hasP; exists (rshift n ord0) => //.
  rewrite [_ ++ _](take_nth q0 Hpij) [unzip1 _]map_rcons mem_rcons.
  by rewrite nth_index // in_cons eqxx.
move=> q0' [q' [qq' Hq']].
apply: (is_edges_path_exists Hq').
move: Hu2; rewrite Hqht qq' /= -[unzip1 _]map_comp => /andP[_].
exact: map_uniq.
Qed.

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
