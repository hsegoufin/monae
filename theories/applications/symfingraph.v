From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section symfingraph.
Variable I : eqType.

Definition adjacent (l : seq (I * I)) a b :=
  ((a,b) \in l) || ((b,a) \in l).

Section expath.
Variables (n : nat) (l : n.-tuple (I * I)).
Definition lookup_vertex (p : 'I_n * bool) :=
  let p' := tnth l p.1 in if p.2 then p'.1 else p'.2.

Definition redge (v : 'I_n * bool) := (v.1, ~~ v.2).

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

End symfingraph.
