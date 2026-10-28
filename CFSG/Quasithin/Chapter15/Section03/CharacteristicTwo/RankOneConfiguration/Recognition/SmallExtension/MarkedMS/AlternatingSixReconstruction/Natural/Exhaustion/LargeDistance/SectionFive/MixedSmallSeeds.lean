module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowNormalizer

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeConjugateKernel

/-!
# Small critical seeds and backward shifts for a mixed-plane radical

The mixed plane in the literal symmetric-six quotient contains a unique
transposition. Thus any two small critical seeds contained in the same edge
kernel have the same image. Pullback through the original projection gives
equal joins with the starting two-core. Centralization by that core gives
equal actual commutator lines, and the full-cover kernel theorem gives equal
seed kernels. Simultaneous conjugation transports the comparison to every
original edge and to critical walks with the same first edge.

If the predecessor radius of a small critical walk has image larger than two,
some radius seed has a large critical image: otherwise all nonzero generators
would induce the same transposition. Choose its critical walk with the entire
original prefix retained. Its seed fills the first edge kernel modulo the
starting core, so any relative normalizer generating with the original
endpoint also generates with this selected endpoint. Apply the large-image
orbit escape and holomorph realization to obtain a backward shift of the
original walk, with the original generating edge condition, all overlapping
vertices, and an eligible starting seed.

This proves the large-predecessor-radius branch of the mixed-plane small-image
shift. The predecessor-radius-at-most-two branch, larger original Sylow
branches and distance-four residual exclusions remain necessary for the
unconditional large-distance theorem. Both moved covers, all central
attachments, the original radical distinction and the actual graph are
retained throughout.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii), (5.5)--(5.8), printed pp.866--867 and 915--920. This is a
specialization of the backward selection to the actual mixed-plane image;
it does not assume the replacement image is the full point core.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedSmallSeeds
local notation "S" => Equiv.Perm (Fin 6)

private theorem mixed_swap_unique (a b : S) (ha : a ∈ plus) (hb : b ∈ plus)
    (hsa : a.IsSwap) (hsb : b.IsSwap) : a = b := by
  have h : ∀ i : Fin 4, (planeWords 0 i).cycleType = {2} → planeWords 0 i = swap45 := by
    decide +kernel
  obtain ⟨i, rfl⟩ := (mem_plus_iff a).mp ha
  obtain ⟨j, rfl⟩ := (mem_plus_iff b).mp hb
  exact (h i (Equiv.Perm.isSwap_iff_cycleType.mp hsa)).trans
    (h j (Equiv.Perm.isSwap_iff_cycleType.mp hsb)).symm

private theorem conjugate_mixed_swap_unique (u a b : S)
    (ha : a ∈ plus.map (MulAut.conj u).toMonoidHom)
    (hb : b ∈ plus.map (MulAut.conj u).toMonoidHom)
    (hsa : a.IsSwap) (hsb : b.IsSwap) : a = b := by
  obtain ⟨a, ha, rfl⟩ := ha
  obtain ⟨b, hb, rfl⟩ := hb
  have hs (x : S) (hx : ((MulAut.conj u) x).IsSwap) : x.IsSwap := by
    obtain ⟨i, j, hij, he⟩ := hx
    have hh := congrArg (MulAut.conj u⁻¹) he
    have hi : (MulAut.conj u⁻¹) ((MulAut.conj u) x) = x := by
      change u⁻¹*(u*x*u⁻¹)*(u⁻¹)⁻¹=x
      group
    rw [hi] at hh
    change x = u⁻¹*Equiv.swap i j*(u⁻¹)⁻¹ at hh
    rw [←Equiv.swap_apply_apply] at hh
    exact ⟨_, _, u.symm.injective.ne hij, hh⟩
  exact congrArg (MulAut.conj u) (mixed_swap_unique a b ha hb (hs a hsa) (hs b hsb))

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

private theorem same_image_sup_core
    (s : FullSymmetricAction h e hz hn d)
    (A B : Subgroup (FreeAmalgam d.radical))
    (hA : A ≤ stabilizer d.radical (alpha d.radical))
    (hB : B ≤ stabilizer d.radical (alpha d.radical))
    (he : graphImage s A = graphImage s B) :
    Q d.radical (alpha d.radical) ⊔ A = Q d.radical (alpha d.radical) ⊔ B := by
  have hh := congrArg (Subgroup.comap s.projection) he
  change (A.comap (embedM d.radical) |>.map s.projection).comap s.projection =
    (B.comap (embedM d.radical) |>.map s.projection).comap s.projection at hh
  rw [comap_map_eq, comap_map_eq, s.projection_kernel] at hh
  have hm := congrArg (Subgroup.map (embedM d.radical)) hh
  rw [Subgroup.map_sup, Subgroup.map_sup,
    map_comap_eq_self (hA.trans_eq (stabilizer_m_base d.radical)),
    map_comap_eq_self (hB.trans_eq (stabilizer_m_base d.radical)),
    ←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at hm
  exact (sup_comm _ _).trans (hm.trans (sup_comm _ _))

private theorem equal_sup_critical_data
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    {a a' b' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) a b')
    (hp : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hq : (Q d.radical b').relIndex (Z d.radical a) < 4)
    (he : Q d.radical a ⊔ Z d.radical a' = Q d.radical a ⊔ Z d.radical b') :
    ⁅Z d.radical a, Z d.radical a'⁆ = ⁅Z d.radical a, Z d.radical b'⁆ ∧
      Z d.radical a ⊓ Q d.radical a' = Z d.radical a ⊓ Q d.radical b' := by
  have hQ : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color))
  have hA := critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
    (by rw [(replacementGeometry h d).distance_constant a p.start_color]
        exact replacementDistance_pos h d) p.critical
  have hB := critical_Z_le_stabilizer d.radical (replacementGeometry h d) a q.start_color
    (by rw [(replacementGeometry h d).distance_constant a q.start_color]
        exact replacementDistance_pos h d) q.critical
  have hcomm := (commutator_eq_of_centralizing_sup rfl hQ
    (hA.trans (Z_normalized d.radical a))).trans
      ((congrArg (fun E => ⁅Z d.radical a, E⁆) he).trans
        (commutator_eq_of_centralizing_sup rfl hQ
          (hB.trans (Z_normalized d.radical a))).symm)
  exact ⟨hcomm, small_critical_equal_commutators_kernel s hc p q hp hq hcomm⟩

/-- Inside one literal mixed edge kernel, two small critical seeds induce
one transposition. Their entire critical kernels and actual commutator lines
coincide, including the central attachment of the order-thirty-two cover. -/
theorem mixed_small_seeds_base_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' b' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) b')
    (hp : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hq : (Q d.radical b').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hpa : Z d.radical a' ≤ Q d.radical (beta d.radical))
    (hqb : Z d.radical b' ≤ Q d.radical (beta d.radical)) :
    Q d.radical (alpha d.radical) ⊔ Z d.radical a' =
        Q d.radical (alpha d.radical) ⊔ Z d.radical b' ∧
      ⁅Z d.radical (alpha d.radical), Z d.radical a'⁆ =
        ⁅Z d.radical (alpha d.radical), Z d.radical b'⁆ ∧
      Z d.radical (alpha d.radical) ⊓ Q d.radical a' =
        Z d.radical (alpha d.radical) ⊓ Q d.radical b' := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨x, hx, hpx⟩ := small_critical_image_eq_swap s hc p hp
  obtain ⟨y, hy, hqy⟩ := small_critical_image_eq_swap s hc q hq
  have himg {v : Vertex d.radical} (hv : Z d.radical v ≤ Q d.radical (beta d.radical)) :
      graphImage s (Z d.radical v) ≤ plus.map (MulAut.conj u).toMonoidHom := by
    change ((Z d.radical v).comap (embedM d.radical)).map s.projection ≤ _
    have hh := map_mono (f := s.projection) (comap_mono (f := embedM d.radical) hv)
    rw [Q_beta, comap_map_eq_self_of_injective (embedM_injective d.radical),
      SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s, him] at hh
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    exact hh
  have he : x=y := conjugate_mixed_swap_unique u x y
    (himg hpa (hpx ▸ mem_zpowers x)) (himg hqb (hqy ▸ mem_zpowers y)) hx hy
  have hEq : graphImage s (Z d.radical a') = graphImage s (Z d.radical b') := by
    rw [hpx, hqy, he]
  have hA := critical_Z_le_stabilizer d.radical (replacementGeometry h d)
    (alpha d.radical) rfl (replacementDistance_pos h d) p.critical
  have hB := critical_Z_le_stabilizer d.radical (replacementGeometry h d)
    (alpha d.radical) rfl (replacementDistance_pos h d) q.critical
  have hjoin := same_image_sup_core s _ _ hA hB hEq
  exact ⟨hjoin, equal_sup_critical_data s hc p q hp hq hjoin⟩


/-- The same full-kernel rigidity at every original edge. Both critical
walks and the common edge are transported by the same graph element. -/
theorem mixed_small_seeds_at_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' b' t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) a b')
    (hp : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hq : (Q d.radical b').relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t)
    (hpa : Z d.radical a' ≤ Q d.radical t)
    (hqb : Z d.radical b' ≤ Q d.radical t) :
    Q d.radical a ⊔ Z d.radical a' = Q d.radical a ⊔ Z d.radical b' ∧
      ⁅Z d.radical a, Z d.radical a'⁆ = ⁅Z d.radical a, Z d.radical b'⁆ ∧
      Z d.radical a ⊓ Q d.radical a' = Z d.radical a ⊓ Q d.radical b' := by
  obtain ⟨g, hg | hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · have hga : act d.radical g⁻¹ a = alpha d.radical := by
      rw [hg.1, act_mVertex, mul_inv_cancel]
      rfl
    have hgt : act d.radical g⁻¹ t = beta d.radical := by
      rw [hg.2, act_hVertex, mul_inv_cancel]
      rfl
    let f := (MulAut.conj g).toMonoidHom
    have hQa : (Q d.radical a).map f = Q d.radical (alpha d.radical) := by
      simpa only [Q_act, inv_inv, hga] using (Q_act d.radical g⁻¹ a).symm
    have hZa : (Z d.radical a).map f = Z d.radical (alpha d.radical) := by
      simpa only [Z_act, inv_inv, hga] using (Z_act d.radical g⁻¹ a).symm
    have hQt : (Q d.radical t).map f = Q d.radical (beta d.radical) := by
      simpa only [Q_act, inv_inv, hgt] using (Q_act d.radical g⁻¹ t).symm
    have p' := p.act g⁻¹
    have q' := q.act g⁻¹
    rw [hga] at p' q'
    have hidx {v : Vertex d.radical} :
        (Q d.radical (act d.radical g⁻¹ v)).relIndex (Z d.radical (alpha d.radical)) =
          (Q d.radical v).relIndex (Z d.radical a) := by
      rw [Q_act, inv_inv, ←hZa, relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    have hle {v : Vertex d.radical} (hv : Z d.radical v ≤ Q d.radical t) :
        Z d.radical (act d.radical g⁻¹ v) ≤ Q d.radical (beta d.radical) := by
      rw [Z_act, inv_inv, ←hQt]
      exact map_mono hv
    obtain ⟨hj, hc, hk⟩ := mixed_small_seeds_base_knownSimple hb u him p' q'
      (by rw [hidx]; exact hp) (by rw [hidx]; exact hq) (hle hpa) (hle hqb)
    have hmapZ (v : Vertex d.radical) : (Z d.radical v).map f =
        Z d.radical (act d.radical g⁻¹ v) := by rw [Z_act, inv_inv]
    have hmapQ (v : Vertex d.radical) : (Q d.radical v).map f =
        Q d.radical (act d.radical g⁻¹ v) := by rw [Q_act, inv_inv]
    refine ⟨?_, ?_, ?_⟩
    · apply map_injective (f := f) (MulAut.conj g).injective
      rw [Subgroup.map_sup, Subgroup.map_sup, hQa, hmapZ, hmapZ]
      exact hj
    · apply map_injective (f := f) (MulAut.conj g).injective
      rw [map_commutator, map_commutator, hZa, hmapZ, hmapZ]
      exact hc
    · apply map_injective (f := f) (MulAut.conj g).injective
      rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective,
        Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hZa, hmapQ, hmapQ]
      exact hk
  · have ha := p.start_color
    rw [hg.1] at ha
    cases ha

private theorem endpoint_seed_le_first_kernel
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    Z d.radical a' ≤ Q d.radical (p.walk.getVert 1) := by
  apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
  rw [SimpleGraph.dist_comm, p.dist_end, (replacementGeometry h d).distance_constant a' p.end_color]
  have hl : p.walk.length = replacementDistance h d := by
    exact p.length_eq_b
  have hb := replacementDistance_pos h d
  change p.walk.length-1 < replacementDistance h d
  omega

/-- The actual small critical walks with the same first edge have the same
full seed kernel and line; no abstract image comparison remains a premise. -/
theorem mixed_small_paths_same_first_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' b' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) a b')
    (hp : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hq : (Q d.radical b').relIndex (Z d.radical a) < 4)
    (he : q.walk.getVert 1 = p.walk.getVert 1) :
    Q d.radical a ⊔ Z d.radical a' = Q d.radical a ⊔ Z d.radical b' ∧
      ⁅Z d.radical a, Z d.radical a'⁆ = ⁅Z d.radical a, Z d.radical b'⁆ ∧
      Z d.radical a ⊓ Q d.radical a' = Z d.radical a ⊓ Q d.radical b' := by
  have hl : 0 < p.walk.length := by
    exact p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
  exact mixed_small_seeds_at_knownSimple hb u him p q hp hq hat
    (endpoint_seed_le_first_kernel (h := h) p) (he ▸ endpoint_seed_le_first_kernel (h := h) q)


private theorem relIndex_sup_of_normalized {H : Type*} [Group H]
    (A D : Subgroup H) (hn : D ≤ normalizer (A : Set H)) :
    A.relIndex (A ⊔ D) = A.relIndex D := by
  let J := A ⊔ D
  let : (A.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  have hi := relIndex_sup_left (D.subgroupOf J) (A.subgroupOf J)
  rw [←subgroupOf_sup le_sup_left le_sup_right, relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at hi
  exact hi

private theorem repath_through_predecessor
    {a a' b : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) a b)
    (hb : 2 ≤ replacementDistance h d)
    (hd : (cosetGraph d.radical).dist b (p.walk.getVert (p.walk.length-2)) ≤ 2) :
    ∃ r : CriticalPath d.radical (replacementGeometry h d) a b,
      ∀ i ≤ p.walk.length-2, r.walk.getVert i = p.walk.getVert i := by
  obtain ⟨w, hw⟩ := (cosetGraph_connected d.radical).exists_walk_length_eq_dist
    (p.walk.getVert (p.walk.length-2)) b
  have hwl : w.length ≤ 2 := by rw [hw, SimpleGraph.dist_comm]; exact hd
  let v := (p.walk.take (p.walk.length-2)).append w
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hdist : (cosetGraph d.radical).dist a b = replacementDistance h d :=
    q.shortest.symm.trans q.length_eq_b
  have hvlen : v.length ≤ replacementDistance h d := by
    simp only [v, SimpleGraph.Walk.length_append, SimpleGraph.Walk.take_length,
      inf_eq_left.mpr (Nat.sub_le _ _)]
    omega
  have hmin := SimpleGraph.dist_le v
  have hshort : v.length = (cosetGraph d.radical).dist a b := by omega
  refine ⟨⟨p.start_color, v, hshort, q.critical⟩, ?_⟩
  intro i hi
  change v.getVert i = p.walk.getVert i
  simp only [v, SimpleGraph.Walk.getVert_append', SimpleGraph.Walk.take_length,
    inf_eq_left.mpr (Nat.sub_le _ _), hi, ite_true, SimpleGraph.Walk.take_getVert,
    inf_eq_right.mpr hi]

/-- A predecessor radius with image larger than a line contains a genuinely
large critical seed in the mixed-plane branch. A collection of different
small seed images cannot account for its size: all would be the same
transposition and would have the same full critical kernel. -/
theorem mixed_predecessor_radius_large_seed_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hp : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hlarge : 2 < (Q d.radical a).relIndex
      (V d.radical (p.walk.getVert (p.walk.length-2)))) :
    ∃ c, (cosetGraph d.radical).dist c (p.walk.getVert (p.walk.length-2)) ≤ 2 ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) a c,
        4 ≤ (Q d.radical c).relIndex (Z d.radical a) ∧
        Z d.radical c ≤ Q d.radical (p.walk.getVert 1) ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert i) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let v := p.walk.getVert (p.walk.length-2)
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hv : color d.radical v = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    rw [hl]
    have he := replacementDistance_even h d
    rw [Nat.even_iff] at he ⊢
    omega
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hVa : (cosetGraph d.radical).dist v a + 2 ≤ replacementDistance h d := by
    rw [SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist a (p.walk.getVert (p.walk.length-2))+2 ≤ _
    rw [p.dist_start (Nat.sub_le _ _)]
    omega
  have hVedge : V d.radical v ≤ Q d.radical (p.walk.getVert 1) := by
    apply V_le_Q_of_dist_add_two_lt d.radical (geometry := replacementGeometry h d) hv
    have hd := SimpleGraph.dist_le ((p.walk.drop 1).take (p.walk.length-3))
    rw [SimpleGraph.Walk.take_length, SimpleGraph.Walk.drop_length,
      inf_eq_left.mpr (by omega : p.walk.length-3 ≤ p.walk.length-1),
      SimpleGraph.Walk.drop_getVert, show 1+(p.walk.length-3)=p.walk.length-2 by omega] at hd
    change (cosetGraph d.radical).dist v (p.walk.getVert 1)+2 < replacementDistance h d
    rw [SimpleGraph.dist_comm]
    change (cosetGraph d.radical).dist (p.walk.getVert 1) (p.walk.getVert (p.walk.length-2))+2 < _
    omega
  by_contra! hbad
  have hVJ : V d.radical v ≤ Q d.radical a ⊔ Z d.radical a' := by
    apply (V_le_iff d.radical hv _).mpr
    intro c hcol hcv
    by_cases hcQ : Z d.radical c ≤ Q d.radical a
    · exact hcQ.trans le_sup_left
    have hca : (cosetGraph d.radical).dist c a ≤ replacementDistance h d := by
      have hh := (cosetGraph_connected d.radical).dist_triangle (u := c) (v := v) (w := a)
      omega
    have hd : (cosetGraph d.radical).dist c a =
        criticalDistance d.radical c ((replacementGeometry h d).exists_critical c hcol) := by
      have hlo := criticalDistance_le d.radical c ((replacementGeometry h d).exists_critical c hcol) hcQ
      rw [(replacementGeometry h d).distance_constant c hcol] at hlo ⊢
      change _ = replacementDistance h d
      change replacementDistance h d ≤ _ at hlo
      omega
    let r : CriticalPath d.radical (replacementGeometry h d) c a :=
      CriticalPath.ofPair hcol ⟨hd, hcQ⟩
    let q₀ : CriticalPath d.radical (replacementGeometry h d) a c :=
      CriticalPath.ofPair p.start_color (critical_reverse_pair s hc r)
    obtain ⟨q, hprefix⟩ := repath_through_predecessor (h := h) p q₀ (by omega) hcv
    have hcV : Z d.radical c ≤ V d.radical v :=
      le_iSup_of_le c (le_iSup_of_le hcv le_rfl)
    have hcE : Z d.radical c ≤ Q d.radical (p.walk.getVert 1) := hcV.trans hVedge
    have hq : (Q d.radical c).relIndex (Z d.radical a) < 4 := by
      by_contra hn
      obtain ⟨i, hi, hne⟩ := hbad c hcv q (Nat.le_of_not_gt hn) hcE
      exact hne (hprefix i hi)
    have he := (mixed_small_seeds_at_knownSimple hb u him p q hp hq hat
      (endpoint_seed_le_first_kernel (h := h) p) hcE).1
    exact le_sup_right.trans he.symm.le
  have hA := critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
    (by rw [(replacementGeometry h d).distance_constant a p.start_color]
        exact replacementDistance_pos h d) p.critical
  have hidx : (Q d.radical a).relIndex (Q d.radical a ⊔ Z d.radical a') = 2 := by
    rw [relIndex_sup_of_normalized _ _ (hA.trans (Q_normalized d.radical a))]
    exact (small_critical_indices s hc p hp).2
  have hbound := relIndex_le_of_le_right hVJ (by rw [hidx]; decide)
  rw [hidx] at hbound
  exact (Nat.not_le_of_gt hlarge) hbound

private theorem mixed_large_seed_fills_edge_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a b t : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) a b)
    (hq : 4 ≤ (Q d.radical b).relIndex (Z d.radical a))
    (hat : Adjacent d.radical a t) (hqt : Z d.radical b ≤ Q d.radical t) :
    Q d.radical a ⊔ Z d.radical b = Q d.radical t := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [q.start_color] at hh
    cases he : color d.radical t <;> simp_all
  have hQ := Q_le_adjacent_h d.radical ht hat
  have hle : Q d.radical a ⊔ Z d.radical b ≤ Q d.radical t := sup_le hQ hqt
  have hedge : (Q d.radical a).relIndex (Q d.radical t) = 4 := by
    rw [edge_kernel_index s a t q.start_color hat,
      SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s, him,
      card_map_of_injective (MulAut.conj u).injective, card_plus]
  have hA := critical_Z_le_stabilizer d.radical (replacementGeometry h d) a q.start_color
    (by rw [(replacementGeometry h d).distance_constant a q.start_color]
        exact replacementDistance_pos h d) q.critical
  have hidx : (Q d.radical a).relIndex (Q d.radical a ⊔ Z d.radical b) =
      (Q d.radical a).relIndex (Z d.radical b) :=
    relIndex_sup_of_normalized _ _ (hA.trans (Q_normalized d.radical a))
  have hfour := reverse_critical_image_four_le s hc (replacementDistance_pos h d) q hq
  have hmul := relIndex_mul_relIndex (Q d.radical a)
    (Q d.radical a ⊔ Z d.radical b) (Q d.radical t) le_sup_left hle
  rw [hedge, hidx] at hmul
  have hpos : 0 < (Q d.radical a ⊔ Z d.radical b).relIndex (Q d.radical t) := by
    nlinarith
  have he : (Q d.radical a ⊔ Z d.radical b).relIndex (Q d.radical t) = 1 := by
    nlinarith
  exact le_antisymm hle (relIndex_eq_one.mp he)

/-- A large predecessor radius discharges the small-image backward-shift
selection on the original walk. The generating edge is selected using the
original endpoint, and all overlap vertices of that original walk remain. -/
theorem mixed_small_large_radius_backward_shift_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hp : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hlarge : 2 < (Q d.radical (alpha d.radical)).relIndex
      (V d.radical (p.walk.getVert (p.walk.length-2)))) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
          stabilizer d.radical (alpha d.radical) ∧
      ∃ c, Adjacent d.radical c t ∧
        ∃ r : CriticalPath d.radical (replacementGeometry h d) c
            (p.walk.getVert (p.walk.length-2)),
          r.walk.getVert 1 = t ∧
          (∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i) ∧
          ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨b, _, q, hq, hqe, hprefix⟩ := mixed_predecessor_radius_large_seed_knownSimple hb u him p hp hlarge
  have hl : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
  have hat₀ : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0)
      (p.length_eq_b ▸ replacementDistance_pos h d)
  have hfill := mixed_large_seed_fills_edge_knownSimple hb u him q hq hat₀ hqe
  have hseed : Z d.radical a' ≤ Q d.radical (alpha d.radical) ⊔ Z d.radical b :=
    (endpoint_seed_le_first_kernel (h := h) p).trans hfill.symm.le
  obtain ⟨P, hP⟩ := large_distance_mixed_original_sylow_knownSimple hb u him
  obtain ⟨t, hat, hgen⟩ := SylowNormalizer.sylow_critical_generating_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb P hP p
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  let N := normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
    stabilizer d.radical (alpha d.radical)
  have hQN : Q d.radical (alpha d.radical) ≤ N :=
    le_inf ((Q_le_adjacent_h d.radical ht hat).trans (Q d.radical t).le_normalizer)
      (fun _ hx => hx.1)
  have hgenq : N ⊔ Z d.radical b = stabilizer d.radical (alpha d.radical) := by
    apply le_antisymm
    · exact sup_le inf_le_right (critical_Z_le_stabilizer d.radical (replacementGeometry h d)
        (alpha d.radical) rfl (replacementDistance_pos h d) q.critical)
    · rw [←hgen]
      exact sup_le le_sup_left (hseed.trans (sup_le (hQN.trans le_sup_left) le_sup_right))
  have hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s, him]
    exact map_mono (plus_le_exceptional.trans
      CFSG.Quasithin.ChapterC.NaturalSixControl.Model.pointCore_eq_exceptional.symm.le)
  obtain ⟨c, hct, hel⟩ := exists_eligible_neighbor_at_edge s hc hb rfl hat
  obtain ⟨k, hk, r, hrt, hover, hidx⟩ := SylowNormalizer.relative_large_backward_shift
    s hc hb u hR q hq hat hct hgenq hel
  have hfix : act d.radical k t = t := hk
  have hpred : q.walk.getVert (q.walk.length-2) = p.walk.getVert (p.walk.length-2) := by
    rw [hl]; exact hprefix _ le_rfl
  have out : ∃ r : CriticalPath d.radical (replacementGeometry h d) (act d.radical k c)
      (q.walk.getVert (q.walk.length-2)),
      r.walk.getVert 1 = t ∧
      (∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i) := by
    exact ⟨r, hrt, fun i hi => (hover i (by rwa [hl])).trans (hprefix i hi)⟩
  rw [hpred] at out
  obtain ⟨r, hrt, hover⟩ := out
  refine ⟨t, hat, hgen, act d.radical k c, ?_, r, hrt, hover, ?_⟩
  · simpa only [hfix] using (adjacent_act_iff d.radical k c t).mpr hct
  · intro hle
    exact hel (relIndex_eq_one.mp (hidx.symm.trans (relIndex_eq_one.mpr hle)))

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedSmallSeeds
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
