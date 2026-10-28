module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.NaturalMovement
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PairedTranspositionMovement
public import Theory.Representation.NormalElementaryQuotient.SubgroupSpaceTransport
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.NaturalMovement
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowNormalizer

/-!
# Small-backward exclusion on both full moving covers

Suppose the first edge of a small critical path moves its critical line.
The orbit of the opposite seed has at least four images. Since the midpoint
core fixes the entire orbit displacement, the large-fixer calculation makes
its action quadratic on the whole starting seed, including the attachment.

The small opposite seed has a transposition image. If every transposition
in the midpoint-core image were equal, its normalizing edge would fix the
critical line. Thus the image contains two distinct transpositions. Their
full-cover calculation gives
`[Z_c,Q_a] = [Z_c,Z_z] ∨ [Z_c ∩ Q_z,Q_a]`.
The fixed-index bound makes this whole movement have order at most eight.

The selected endpoint actor normalizes the second summand and fixes the
first. When it generates the midpoint stabilizer with the actual edge
kernel, the whole movement is invariant. The small automorphism bound makes
it residual-fixed; the small critical pair then makes its critical line
central, contradicting the strict Baumann slice.

The final application uses the proved relative-normalizer identity when the
radical image has order sixteen. It excludes the small backward alternative
for both cover orders, with the same full endpoint restriction, central
attachment, exact critical commutator, strict slice and literal path.
Other relative normalizers and the large-image and large-slice terminal
contradictions remain separate obligations. No whole residual-core bound or
unconditional distance-four exclusion is asserted.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii), (5.2)(ii) and (5.12)(1)--(2), printed
pp.867,914--915,924--926. Internal imports reuse the checked orbit and
fixed-index proofs without changing their existing public boundaries.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.GroupTheory Representation.NormalElementaryQuotient
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
private theorem cover_small_moved_line_control
    (A P T : Subgroup d.overgroup) (hAP : A ≤ P)
    (hPN : T ≤ normalizer (P : Set d.overgroup))
    (hquad : ⁅replacementMoved d,P⁆ ≤ centralizer (P : Set d.overgroup))
    (hne : ¬ A ≤ pCore 2 d.overgroup)
    (hsmall : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2)
    (hmove : ¬ T ≤ normalizer ((⁅replacementMoved d,A⁆ : Subgroup d.overgroup) : Set _)) :
    ⁅replacementMoved d,P⁆ ≤ ⁅replacementMoved d,A⁆ ⊔
      ⁅replacementMoved d ⊓ centralizer (A : Set d.overgroup),P⁆ := by
  let := replacementMoved_normal h d
  let U := replacementMoved d
  let F := U ⊓ centralizer (A : Set d.overgroup)
  have hker := s.projection_kernel.trans (moved_centralizer s).symm
  let : IsElementaryAbelian 2 (P.map s.projection) :=
    elementary_of_faithful_quadratic (naturalRepresentation (Fin 6))
      (naturalRepresentation_injective (Fin 6) (by decide)) _
      (image_quadratic_of_commutator s P hquad)
  have hi : fixedCodim (coverAction s) (A.map s.projection) ≤ 1 := by
    rw [centralizer_index_eq_fixedCodim U s.projection s.surjective hker] at hsmall
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hsmall
  have hin : fixedCodim (naturalRepresentation (Fin 6)) (A.map s.projection) ≤ 1 := by
    have hh := ((cover_model s).fixedCodim_bounds (A.map s.projection)).1
    rw [Subgroup.map_id] at hh
    exact hh.trans hi
  have hnA : A.map s.projection ≠ ⊥ := by
    intro he
    exact hne (s.projection_kernel ▸ (map_eq_bot_iff A).mp he)
  obtain ⟨t,ht,hs,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers
    (A.map s.projection) hnA hin
  have htP : t ∈ P.map s.projection := (map_mono hAP) ht
  have hpairs : ∃ t' ∈ P.map s.projection, t'.IsSwap ∧ t≠t' := by
    by_contra! hbad
    have hfix (x : d.overgroup) (hx : x∈T) :
        s.projection x*t*(s.projection x)⁻¹=t := by
      have hm : s.projection x*t*(s.projection x)⁻¹ ∈ P.map s.projection := by
        obtain ⟨a,ha,rfl⟩ := htP
        refine ⟨x*a*x⁻¹,(mem_normalizer_iff.mp (hPN hx) a).mp ha,by simp⟩
      have hswap : (s.projection x*t*(s.projection x)⁻¹).IsSwap := by
        rw [Equiv.Perm.isSwap_iff_cycleType,Equiv.Perm.cycleType_conj]
        exact Equiv.Perm.isSwap_iff_cycleType.mp hs
      exact (hbad _ hm hswap).symm
    have hTA : ⁅T,A⁆ ≤ centralizer (U : Set d.overgroup) := by
      rw [←hker,←Subgroup.map_eq_bot_iff,map_commutator]
      apply commutator_eq_bot_iff_le_centralizer.mpr
      rintro _ ⟨x,hx,rfl⟩ a ha
      rw [he] at ha
      obtain ⟨n,rfl⟩ := mem_zpowers_iff.mp ha
      exact ((Commute.zpow_right (show Commute (s.projection x) t from
        mul_inv_eq_iff_eq_mul.mp (hfix x hx)) n).eq).symm
    exact hmove (by
      rw [commutator_comm U A]
      exact SylowNormalizer.fixed_mod_central_normalizes A U T
        (by rw [normalizer_eq_top]; exact le_top)
        (by rw [normalizer_eq_top]; exact le_top) hTA)
  obtain ⟨t',ht',hs',hnt⟩ := hpairs
  have hF : subgroupSpace U F = fixedSpace (coverAction s) (A.map s.projection) := by
    ext v
    change ((v.toMul : d.overgroup) ∈ U ∧ (v.toMul : d.overgroup) ∈ centralizer (A : Set d.overgroup)) ↔ _
    simp only [v.toMul.property,true_and]
    exact (mem_fixedSpace_image U s.projection s.surjective hker A v).symm
  have hwhole (B : Subgroup d.overgroup) : subgroupSpace U ⁅U,B⁆ =
      subspaceCommutator (coverAction s) ⊤ (B.map s.projection) := by
    rw [subgroupSpace_commutator U s.projection s.surjective hker U B le_rfl]
    congr 1
    ext v
    exact iff_of_true v.toMul.property trivial
  have hFcomm : subgroupSpace U ⁅F,P⁆ =
      subspaceCommutator (coverAction s) (fixedSpace (coverAction s) (A.map s.projection))
        (P.map s.projection) := by
    rw [subgroupSpace_commutator U s.projection s.surjective hker F P inf_le_left,hF]
    rfl
  have hm := PairedTranspositionMovement.cover_movement_le (coverAction s) (cover_model s)
    (P.map s.projection) t t' htP ht' hs hs' hnt
  rw [←he,←hwhole P,←hwhole A,←hFcomm,←subgroupSpace_sup U
    (commutator_le_left U A) ((commutator_mono inf_le_left le_rfl).trans (commutator_le_left U P))] at hm
  intro v hv
  exact hm (show Additive.ofMul (⟨v,(commutator_le_left U P) hv⟩ : U) ∈ subgroupSpace U ⁅U,P⁆ from hv)

include s in
private theorem small_orbit_movement
    (hc : DistanceTwo.CentralLayer d)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < 4)
    (T P : Subgroup (FreeAmalgam d.radical))
    (hTG : T ≤ stabilizer d.radical a) (hTP : IsPGroup 2 T)
    (hTedge : T ≤ Q d.radical (p.walk.getVert 1))
    (hPT : P ≤ T) (hPN : T ≤ normalizer (P : Set (FreeAmalgam d.radical)))
    (hAP : Z d.radical z ≤ P)
    (hfix : P ≤ centralizer ((⁅Z d.radical a,Z d.radical z⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set _))
    (hmove : ¬ T ≤ centralizer ((⁅Z d.radical a,Z d.radical z⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ⁅Z d.radical a,P⁆ = ⁅Z d.radical a,Z d.radical z⁆ ⊔
      ⁅Z d.radical a ⊓ Q d.radical z,P⁆ ∧
      ⁅Z d.radical a,P⁆ ≤ centralizer (P : Set (FreeAmalgam d.radical)) ∧
      Nat.card (⁅Z d.radical a,P⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 8 := by
  let Z₀ := Z d.radical a
  let A := Z d.radical z
  let K := Z₀ ⊓ Q d.radical z
  let D := ⁅Z₀,A⁆
  let E := componentOrbit A T
  let J := componentOrbit D T
  let := finite_stabilizer d.radical a
  let : Finite T := Finite.of_injective (inclusion hTG) (inclusion_injective _)
  let : Finite P := Finite.of_injective (inclusion hPT) (inclusion_injective _)
  have hTZ : T ≤ normalizer (Z₀ : Set (FreeAmalgam d.radical)) := hTG.trans (Z_normalized d.radical a)
  have hAZ : A ≤ normalizer (Z₀ : Set (FreeAmalgam d.radical)) := (hAP.trans hPT).trans hTZ
  have hEP : E ≤ P := by
    apply iSup_le
    intro x
    exact (map_mono hAP).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hPN x.property))
  have hJG : ⁅Z₀,E⁆ = J := SylowKernelPair.orbit_commutator Z₀ A T hAZ hTZ
  have hJP : J ≤ centralizer (P : Set (FreeAmalgam d.radical)) := by
    apply iSup_le
    intro x
    have hn : T ≤ normalizer (centralizer (P : Set (FreeAmalgam d.radical)) : Set _) :=
      hPN.trans (normalizer_le_normalizer_centralizer P)
    exact (map_mono (le_centralizer_iff.mp hfix)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (hn x.property))
  have hEA : ⁅U d.radical a,E⁆ ≤ J :=
    (commutator_mono (DistanceEight.U_le_Z d.radical a) le_rfl).trans_eq hJG
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a p.start_color
  have hEbound : E ≤ i.range := (hEP.trans (hPT.trans hTG)).trans_eq hir.symm
  have hEm : (E.comap i).map i = E := map_comap_eq_self hEbound
  have hTm : (T.comap i).map i = T := map_comap_eq_self (hTG.trans_eq hir.symm)
  have hEi : 4 ≤ ((pCore 2 d.overgroup).map i).relIndex E := by
    by_contra! hs
    have hiE : Nat.card ((E.comap i).map s.projection) < 4 := by
      rwa [←hEm,relIndex_map_map_of_injective _ _ hi,←s.projection_kernel,relIndex_ker] at hs
    have hpE : IsPGroup 2 ((E.comap i).map s.projection) :=
      (((hTP.to_le (hEP.trans hPT)).comap_of_injective i hi).map s.projection)
    obtain ⟨n,hn⟩ := hpE.exists_card_eq
    have hiE2 : Nat.card ((E.comap i).map s.projection) ≤ 2 := by
      rw [hn] at hiE ⊢
      have hn2 : n < 2 := (Nat.pow_lt_pow_iff_right (by decide)).mp hiE
      interval_cases n <;> decide
    have hEN : T.comap i ≤ normalizer (E.comap i : Set d.overgroup) :=
      (comap_mono (le_normalizer_componentOrbit A T)).trans (le_normalizer_comap i)
    have hTE : ⁅T,E⁆ ≤ Q d.radical a := by
      have hh := map_mono (f := i)
        (commutator_le_ker_of_normalized_image_card_le_two s.projection _ _ hEN hiE2)
      rwa [map_commutator,hTm,hEm,s.projection_kernel,hiQ] at hh
    have hTA : ⁅T,A⁆ ≤ centralizer (Z₀ : Set (FreeAmalgam d.radical)) :=
      ((commutator_mono le_rfl (le_componentOrbit A T)).trans hTE).trans
        (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
          (Z_centralizes_Q d.radical a p.start_color)))
    have hTD : T ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
      dsimp only [D]
      rw [commutator_comm]
      exact SylowNormalizer.fixed_mod_central_normalizes A Z₀ T hAZ hTZ hTA
    exact hmove (hTD.trans (normalizer_le_centralizer_of_card_two D
      (small_critical_commutator_card s hc p hsmall)))
  have hpos : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
  have hat : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hpos
  have hquad : ⁅Z₀,P⁆ ≤ centralizer (P : Set (FreeAmalgam d.radical)) :=
    edge_large_fixer_quadratic s hc p.start_color hat E P
      (hEP.trans (hPT.trans hTedge)) (hPT.trans hTedge)
      (by rw [hiQ] at hEi; omega) (le_centralizer_iff.mp (hEA.trans hJP))
  have hPm : (P.comap i).map i = P :=
    map_comap_eq_self ((hPT.trans hTG).trans_eq hir.symm)
  have hAm : (A.comap i).map i = A :=
    map_comap_eq_self ((hAP.trans (hPT.trans hTG)).trans_eq hir.symm)
  have hq₀ : ⁅replacementMoved d,P.comap i⁆ ≤ centralizer (P.comap i : Set d.overgroup) := by
    intro x hx y hy
    apply hi
    simp only [map_mul]
    have hh := mem_map_of_mem i hx
    rw [map_commutator,hiU,hPm] at hh
    exact hquad ((commutator_mono (DistanceEight.U_le_Z d.radical a) le_rfl) hh) (i y) hy
  have hn₀ : ¬ A.comap i ≤ pCore 2 d.overgroup := by
    intro hh
    have hAQ : A ≤ Q d.radical a := by
      have he := map_mono (f := i) hh
      rwa [hAm,hiQ] at he
    have hidx := (small_critical_indices s hc p hsmall).2
    have he := relIndex_eq_one.mpr hAQ
    change (Q d.radical a).relIndex A = 2 at hidx
    omega
  have hsmall₀ : (centralizer (A.comap i : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    let := finite_Z d.radical a
    rw [←SmallMover.centralizer_index_map i hi (replacementMoved d) (A.comap i),hiU,hAm]
    apply (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a) index_ne_zero_of_finite).trans
    apply (relIndex_le_of_le_left
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical z p.end_color))) index_ne_zero_of_finite).trans
    exact (small_critical_indices s hc p hsmall).1.le
  have hnorm₀ : T.comap i ≤ normalizer (P.comap i : Set d.overgroup) :=
    (comap_mono hPN).trans (le_normalizer_comap i)
  have hmove₀ : ¬ T.comap i ≤ normalizer ((⁅replacementMoved d,A.comap i⁆ :
      Subgroup d.overgroup) : Set d.overgroup) := by
    intro hh
    have hm := (map_mono (f := i) hh).trans (le_normalizer_map i)
    rw [hTm,map_commutator,hiU,hAm,small_critical_moving_commutator_eq s hc p hsmall] at hm
    exact hmove (hm.trans (normalizer_le_centralizer_of_card_two D
      (small_critical_commutator_card s hc p hsmall)))
  have hcontrol := map_mono (f := i) (cover_small_moved_line_control s
    (A.comap i) (P.comap i) (T.comap i) (comap_mono hAP) hnorm₀ hq₀ hn₀ hsmall₀ hmove₀)
  have hFK : (replacementMoved d ⊓ centralizer (A.comap i : Set d.overgroup)).map i ≤ K := by
    rintro x ⟨v,hv,rfl⟩
    have hZU : i v ∈ U d.radical a := hiU ▸ mem_map_of_mem i hv.1
    have hZ : i v ∈ Z d.radical a := DistanceEight.U_le_Z d.radical a hZU
    refine ⟨hZ,?_⟩
    rw [←C_eq_Q s hc z p.end_color]
    refine ⟨Z_le_stabilizer_of_dist_le a _ p.critical.1.le hZ,?_⟩
    intro x hx
    have hxA : x ∈ (A.comap i).map i := hAm.symm ▸ hx
    obtain ⟨y,hy,rfl⟩ := hxA
    simpa only [map_mul] using congrArg i (hv.2 y hy)
  rw [map_commutator,hiU,hPm,Subgroup.map_sup,map_commutator,hiU,hAm,
    small_critical_moving_commutator_eq s hc p hsmall,map_commutator,hPm] at hcontrol
  have hwhole : ⁅Z₀,P⁆ ≤ D ⊔ ⁅K,P⁆ := by
    change ⁅Z d.radical a,P⁆ ≤ _
    rw [seed_commutator_eq_moving (h := h) (e := e) (hz := hz) p.start_color hat P (hPT.trans hTedge)]
    exact hcontrol.trans (sup_le_sup_left (commutator_mono hFK le_rfl) D)

  have hcardH : Nat.card (⁅Z₀,P⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 8 := by
    let H := ⁅Z₀,P⁆
    have hHU : H ≤ U d.radical a := by
      have hl : 0 < p.walk.length := p.length_eq_b ▸ replacementDistance_pos h d
      have hat : Adjacent d.radical a (p.walk.getVert 1) := by
        apply (cosetGraph_adj d.radical _ _).mp
        simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hl
      change ⁅Z d.radical a,P⁆ ≤ U d.radical a
      rw [seed_commutator_eq_moving (h := h) (e := e) (hz := hz) p.start_color hat P (hPT.trans hTedge)]
      exact le_normalizer_iff_commutator_le_left.mp ((hPT.trans hTG).trans (U_normalized a))
    have hPm : (P.comap i).map i = P := map_comap_eq_self ((hPT.trans hTG).trans_eq hir.symm)
    have hPcard : 4 ≤ Nat.card ((P.comap i).map s.projection) := by
      have hh := hEi.trans (relIndex_le_of_le_right hEP index_ne_zero_of_finite)
      rwa [←hPm,relIndex_map_map_of_injective _ _ hi,←s.projection_kernel,relIndex_ker] at hh
    have hq : ⁅replacementMoved d,P.comap i⁆ ≤ centralizer (P.comap i : Set d.overgroup) := by
      intro x hx y hy
      apply hi
      simp only [map_mul]
      have hxH : i x ∈ H := by
        have hh := mem_map_of_mem i hx
        rw [map_commutator,hiU,hPm] at hh
        exact commutator_mono (DistanceEight.U_le_Z d.radical a) le_rfl hh
      exact hquad hxH (i y) hy
    have hhi : 4 ≤ H.relIndex (U d.radical a) := by
      rw [←hiU,←relIndex_comap]
      apply (quadratic_cover_fixedIndex_four_le s _ hPcard hq).trans
      apply relIndex_le_of_le_left _ index_ne_zero_of_finite
      intro x hx y hy
      apply hi
      simp only [map_mul]
      exact hquad hx (i y) hy
    have hm := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) H
      (U d.radical a) bot_le hHU
    simp only [relIndex_bot_left] at hm
    have hUc : Nat.card (U d.radical a) ≤ 32 := by
      rw [←hiU,card_map_of_injective hi]
      rcases moved_card s with hh | hh <;> omega
    nlinarith
  exact ⟨le_antisymm hwhole
    (sup_le (commutator_mono le_rfl hAP) (commutator_mono inf_le_left le_rfl)),
    hquad,hcardH⟩

include s in
/-- On either full cover, a strict small backward kernel is incompatible
with its controlling actor and the actual edge-kernel generation. -/
theorem strict_small_actor_false
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {c z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) c z)
    (hsmall : (Q d.radical z).relIndex (Z d.radical c) < 4)
    (W : Subgroup (FreeAmalgam d.radical))
    (hgen : Q d.radical (p.walk.getVert 1) ⊔ W = stabilizer d.radical (p.walk.getVert 2))
    (hstrict : 2 < (B d.radical (p.walk.getVert 2) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c))
    (hWne : ¬ W ≤ Q d.radical (p.walk.getVert 2))
    (hWbound : ⁅(Z d.radical c ⊓ Q d.radical z) ⊔ Z d.radical (p.walk.getVert 2),W⁆ ≤
      Z d.radical (p.walk.getVert 2))
    (hWfix : ⁅Z d.radical c,Z d.radical z⁆ ≤ centralizer (W : Set (FreeAmalgam d.radical))) : False := by
  let a := p.walk.getVert 2
  let t := p.walk.getVert 1
  let K := Z d.radical c ⊓ Q d.radical z
  let D := ⁅Z d.radical c,Z d.radical z⁆
  let H := ⁅Z d.radical c,Q d.radical a⁆
  let F := ⁅K,Q d.radical a⁆
  let J := K ⊔ Z d.radical a
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have ha : color d.radical a = false := (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent d.radical c t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent d.radical a t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hTGc : Q d.radical t ≤ stabilizer d.radical c := fun _ hx => hx.2 _ (adjacent_symm d.radical hct)
  have hTGa : Q d.radical t ≤ stabilizer d.radical a := fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hWG : W ≤ stabilizer d.radical a := le_sup_right.trans_eq hgen
  have hWN : W ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
    le_normalizer_iff_commutator_le_left.mpr (hWbound.trans le_sup_right)
  have hZcQ : Z d.radical c ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c p.start_color)
    rw [(replacementGeometry h d).distance_constant _ p.start_color,p.dist_start (by omega)]
    exact hb2
  have hZwQ : Z d.radical z ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    exact hb2
  have hKV : K ≤ V d.radical a := inf_le_left.trans
    (le_iSup_of_le c (le_iSup_of_le (by rw [p.dist_start (by omega)]) le_rfl))
  have central_false (hcentral : D ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) : False := by
    have hTK : Q d.radical t ≤ normalizer (K : Set (FreeAmalgam d.radical)) := by
      have hh := le_inf hTGc (le_centralizer_iff.mp (hcentral.trans (centralizer_le hTGa)))
      rw [←small_critical_kernel_normalizer_eq_line_centralizer s hc p hsmall] at hh
      exact hh.trans inf_le_right
    have hTJ : Q d.radical t ≤ normalizer (J : Set (FreeAmalgam d.radical)) :=
      (le_inf hTK (hTGa.trans (Z_normalized d.radical a))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    have hGJ : stabilizer d.radical a ≤ normalizer (J : Set (FreeAmalgam d.radical)) := by
      rw [←hgen]
      exact sup_le hTJ hWN
    have hJB := normalized_radius_le_slice_of_actor_at s hb2 ha J W
      (sup_le hKV (Z_le_VBall d.radical _ 2)) hGJ hWG hWne hWbound
    let := finite_Z d.radical c
    have hi := relIndex_le_of_le_left (le_sup_left.trans hJB : K ≤ B d.radical a _)
      (index_ne_zero_of_finite (H := K.subgroupOf (Z d.radical c)))
    change (B d.radical a _).relIndex (Z d.radical c) ≤
      (Z d.radical c ⊓ Q d.radical z).relIndex (Z d.radical c) at hi
    rw [inf_relIndex_left,(small_critical_indices s hc p hsmall).1] at hi
    have hsmallSlice := (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical c)
      index_ne_zero_of_finite).trans hi
    exact (not_le_of_gt hstrict) hsmallSlice
  have hmove : ¬ Q d.radical t ≤ centralizer (D : Set (FreeAmalgam d.radical)) := by
    intro hh
    apply central_false
    apply le_centralizer_iff.mp
    rw [←hgen]
    exact sup_le hh (le_centralizer_iff.mp hWfix)
  have hQt : IsPGroup 2 (Q d.radical t) := by
    obtain ⟨i,_,_,hiR,_,_⟩ := SylowAdjacent.edge_coordinates (h := h) hc p.start_color hct
    rw [←hiR]
    exact (replacement_radical_isPGroup h d).map i
  have hPQ : Q d.radical a ≤ Q d.radical t := Q_le_adjacent_h d.radical ht hat
  have hDX : D ≤ X d.radical a := by
    have hVc : Z d.radical c ≤ V d.radical a :=
      le_iSup_of_le c (le_iSup_of_le (by rw [p.dist_start (by omega)]) le_rfl)
    have hVz : Z d.radical z ≤ V d.radical a :=
      le_iSup_of_le z (le_iSup_of_le (by rw [SimpleGraph.dist_comm,p.dist_end,hl]) le_rfl)
    exact (commutator_mono hVc hVz).trans (radius_bounds_general s hc hb2 ha c z).2.1
  have hfix : Q d.radical a ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (hDX.trans (fun _ hx => (mem_omegaCenter_iff.mp hx).2.2))
  obtain ⟨hdecomp,hquad,hcard⟩ := small_orbit_movement s hc p hsmall
    (Q d.radical t) (Q d.radical a) hTGc hQt le_rfl hPQ
    (hTGa.trans (Q_normalized d.radical a)) hZwQ hfix hmove
  have hHU : H ≤ U d.radical c := by
    change ⁅Z d.radical c,Q d.radical a⁆ ≤ U d.radical c
    rw [seed_commutator_eq_moving (h := h) (e := e) (hz := hz) p.start_color hct _ hPQ]
    exact le_normalizer_iff_commutator_le_left.mp ((hPQ.trans hTGc).trans (U_normalized c))
  have hHQ : H ≤ Q d.radical a := (hHU.trans (DistanceEight.U_le_Z d.radical c)).trans hZcQ
  have hHX : H ≤ X d.radical a := by
    let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) c p.start_color
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hHQ hx,
      elemPow_eq_one_of_isElementaryAbelian x ((hHU.trans (DistanceEight.U_le_Z d.radical c)) hx),hquad hx⟩
  have hTN : Q d.radical t ≤ normalizer (H : Set (FreeAmalgam d.radical)) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅Z d.radical c,Q d.radical a⁆).map _ = _
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical c (hTGc hx)),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a (hTGa hx))]
  have hcore := critical_kernel_core_control s hc hb p W hWG hWN
  have hFN : W ≤ normalizer (F : Set (FreeAmalgam d.radical)) := hcore.2.2
  have hWH : W ≤ normalizer (H : Set (FreeAmalgam d.radical)) := by
    change W ≤ normalizer ((⁅Z d.radical c,Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)
    rw [hdecomp]
    exact (le_inf ((le_centralizer_iff.mp hWfix).trans (Subgroup.centralizer_le_normalizer _)) hFN).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hGH : stabilizer d.radical a ≤ normalizer (H : Set (FreeAmalgam d.radical)) := by
    rw [←hgen]
    exact sup_le hTN hWH
  have hfixed := small_core_residual_fixed_knownSimple (h := h) (e := e) ha H hHQ
    ((Ltilde_le_stabilizer a).trans hGH) hcard
  exact central_false ((commutator_mono le_rfl hZwQ).trans
    ((le_inf hHX hfixed).trans (omega_fixed_central_of_small_critical s hc p hsmall a ha)))

include e hz hn in
/-- For radical image sixteen, both full moving covers exclude the small
backward alternative for the same chosen endpoint restriction. -/
theorem sixteen_full_seed_backward_large_knownSimple
    (hb : replacementDistance h d = 4)
    (himage : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    ∃ (W : Subgroup (FreeAmalgam d.radical)) (t c : Vertex d.radical),
      Z d.radical (p.walk.getVert 3) ≤ W ∧ W ≤ Z d.radical z ∧
      W.relIndex (Z d.radical z) ≤ 2 ∧
      ⁅Z d.radical (alpha d.radical),W⁆ = ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ∧
      (¬ W ≤ Q d.radical (alpha d.radical)) ∧
      Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ W = stabilizer d.radical (alpha d.radical) ∧
      ∃ q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2),
        q.walk.getVert 1 = t ∧ q.walk.getVert 2 = alpha d.radical ∧
        q.walk.getVert 3 = p.walk.getVert 1 ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical c) ∧
        ⁅(Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔ Z d.radical (alpha d.radical),W⁆ =
          ⁅Z d.radical (alpha d.radical),Z d.radical z⁆ ∧
        W ≤ normalizer (((Z d.radical c ⊓ Q d.radical (p.walk.getVert 2)) ⊔
          Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤
          centralizer (W : Set (FreeAmalgam d.radical)) ∧
        4 ≤ (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  obtain ⟨W,hFE,hWZ,hi,hcomm,hWne,_,t,c,hat,hct,hgen,_,q,hq1,hq2,hq3,
    _,hstrict,_,_,hDexact,hWN,hfix,_,_⟩ :=
    large_image_full_seed_backward_knownSimple (e := e) (hz := hz) (hn := hn) hb p hlarge
  have hgenQ : Q d.radical t ⊔ W = stabilizer d.radical (alpha d.radical) := by
    have hh := SylowLarge.sixteen_edge_relative_normalizer_knownSimple
      (e := e) (hz := hz) (hn := hn) (by omega : 2 < replacementDistance h d) himage rfl hat
    rwa [hh] at hgen
  have hback : 4 ≤ (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c) := by
    by_contra! hs
    apply strict_small_actor_false s hc hb q hs W
    · rwa [hq1,hq2]
    · rwa [hq2]
    · rwa [hq2]
    · rw [hq2,hDexact]
      exact ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
        (DistanceEight.U_le_Z d.radical _)
    · exact hfix
  exact ⟨W,t,c,hFE,hWZ,hi,hcomm,hWne,hat,hct,hgen,q,hq1,hq2,hq3,hstrict,hDexact,hWN,hfix,hback⟩



end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

