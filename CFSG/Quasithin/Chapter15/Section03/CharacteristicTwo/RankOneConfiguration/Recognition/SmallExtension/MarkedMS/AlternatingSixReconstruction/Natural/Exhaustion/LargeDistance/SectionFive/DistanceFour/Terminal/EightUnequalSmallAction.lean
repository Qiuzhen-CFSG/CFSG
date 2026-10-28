module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightUnequalSmallKernel
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeCommonFixer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowAdjacent
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowCompatible
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.NonsylowImage
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SmallCriticalLine
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowNormalizer

/-!
# Abelian edge action in the omitted-core image-eight branch

An eight-element nonelementary permutation group containing a central
transposition is a product of its four-cycle and that transposition. Its
action is abelian. This finite calculation is used on the literal critical
seed image, with the full moving cover and central attachment retained.

Source: the unequal alternative in MS93 (5.12)(1), printed p.925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped commutatorElement Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
local notation "S" => Equiv.Perm (Fin 6)

private theorem eight_central_swap_commutative (E : Subgroup S)
    (hES : E ≤ sylowCarrier) (hE : Nat.card E = 8)
    (hne : ¬ IsElementaryAbelian 2 E) (v : S) (hv : v.IsSwap) (hvE : v ∈ E)
    (hcentral : E ≤ centralizer ({v} : Set S)) : IsMulCommutative E := by
  have hex : ∃ x ∈ E, x^2 ≠ 1 := by
    by_contra! hh
    exact hne (NonsylowImage.elementary_of_squares E hh)
  obtain ⟨x,hx,hx2⟩ := hex
  obtain ⟨i,hi⟩ := (mem_sylowCarrier_iff _).mp (hES hx)
  obtain ⟨j,hj⟩ := (mem_sylowCarrier_iff _).mp (hES hvE)
  have hxv : Commute x v := (hcentral hx v (Set.mem_singleton v)).symm
  let f : Fin 8 → E := fun k => ⟨x^(k.val%4)*v^(k.val/4),
    E.mul_mem (E.pow_mem hx _) (E.pow_mem hvE _)⟩
  have hfi : Function.Injective f := by
    have cert : ∀ i j : Fin 16, (sylowWords i)^2 ≠ 1 →
        (sylowWords j).cycleType = {2} → sylowWords i * sylowWords j = sylowWords j * sylowWords i →
        Function.Injective (fun k : Fin 8 =>
          (sylowWords i)^(k.val%4)*(sylowWords j)^(k.val/4)) := by decide +kernel
    intro k l he
    exact cert i j (hi ▸ hx2) (hj ▸ Equiv.Perm.isSwap_iff_cycleType.mp hv) (by rwa [hi,hj])
      (by simpa only [f,hi,hj] using congrArg Subtype.val he)
  have hfs : Function.Surjective f :=
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hfi,by simpa using hE.symm⟩).2
  refine ⟨⟨?_⟩⟩
  intro a b
  obtain ⟨k,rfl⟩ := hfs a
  obtain ⟨l,rfl⟩ := hfs b
  apply Subtype.ext
  exact (((Commute.refl x).pow_pow _ _).mul_right (hxv.pow_pow _ _)).mul_left
    (((hxv.symm).pow_pow _ _).mul_right ((Commute.refl v).pow_pow _ _)) |>.eq

private theorem eight_central_swap_commutative_conjugate (E : Subgroup S) (u : S)
    (hES : E ≤ sylowCarrier.map (MulAut.conj u).toMonoidHom) (hE : Nat.card E = 8)
    (hne : ¬ IsElementaryAbelian 2 E) (v : S) (hv : v.IsSwap) (hvE : v ∈ E)
    (hcentral : E ≤ centralizer ({v} : Set S)) : E ≤ centralizer (E : Set S) := by
  let f := (MulAut.conj u⁻¹).toMonoidHom
  have hback : (sylowCarrier.map (MulAut.conj u).toMonoidHom).map f = sylowCarrier := by
    rw [CubeCommonFixer.conjugate_twice,inv_mul_cancel,
      show (MulAut.conj (1 : S)).toMonoidHom = MonoidHom.id S from rfl,map_id]
  have hE' : Nat.card (E.map f) = 8 := by
    rw [card_map_of_injective (MulAut.conj u⁻¹).injective,hE]
  have hne' : ¬ IsElementaryAbelian 2 (E.map f) := by
    intro he
    let := he
    apply hne
    apply NonsylowImage.elementary_of_squares
    intro x hx
    apply (MulAut.conj u⁻¹).injective
    rw [map_pow,map_one]
    exact elemPow_eq_one_of_isElementaryAbelian _ (mem_map_of_mem f hx)
  have hv' : (f v).IsSwap := by
    have hc : IsConj v (f v) := isConj_iff.mpr ⟨u⁻¹,rfl⟩
    exact Equiv.Perm.isSwap_iff_cycleType.mpr
      ((Equiv.Perm.isConj_iff_cycleType_eq.mp hc).symm.trans
        (Equiv.Perm.isSwap_iff_cycleType.mp hv))
  have hcent : E.map f ≤ centralizer ({f v} : Set S) := by
    rintro _ ⟨x,hx,rfl⟩ y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    simpa only [map_mul] using congrArg f (hcentral hx v (Set.mem_singleton v))
  let := eight_central_swap_commutative (E.map f) ((map_mono hES).trans_eq hback)
    hE' hne' (f v) hv' (mem_map_of_mem f hvE) hcent
  intro x hx y hy
  apply (MulAut.conj u⁻¹).injective
  simpa only [Subgroup.coe_mul, f, MulEquiv.coe_toMonoidHom, map_mul] using congrArg Subtype.val
    (mul_comm (⟨f y,mem_map_of_mem f hy⟩ : E.map f) ⟨f x,mem_map_of_mem f hx⟩)

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- A fixed nonzero small-actor line makes the actual order-eight edge
image abelian on either entire moving cover. -/
private theorem eight_cover_fixed_line_abelian
    (s : FullSymmetricAction h e hz hn d)
    (hne₀ : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    (A : Subgroup d.overgroup) (hA : A ≤ d.radical)
    (hnot : ¬ A ≤ pCore 2 d.overgroup)
    (hidx : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2)
    (hfix : d.radical ≤ centralizer
      ((⁅replacementMoved d,A⁆ : Subgroup d.overgroup) : Set d.overgroup)) :
    ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup := by
  let := replacementMoved_normal h d
  let U := replacementMoved d
  let D := ⁅U,A⁆
  have hsmall : fixedCodim (naturalRepresentation (Fin 6)) (A.map s.projection) ≤ 1 := by
    have hbds := (cover_model s).fixedCodim_bounds (A.map s.projection)
    simp only [map_id] at hbds
    rw [Representation.NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)] at hidx
    exact hbds.1.trans ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hidx)
  have hnon : A.map s.projection ≠ ⊥ := by
    intro he
    exact hnot (s.projection_kernel ▸ (Subgroup.map_eq_bot_iff A).mp he)
  obtain ⟨v,hv,hvs,he⟩ := PointCoreTranspositionFixed.small_image_eq_zpowers
    (A.map s.projection) hnon hsmall
  have hcardA : Nat.card (A.map s.projection) = 2 := by
    rw [he,Nat.card_zpowers,hvs.orderOf]
  have hnorm : d.radical.map s.projection ≤ normalizer (A.map s.projection : Set S) := by
    rintro _ ⟨x,hx,rfl⟩
    apply mem_normalizer_iff_map_conj_eq.mpr
    let f := (MulAut.conj x).toMonoidHom
    have hUm : U.map f = U :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top x)
    have hQm : (pCore 2 d.overgroup).map f = pCore 2 d.overgroup :=
      mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top x)
    have hDm : D.map f = D := mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _ (hfix hx))
    have hnB : ¬ A.map f ≤ pCore 2 d.overgroup := by
      rw [←hQm,map_le_map_iff_of_injective (MulAut.conj x).injective]
      exact hnot
    have hcomm : ⁅U,A⁆ = ⁅U,A.map f⁆ := by
      rw [map_commutator,hUm] at hDm
      exact hDm.symm
    have him := cover_small_images_eq_of_commutator_eq s A (A.map f) hnot hnB hidx hcomm
    change (A.map s.projection).map (MulAut.conj (s.projection x)).toMonoidHom = A.map s.projection
    exact (SylowCompatible.image_conjugate s.projection A x).symm.trans him.symm
  obtain ⟨u,hN,_,_,_,_,_,_⟩ := Nonelementary.normalizer_small_movers_knownSimple
    (e := e) (hz := hz) (hn := hn) hne₀ hb
  have hN' : (normalizer (d.radical : Set d.overgroup)).map s.projection =
      sylowCarrier.map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d
      (fullSymmetricAction_knownSimple h e hz hn d hb)] at hN
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hE : Nat.card (d.radical.map s.projection) = 8 := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hne : ¬ IsElementaryAbelian 2 (d.radical.map s.projection) := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hcentral : d.radical.map s.projection ≤ centralizer ({v} : Set S) :=
    (hnorm.trans (normalizer_le_centralizer_of_card_two _ hcardA)).trans
      (centralizer_le (by intro x hx; obtain rfl := Set.mem_singleton_iff.mp hx; exact hv))
  have hab := eight_central_swap_commutative_conjugate (d.radical.map s.projection) u
    ((map_mono d.radical.le_normalizer).trans_eq hN') hE hne v hvs (map_mono hA hv) hcentral
  have hzero : (⁅d.radical,d.radical⁆ : Subgroup d.overgroup).map s.projection = ⊥ := by
    rw [map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr hab
  exact ((Subgroup.map_eq_bot_iff _).mp hzero).trans_eq s.projection_kernel

/-- Fixing the small critical line makes the literal image-eight edge action
abelian on the full endpoint seed, including its central attachment. -/
theorem eight_small_edge_fixed_line_abelian_knownSimple
    (s : FullSymmetricAction h e hz hn d) (hc : DistanceTwo.CentralLayer d)
    (hne₀ : ¬ IsElementaryAbelian 2 (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : 2 < replacementDistance h d)
    {c v : Vertex d.radical}
    (q : CriticalPath d.radical (replacementGeometry h d) c v)
    (hsmall : (Q d.radical v).relIndex (Z d.radical c) < 4)
    (hfix : Q d.radical (q.walk.getVert 1) ≤
      centralizer ((⁅Z d.radical c,Z d.radical v⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ⁅Q d.radical (q.walk.getVert 1),Q d.radical (q.walk.getVert 1)⁆ ≤
      centralizer (Z d.radical c : Set (FreeAmalgam d.radical)) := by
  let t := q.walk.getVert 1
  have hl : 0 < q.walk.length := q.length_eq_b ▸ replacementDistance_pos h d
  have hct : Adjacent d.radical c t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using q.walk.adj_getVert_succ (i := 0) hl
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := SylowAdjacent.edge_coordinates (h := h) hc q.start_color hct
  have hAt : Z d.radical v ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical v ((replacementGeometry h d).exists_critical v q.end_color)
    rw [(replacementGeometry h d).distance_constant v q.end_color,SimpleGraph.dist_comm,q.dist_end]
    have hh : q.walk.length = replacementDistance h d := q.length_eq_b
    change q.walk.length - 1 < replacementDistance h d
    omega
  have hAR : Z d.radical v ≤ i.range :=
    hAt.trans ((hiR ▸ map_le_range i d.radical))
  let A := (Z d.radical v).comap i
  have hmA : A.map i = Z d.radical v := map_comap_eq_self hAR
  have hA : A ≤ d.radical := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [hmA,hiR]
  have hnot : ¬ A ≤ pCore 2 d.overgroup := by
    intro hh
    have hh := map_mono (f := i) hh
    rw [hmA,hiQ] at hh
    exact (critical_reverse_pair s hc q).2 hh
  have hidx : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    rw [←SectionFive.centralizer_index_map i hi,hmA,hiU]
    let := finite_Z d.radical c
    let : Finite (U d.radical c) := Finite.of_injective
      (inclusion (DistanceEight.U_le_Z d.radical c)) (inclusion_injective _)
    have hC := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical v q.end_color))
    exact ((relIndex_le_of_le_left hC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical c) index_ne_zero_of_finite)).trans_eq
      (small_critical_indices s hc q hsmall).1
  have hfix' : d.radical ≤ centralizer
      ((⁅replacementMoved d,A⁆ : Subgroup d.overgroup) : Set _) := by
    intro x hx y hy
    apply hi
    simp only [map_mul]
    have hix : i x ∈ Q d.radical t := hiR ▸ mem_map_of_mem i hx
    have hiy := mem_map_of_mem i hy
    rw [map_commutator,hmA,hiU,small_critical_moving_commutator_eq s hc q hsmall] at hiy
    exact hfix hix (i y) hiy
  have hh := map_mono (f := i) (eight_cover_fixed_line_abelian s hne₀ hcard hb A hA hnot hidx hfix')
  rw [map_commutator,hiR,hiQ] at hh
  exact hh.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q d.radical c q.start_color)))

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
