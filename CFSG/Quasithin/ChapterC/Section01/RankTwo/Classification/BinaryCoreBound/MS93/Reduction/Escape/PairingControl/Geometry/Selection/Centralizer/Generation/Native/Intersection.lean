module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.Native.Incidence
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Six.Complement.FixedComparison.DualFixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.StepThree.Kernel.Geometry

/-!
# Native intersection and fixed-preimage indices

Every neighboring radius group has a two-element image in V_c/B_c: its
image is fixed by its incident kernel, hence lies in the dual annihilator
of the natural edge plane. Neighbor transitivity excludes a zero image.
The radius decomposition and the orders |Vcirc_c| = 64 and |U_c| = 8 give

  [Vcirc_c intersect V_s : U_c] * [B_c : B_c intersect V_s] = 2.

Consequently native incidence is equivalent to B_c being contained in one
neighboring radius group, and hence in every one by transitivity. The
containment of this full fixed preimage remains unproved. In particular,
the already available containment of Z_c[V_c,Q_c] in every neighbor does
not by itself discharge it.

The earlier index reduction is retained: the requested native incidence
is equivalent to finding a neighboring radius group of index at most four.
These equivalences do not prove the source generation display.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), immediately before (4.3.2)(4), printed p.884. The display concerns
actual neighboring radius groups; a nonzero image modulo B alone does not
supply a representative in their intersections with Vcirc.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- Every neighboring radius group has exactly a line as its image modulo B.
Fixation by the incident kernel bounds the dual image by the annihilator of
the edge plane. A zero image would make all of V fixed by neighbor transitivity. -/
theorem neighbor_fixed_quotient_index (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    {c s : Vertex R} (hc : color R c = false) (hcs : Adjacent R c s) :
    (B R c (geometry.Z_normal c)).relIndex (V R s) = 2 := by
  obtain ⟨q, hqc⟩ := Initial.Consequences.counterexample_at_start p c hc
  obtain ⟨iq⟩ := initial q
  have sectionAt : NaturalSectionAt c (V R c) (Z R c) := by
    simpa only [hqc] using iq.natural_section
  obtain ⟨o⟩ := facts.opposite c hc
  let dual := Six.Complement.FixedComparison.fullRadiusDual source hb hc sectionAt o
  let A := stabilizer R c
  let W := (V R s).subgroupOf A
  let V₀ := (V R c).subgroupOf A
  let B₀ := (B R c (geometry.Z_normal c)).subgroupOf A
  let T := (Q R s).subgroupOf A
  let U₀ := (U R c).subgroupOf A
  let := finite_stabilizer R c
  let : B₀.Normal := normal_subgroupOf_of_le_normalizer (fixedPreimage_normalized hb c hc)
  have hWV : V R s ≤ V R c := Initial.Consequences.edge_radius_le_radius hc hcs
  have hVA : V R c ≤ A := (geometry.V_le_Q hb c hc).trans (fun _ hx => hx.1)
  have hWA := hWV.trans hVA
  have hBA : B R c (geometry.Z_normal c) ≤ A := map_subtype_le _
  have hTA : Q R s ≤ A := fun _ hx => hx.2 c (adjacent_symm R hcs)
  have hUA : U R c ≤ A := (U_le_Z c).trans (Z_le_stabilizer R c)
  have hBV : B₀.relIndex V₀ = 8 := by
    let n := FirstPairing.Orientation.ImageCases.natural_coordinates_at source hb hc sectionAt
    let := n.kernel_normal
    rw [relIndex, index_eq_card, Nat.card_congr n.quotientEquiv.toEquiv]
    change Nat.card (Fin 3 → ZMod 2) = 8
    simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  have hnot : ¬ W ≤ B₀ := by
    intro h
    have hSB : V R s ≤ B R c (geometry.Z_normal c) := by
      intro x hx
      exact h (show (⟨x, hWA hx⟩ : A) ∈ W from hx)
    have hVB := FirstPairing.Orientation.ImageCases.V_le_of_normalized_neighbor hc hcs
      (B R c (geometry.Z_normal c)) (fixedPreimage_normalized hb c hc) hSB
    have hi : B₀.relIndex V₀ = 1 := relIndex_eq_one.mpr (fun _ hx => hVB hx)
    omega
  have hfixed : ⁅W, T⁆ ≤ B₀ := by
    apply map_le_iff_le_comap.mp
    rw [map_commutator, map_subgroupOf_eq_of_le hWA, map_subgroupOf_eq_of_le hTA]
    exact neighbor_fixed_mod_B source hb facts hc hcs
  have hdisplacement : ⁅U₀, T⁆ = (edgeDisplacement c s).subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hUA, map_subgroupOf_eq_of_le hTA,
      map_subgroupOf_eq_of_le ((Initial.edge_le_natural source c s hc hcs).trans hUA)]
    exact (Initial.edge_eq_natural_commutator source hb modules c s hc hcs).symm
  obtain ⟨y, hyW, hyB⟩ := SetLike.not_le_iff_exists.mp hnot
  have hY : zpowers y ≤ W := zpowers_le.mpr hyW
  have hcover : W ≤ zpowers y ⊔ B₀ := by
    apply Six.Complement.FixedComparison.cover_of_equal_displacements o.naturalU dual
      T T W (zpowers y) (fun _ hx => hWV hx) (hY.trans (fun _ hx => hWV hx))
      hfixed ((commutator_mono hY le_rfl).trans hfixed) rfl
    · rw [hdisplacement, Nat.card_congr (subgroupOfEquivOfLe
        ((Initial.edge_le_natural source c s hc hcs).trans hUA)).toEquiv]
      exact FirstPairing.StepThree.edge_card p (by omega) initial c s hc hcs
    · exact fun h => hyB (h (mem_zpowers y))
  have hy2 : y ^ 2 = 1 := by
    let := FirstPairing.StepThree.Kernel.radius_elementary c hc iq.six_le
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (y : FreeAmalgam R) (hWV hyW))
  have hsmall : B₀.relIndex W ≤ 2 := calc
    B₀.relIndex W ≤ B₀.relIndex (zpowers y ⊔ B₀) :=
      relIndex_le_of_le_right hcover index_ne_zero_of_finite
    _ = B₀.relIndex (zpowers y) := relIndex_sup_right _ _
    _ ≤ Nat.card (zpowers y) := Nat.le_of_dvd Nat.card_pos (relIndex_dvd_card _ _)
    _ = orderOf y := Nat.card_zpowers y
    _ ≤ 2 := orderOf_le_of_pow_eq_one (by decide) hy2
  have hpos : B₀.relIndex W ≠ 0 := index_ne_zero_of_finite
  have hne : B₀.relIndex W ≠ 1 := fun h => hnot (relIndex_eq_one.mp h)
  have htwo : B₀.relIndex W = 2 := by omega
  rw [relIndex_subgroupOf hWA] at htwo
  exact htwo

/-- The exact index product, retaining the literal neighboring subgroup. -/
theorem neighbor_radius_index_mul (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (facts : ContraryLocalFacts geometry)
    (hsix : 6 ≤ geometry.b R) {c s : Vertex R}
    (hc : color R c = false) (hcs : Adjacent R c s) :
    (U R c).relIndex (Vcirc R c ⊓ V R s) * (V R s).relIndex (V R c) = 8 := by
  let C := (Vcirc R c).subgroupOf (V R c)
  let S := (V R s).subgroupOf (V R c)
  let := FirstPairing.StepThree.Kernel.radius_elementary c hc hsix
  have hCV : Vcirc R c ≤ V R c := Vcirc_le_V c
  have hSV : V R s ≤ V R c := Initial.Consequences.edge_radius_le_radius hc hcs
  have hcover : C ⊔ S = ⊤ := by
    apply map_injective (V R c).subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hCV,
      map_subgroupOf_eq_of_le hSV, ← MonoidHom.range_eq_map, range_subtype]
    exact (Initial.Consequences.radius_eq_moving_sup_edge source hc hcs).symm
  have hindex : (V R s).relIndex (V R c) = (V R s).relIndex (Vcirc R c) := by
    rw [← relIndex_subgroupOf (H := V R s) (le_refl (V R c)),
      ← relIndex_subgroupOf (H := V R s) hCV, subgroupOf_self]
    change S.relIndex ⊤ = S.relIndex C
    rw [← hcover, relIndex_sup_right]
  have hUC : U R c ≤ Vcirc R c := commutator_mono (Z_le_VBall R c 2) le_rfl
  have hUS : U R c ≤ V R s := by
    apply (U_le_Z c).trans
    apply le_iSup_of_le c
    exact le_iSup_of_le
      ((SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hcs)).le.trans
        (by decide : 1 ≤ 2)) le_rfl
  have hUCindex : (U R c).relIndex (Vcirc R c) = 8 := by
    have hh := ((U R c).subgroupOf (Vcirc R c)).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hUC).toEquiv,
      modules.natural.card_at c hc, facts.moving_card c hc] at hh
    change (U R c).relIndex (Vcirc R c) * 8 = 64 at hh
    omega
  have hm := relIndex_mul_relIndex (U R c) (Vcirc R c ⊓ V R s) (Vcirc R c)
    (le_inf hUC hUS) inf_le_left
  rwa [inf_relIndex_left, ← hindex, hUCindex] at hm

/-- The native incidence target is precisely a neighboring index bound of four.
This equivalence leaves that bound to be proved from the source geometry. -/
theorem nativeIncidence_iff_neighbor_index_le_four (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (facts : ContraryLocalFacts geometry)
    (hsix : 6 ≤ geometry.b R) {c : Vertex R} (hc : color R c = false) :
    NativeIncidence c ↔
      ∃ s : Vertex R, Adjacent R c s ∧ (V R s).relIndex (V R c) ≤ 4 := by
  constructor
  · rintro ⟨s, hcs, hnot⟩
    refine ⟨s, hcs, ?_⟩
    have hm := neighbor_radius_index_mul source modules facts hsix hc hcs
    have hn : (U R c).relIndex (Vcirc R c ⊓ V R s) ≠ 1 := by
      exact fun h => hnot (relIndex_eq_one.mp h)
    have hp : 0 < (U R c).relIndex (Vcirc R c ⊓ V R s) := by nlinarith
    have hq : 0 < (V R s).relIndex (V R c) := by nlinarith
    have htwo : 2 ≤ (U R c).relIndex (Vcirc R c ⊓ V R s) := by omega
    nlinarith
  · rintro ⟨s, hcs, hlt⟩
    refine ⟨s, hcs, ?_⟩
    intro hle
    have hm := neighbor_radius_index_mul source modules facts hsix hc hcs
    rw [relIndex_eq_one.mpr hle, one_mul] at hm
    omega



/-- The neighbor index is four times the index of its intersection with B
in B. Thus the extra fixed component is exactly the remaining index obstruction. -/
theorem neighbor_radius_index_eq_four_mul_fixed_index (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    {c s : Vertex R} (hc : color R c = false) (hcs : Adjacent R c s) :
    (V R s).relIndex (V R c) =
      4 * (V R s).relIndex (B R c (geometry.Z_normal c)) := by
  obtain ⟨q, hqc⟩ := Initial.Consequences.counterexample_at_start p c hc
  obtain ⟨iq⟩ := initial q
  have sectionAt : NaturalSectionAt c (V R c) (Z R c) := by
    simpa only [hqc] using iq.natural_section
  let A := stabilizer R c
  let Bc := B R c (geometry.Z_normal c)
  have hVA : V R c ≤ A := (geometry.V_le_Q hb c hc).trans (fun _ hx => hx.1)
  have hBV : Bc.relIndex (V R c) = 8 := by
    rw [← relIndex_subgroupOf (H := Bc) hVA]
    let n := FirstPairing.Orientation.ImageCases.natural_coordinates_at source hb hc sectionAt
    let := finite_stabilizer R c
    let := n.kernel_normal
    rw [relIndex, index_eq_card, Nat.card_congr n.quotientEquiv.toEquiv]
    change Nat.card (Fin 3 → ZMod 2) = 8
    simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  have h₁ := relIndex_mul_relIndex (V R s ⊓ Bc) (V R s) (V R c)
    inf_le_left (Initial.Consequences.edge_radius_le_radius hc hcs)
  have h₂ := relIndex_mul_relIndex (V R s ⊓ Bc) Bc (V R c)
    inf_le_right (EdgeTransfer.B_le_radius hb c hc)
  rw [inf_relIndex_left, neighbor_fixed_quotient_index source hb modules initial facts p hc hcs] at h₁
  rw [inf_relIndex_right, hBV] at h₂
  change (V R s).relIndex (V R c) = 4 * (V R s).relIndex Bc
  omega

/-- The two possible obstructions have product two: either the native
intersection is larger than U, or the neighboring subgroup misses half of B. -/
theorem native_intersection_index_mul_fixed_index (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    {c s : Vertex R} (hc : color R c = false) (hcs : Adjacent R c s) :
    (U R c).relIndex (Vcirc R c ⊓ V R s) *
      (V R s).relIndex (B R c (geometry.Z_normal c)) = 2 := by
  obtain ⟨ip⟩ := initial p
  have hm := neighbor_radius_index_mul source modules facts ip.six_le hc hcs
  rw [neighbor_radius_index_eq_four_mul_fixed_index source hb modules initial facts p hc hcs] at hm
  nlinarith [show (U R c).relIndex (Vcirc R c ⊓ V R s) *
      (4 * (V R s).relIndex (B R c (geometry.Z_normal c))) =
      4 * ((U R c).relIndex (Vcirc R c ⊓ V R s) *
        (V R s).relIndex (B R c (geometry.Z_normal c))) by ring]

/-- A nonzero native intersection is equivalent to containment of the full
fixed preimage in that same neighbor. This is a reduction, not a producer
of either equivalent geometric assertion. -/
theorem native_intersection_iff_fixed_le_neighbor (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    {c s : Vertex R} (hc : color R c = false) (hcs : Adjacent R c s) :
    (¬ Vcirc R c ⊓ V R s ≤ U R c) ↔ B R c (geometry.Z_normal c) ≤ V R s := by
  have hm := native_intersection_index_mul_fixed_index source hb modules initial facts p hc hcs
  constructor
  · intro h
    have hn : (U R c).relIndex (Vcirc R c ⊓ V R s) ≠ 1 :=
      fun he => h (relIndex_eq_one.mp he)
    have hp : 0 < (U R c).relIndex (Vcirc R c ⊓ V R s) := by nlinarith
    have hq : 0 < (V R s).relIndex (B R c (geometry.Z_normal c)) := by nlinarith
    apply relIndex_eq_one.mp
    have hn₂ : 2 ≤ (U R c).relIndex (Vcirc R c ⊓ V R s) := by omega
    nlinarith
  · intro hfix hle
    rw [relIndex_eq_one.mpr hfix, relIndex_eq_one.mpr hle] at hm
    norm_num at hm

/-- The existential native-incidence target retains precisely the
obligation to put B inside one actual neighboring radius group. -/
theorem nativeIncidence_iff_fixed_le_neighbor (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    {c : Vertex R} (hc : color R c = false) :
    NativeIncidence c ↔ ∃ s : Vertex R, Adjacent R c s ∧
      B R c (geometry.Z_normal c) ≤ V R s := by
  constructor
  · rintro ⟨s, hcs, hs⟩
    exact ⟨s, hcs, (native_intersection_iff_fixed_le_neighbor source hb modules initial facts p hc hcs).mp hs⟩
  · rintro ⟨s, hcs, hs⟩
    exact ⟨s, hcs, (native_intersection_iff_fixed_le_neighbor source hb modules initial facts p hc hcs).mpr hs⟩

/-- Transitivity makes the remaining fixed-preimage obligation uniform
over every neighbor. No fixed-preimage containment is asserted here. -/
theorem nativeIncidence_iff_fixed_le_every_neighbor (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    {c : Vertex R} (hc : color R c = false) :
    NativeIncidence c ↔ ∀ s : Vertex R, Adjacent R c s →
      B R c (geometry.Z_normal c) ≤ V R s := by
  rw [nativeIncidence_iff_fixed_le_neighbor source hb modules initial facts p hc]
  constructor
  · rintro ⟨s, hcs, hs⟩ t hct
    obtain ⟨g, hg, hgt⟩ := stabilizer_transitive_neighbors R c hcs hct
    have hm := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hs
    rw [← FirstPairing.B_act hb g c hc, ← V_act, show act R g c = c from hg, hgt] at hm
    exact hm
  · intro h
    obtain ⟨g, hg⟩ := exists_mVertex_of_color R hc
    have hadj : Adjacent R c (hVertex R g) := by
      rw [hg]
      exact (adjacent_iff_exists_common R _ _).mpr ⟨g, Or.inl ⟨rfl, rfl⟩⟩
    exact ⟨hVertex R g, hadj, h _ hadj⟩
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
