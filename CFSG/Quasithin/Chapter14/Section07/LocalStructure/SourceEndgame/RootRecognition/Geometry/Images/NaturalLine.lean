module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Images.Sylow
public import Theory.SpecificGroups.SL2.LineRootGeometry
public import Theory.Representation.SL2FourNaturalOrbits.PlaneOrbits
/-!
# The original V/V₁ field line and its literal stabilizer

The coordinate image of V has order four, by its literal kernel V₁.
If the original S-image is Sylow and V = Z(S), that image is the Sylow
fixed plane. The checked natural-module calculation makes it an F₄-line.
Preservation of this line is equivalent to normalization of the original V,
because the coordinate kernel lies in V. The displacement-and-axis definition
of the projective root group agrees with the literal pointwise line fixer:
determinant preservation puts every displacement in the fixed line.

All coordinates are those of `natural_U_section d`, using the unchanged qK.
The parent Images module consumes these facts for generation and normalizer
lifting. It retains the original k and never replaces O₂(K) by O₂(H).

Source: Aschbacher–Smith, 14.7.73, printed p.1076, manuscript of 1 March 2004.
-/

public section
open Subgroup Representation
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Images
open Chapter12.Section08 CriticalFusion.Source
open ChapterG.Section02.RankOneHigherFields.QuotientAction.Projective

/-- In the natural plane the literal root definition equals the pointwise fixer. -/
theorem root_eq_fixer (P : Point SL2FourNatural.F) :
    rootGroup SL2FourNatural.F P.val =
      fixingSubgroup SL2FourNatural.SL (P.val : Set SL2FourNatural.V) := by
  open SL2FourNatural SL2FourNatural.PlaneGeometry in
  ext g
  rw [mem_fixingSubgroup_iff]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨v, hv, hv0⟩ := P.val.ne_bot_iff.mp
      (Submodule.isAtom_iff_finrank_eq_one.mpr P.property).ne_bot
    have hP := eq_span_singleton_of_mem_of_finrank_eq_one P.property hv hv0
    intro w
    rw [hP, ← wedge_zero_iff v _ hv0]
    have hg : action g v = v := h v hv
    have he := wedge_action g v w
    rw [hg] at he
    change wedge v (action g w - w) = 0
    calc
      _ = wedge v (action g w) - wedge v w := by
        simp only [wedge, Pi.sub_apply]; ring
      _ = 0 := sub_eq_zero.mpr he

universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  (hp : d.U₀ = F.Vi 1) (hUK : F.U ≤ K F)

/-- The natural coordinates always mean those already attached to d. -/
noncomputable abbrev naturalSection := natural_U_section d hp hUK

/-- Kernel saturation recovers the actual V from its original coordinates. -/
theorem coordinates_mem_seed_iff (v : F.U) :
    ((naturalSection d hp hUK).coordinates v).toAdd ∈
      (naturalSection d hp hUK).imageSpace V ↔ (v : G) ∈ V := by
  let c := naturalSection d hp hUK
  constructor
  · intro hv
    obtain ⟨w, hw, he⟩ := (c.mem_imageSpace_iff V _).mp hv
    have hk : (v / w : F.U).val ∈ F.Vi 1 := by
      apply (c.coordinates_eq_one_iff _).mp
      rw [map_div, Multiplicative.toAdd.injective he]
      exact div_self' _
    simpa using V.mul_mem (F.le_seed 1 hk) hw
  · intro hv
    exact (c.mem_imageSpace_iff V _).mpr ⟨v, hv, rfl⟩

/-- The original V/V₁ image has four elements. -/
theorem seed_image_card : Nat.card ((naturalSection d hp hUK).imageSpace V) = 4 := by
  let c := naturalSection d hp hUK
  let f := c.coordinates.comp (inclusion (Data.V_le_U F))
  have hk : f.ker = (F.Vi 1).subgroupOf V := by
    ext v
    exact c.coordinates_eq_one_iff ⟨v, Data.V_le_U F v.property⟩
  have hr : f.range = (V.subgroupOf F.U).map c.coordinates := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨⟨x, Data.V_le_U F x.property⟩, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hker : Nat.card f.ker = 2 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 1)).toEquiv]
    simpa using F.card 1 (by decide)
  have hV : Nat.card V = 8 := by simpa [F.last] using F.card 3 (by decide)
  have hh := f.ker.card_mul_index
  rw [index_ker, hker, hV, hr] at hh
  change Nat.card ((V.subgroupOf F.U).map c.coordinates) = 4
  omega

/-- The actual central V/V₁ is the fixed field line of the original Sylow image. -/
theorem exists_seed_line
    (hcenter : (center (S L F)).map (S L F).subtype = V)
    (R : Sylow 2 SL2FourNatural.SL)
    (hR : ((S L F).subgroupOf (K F)).map (qK d) = (R : Subgroup _)) :
    ∃ P : Point SL2FourNatural.F,
      P.val.restrictScalars (ZMod 2) = (naturalSection d hp hUK).imageSpace V ∧
      (R : Subgroup _) = rootGroup SL2FourNatural.F P.val := by
  let c := naturalSection d hp hUK
  have hc : ⁅S L F, V⁆ ≤ F.Vi 1 := by
    have hz : V ≤ centralizer (S L F : Set G) := by
      intro v hv
      obtain ⟨z, hz, rfl⟩ := hcenter.ge hv
      intro s hs
      exact congrArg Subtype.val (mem_center_iff.mp hz ⟨s, hs⟩)
    rw [commutator_comm, commutator_eq_bot_iff_le_centralizer.mpr hz]
    exact bot_le
  obtain ⟨A, hA, hf⟩ := SL2FourNatural.PlaneGeometry.sylow_fixed_isFieldLine R
  have hle : c.imageSpace V ≤ A.val := by
    intro v hv
    apply (hf v).mpr
    intro a ha
    rw [← hR] at ha
    obtain ⟨s, hs, rfl⟩ := ha
    exact c.fixed_on_imageSpace_of_commutator_le (S L F) V hc s hs v hv
  have he : c.imageSpace V = A.val :=
    SL2FourNatural.PlaneGeometry.submodule_eq_of_card _ _ hle
      ((seed_image_card d hp hUK).trans A.property.symm)
  obtain ⟨P, hP, hPA⟩ := hA
  refine ⟨⟨P, hP⟩, hPA.trans he.symm, ?_⟩
  have hfix : (R : Subgroup _) ≤ fixingSubgroup SL2FourNatural.SL
      (P : Set SL2FourNatural.V) := by
    intro a ha
    rw [mem_fixingSubgroup_iff]
    intro v hv
    exact (hf v).mp (hPA ▸ hv) a ha
  obtain ⟨R', hR'⟩ := Matrix.SpecialLinearGroup.exists_sylow_fixing_line P hP
  rw [root_eq_fixer ⟨P, hP⟩]
  exact (R.is_maximal' (hR' ▸ R'.isPGroup') hfix).symm

/-- Setwise preservation of the original coordinate line lifts to the literal V. -/
theorem stabilizer_preimage (P : Point SL2FourNatural.F)
    (hP : P.val.restrictScalars (ZMod 2) = (naturalSection d hp hUK).imageSpace V)
    (l : K F) :
    qK d l ∈ MulAction.stabilizer SL2FourNatural.SL (P.val : Set SL2FourNatural.V) ↔
      (l : G) ∈ normalizer (V : Set G) := by
  let c := naturalSection d hp hUK
  have hm (v : SL2FourNatural.V) : v ∈ P.val ↔ v ∈ c.imageSpace V := by
    change v ∈ P.val.restrictScalars (ZMod 2) ↔ _
    rw [hP]
  rw [MulAction.mem_stabilizer_set' (Set.toFinite _)]
  constructor
  · intro h
    have hle : V.conjBy (l : G) ≤ V := by
      rintro v ⟨w, hw, rfl⟩
      let wU : F.U := ⟨w, Data.V_le_U F hw⟩
      let vU : F.U := ⟨l * w * (l : G)⁻¹,
        (mem_normalizer_iff.mp (c.normalized l.property) w).mp wU.property⟩
      apply (coordinates_mem_seed_iff d hp hUK vU).mp
      rw [show (c.coordinates vU).toAdd = _ from c.equivariant l wU]
      exact (hm _).mp (h ((hm _).mpr
        ((c.mem_imageSpace_iff V _).mpr ⟨wU, hw, rfl⟩)))
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact eq_of_le_of_card_ge hle (card_map_of_injective (MulAut.conj (l : G)).injective).ge
  · intro h v hv
    obtain ⟨w, hw, he⟩ := (c.mem_imageSpace_iff V v).mp ((hm v).mp hv)
    apply (hm _).mpr
    refine (c.mem_imageSpace_iff V _).mpr ⟨⟨l * w * (l : G)⁻¹,
      (mem_normalizer_iff.mp (c.normalized l.property) w).mp w.property⟩,
      (mem_normalizer_iff.mp h w).mp hw, ?_⟩
    exact (c.equivariant l w).trans (congrArg _ he)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Geometry.Images
