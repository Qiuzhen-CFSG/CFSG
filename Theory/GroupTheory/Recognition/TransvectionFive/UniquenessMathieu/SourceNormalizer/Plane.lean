module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Catalogue
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourcePlaneImage

/-!
# The 21-point Mathieu rectangle normalizer

The checked 64-element orbit census uses only the fusion count of the first
rectangle. Apply it to the oriented Mathieu marking, then identify the full
quotient action using the previously proved marked point stabilizer and tensor
symmetry group. This proves the literal quotient N_G(A₁)/A₁ ≃ GL₃(2) × S₃
and its natural tensor action without imposing a count on the other rectangle.

Source: Aschbacher, *Sporadic Groups* (1994), 40.3 and 40.5(2), pp.217–219.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear UniquenessLinear.PlaneTensor
open UniquenessLinear.PlaneCensus (Code pure rankOneGroup)
variable {G : Type*} [Group G] {z : G} (F : MarkedCentralizer z)

private def fusionCodes : Finset Code := by
  classical
  exact Finset.univ.filter (fun x => IsConj z (element F x))
private theorem mem_fusionCodes (x : Code) :
    x ∈ fusionCodes F ↔ IsConj z (element F x) := by
  classical
  simp [fusionCodes]

private theorem conjugate_fusion {a b : G} (hab : IsConj a b) : IsConj z a ↔ IsConj z b :=
  ⟨fun h => h.trans hab, fun h => h.trans hab.symm⟩

private theorem normalizerAction_mem (n : normalizer (F.plane : Set G)) (x : Code) :
    normalizerAction F n x ∈ fusionCodes F ↔ x ∈ fusionCodes F := by
  rw [mem_fusionCodes, mem_fusionCodes]
  apply (conjugate_fusion (z := z) (show IsConj (element F x)
    (element F (normalizerAction F n x)) from ?_)).symm
  exact isConj_iff.mpr ⟨(n : G), (normalizerAction_element F n x).symm⟩

private theorem fusionCodes_card {n : ℕ} (hcount : (F.fusion F.plane).ncard = n) : (fusionCodes F).card = n := by
  classical
  have he : element F '' (fusionCodes F : Set Code) = F.fusion F.plane := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨element_mem F x, (mem_fusionCodes F x).mp hx⟩
    · rintro ⟨ha, hza⟩
      obtain ⟨x, hx⟩ := (sourceEquiv F).surjective ⟨a, ha⟩
      have hxe : element F x = a := congrArg Subtype.val hx
      refine ⟨x, (mem_fusionCodes F x).mpr (hxe.symm ▸ hza), hxe⟩
  have hc := congrArg Set.ncard he
  rw [Set.ncard_image_of_injective _ (element_injective F), Set.ncard_coe_finset] at hc
  exact hc.trans hcount

private theorem fusionCodes_pairCount [Finite G] (a : Code) (ha : a ∈ fusionCodes F) :
    PlaneCensus.pairCount (fusionCodes F) a = PlaneCensus.pairCount (fusionCodes F) 4 := by
  classical
  obtain ⟨n, hn, hna⟩ := source_plane_fusion F (point_mem_plane F) (element_mem F a)
    ((mem_fusionCodes F a).mp ha)
  let f := normalizerAction F ⟨n, hn⟩
  have hf : f 4 = a := by
    apply element_injective F
    rw [normalizerAction_element, element_point]
    exact hna
  symm
  unfold PlaneCensus.pairCount
  apply Finset.card_bijective f f.bijective
  intro b
  simp only [Finset.mem_filter]
  rw [← hf, ← normalizerAction_xor F ⟨n, hn⟩,
    normalizerAction_mem, normalizerAction_mem]

/-- Transfer a checked additive orbit census to the actual marked plane fusion
set. The point stabilizer supplies invariance, and ambient normalizer fusion
supplies the constant pair counts. -/
theorem plane_fusion_census [Finite G] {n : ℕ}
    (hcount : (F.fusion F.plane).ncard = n) (test : Code → Bool)
    (hcensus : ∀ s : Finset Code, (0 : Code) ∉ s → (4 : Code) ∈ s → s.card = n →
      (∀ (k : Fin 5) (x : Code), PlaneCensus.shear k x ∈ s ↔ x ∈ s) →
      (∀ a ∈ s, PlaneCensus.pairCount s a = PlaneCensus.pairCount s 4) →
      ∀ x : Code, x ∈ s ↔ test x = true) (x : Code) :
    IsConj z (element F x) ↔ test x = true := by
  classical
  rw [← mem_fusionCodes]
  apply hcensus (fusionCodes F) ?_ ?_ (fusionCodes_card F hcount) ?_
    (fusionCodes_pairCount F) x
  · intro h
    have he := (mem_fusionCodes F 0).mp h
    rw [element_zero, isConj_one_left] at he
    have ho := F.point_orderOf
    simp [he] at ho
  · rw [mem_fusionCodes, element_point]
  · intro k a
    rw [mem_fusionCodes, mem_fusionCodes]
    obtain ⟨n, _, hn⟩ := exists_shear_conjugator F k a
    exact (conjugate_fusion (z := z) (isConj_iff.mpr ⟨n, hn⟩)).symm


/-- In the 21-element branch the actual fusion set, under its marked matrix
coordinates, is precisely the nonzero rank-one locus. -/
theorem plane_fusion_iff_pure [Finite G] (hcount : (F.fusion F.plane).ncard = 21) (x : Code) :
    IsConj z (element F x) ↔ PlaneCensus.pure x = true :=
  plane_fusion_census F hcount PlaneCensus.pure PlaneCensus.eq_pure_of_twenty_one x


variable [Finite G]

private theorem normalizer_rankOne (hcount : (F.fusion F.plane).ncard = 21) (n : sourcePlaneNormalizer F) :
    normalizerAction F n ∈ rankOneGroup := by
  apply (PlaneCensus.mem_rankOneGroup _).mpr
  refine ⟨normalizerAction_xor F n, fun x => ?_⟩
  have he : (pure (normalizerAction F n x) = true) ↔ pure x = true := by
    rw [← plane_fusion_iff_pure F hcount, ← plane_fusion_iff_pure F hcount, normalizerAction_element]
    have hc : IsConj (element F x) ((n : G) * element F x * (n : G)⁻¹) :=
      isConj_iff.mpr ⟨n, rfl⟩
    exact ⟨fun h => h.trans hc.symm, fun h => h.trans hc⟩
  cases hp : pure (normalizerAction F n x) <;> cases hq : pure x <;> simp_all

private theorem quotientCodeAction_rankOne (hcount : (F.fusion F.plane).ncard = 21) (q : planeQuotient F) :
    quotientCodeAction F q ∈ rankOneGroup := by
  induction q using QuotientGroup.induction_on with
  | H n => rw [quotientCodeAction_mk]; exact normalizer_rankOne F hcount n

/-- The full rank-one preserving additive group is realized by the source
normalizer: fusion gives the point orbit, and the marked centralizer supplies
its entire stabilizer. -/
theorem planeCodeAction_range (hcount : (F.fusion F.plane).ncard = 21) :
    (quotientCodeAction F).range = rankOneGroup := by
  apply le_antisymm
  · rintro _ ⟨q, rfl⟩
    exact quotientCodeAction_rankOne F hcount q
  · intro f hf
    have hp : pure (f 4) = true := by
      rw [(PlaneCensus.mem_rankOneGroup f).mp hf |>.2]
      decide
    obtain ⟨n, hn, hne⟩ := source_plane_fusion F (point_mem_plane F) (element_mem F (f 4))
      ((plane_fusion_iff_pure F hcount (f 4)).mpr hp)
    let q : planeQuotient F := QuotientGroup.mk (⟨n, hn⟩ : sourcePlaneNormalizer F)
    let b := quotientCodeAction F q
    have hb : b 4 = f 4 := by
      apply element_injective F
      change element F (quotientCodeAction F q 4) = _
      rw [quotientCodeAction_mk, normalizerAction_element, element_point]
      exact hne
    have hd : b⁻¹ * f ∈ rankOneGroup := rankOneGroup.mul_mem
      (rankOneGroup.inv_mem (quotientCodeAction_rankOne F hcount q)) hf
    have hd4 : (b⁻¹ * f) 4 = 4 := by
      change b.symm (f 4) = 4
      rw [← hb, b.symm_apply_apply]
    obtain ⟨c, hc⟩ := exists_point_code_action F (b⁻¹ * f) hd hd4
    have hcR : b⁻¹ * f ∈ (quotientCodeAction F).range := by
      refine ⟨QuotientGroup.mk (⟨c, c.property.2⟩ : sourcePlaneNormalizer F), ?_⟩
      rw [quotientCodeAction_mk, ← pointCodeAction_apply, hc]
    have h := (quotientCodeAction F).range.mul_mem (show b ∈ (quotientCodeAction F).range from ⟨q, rfl⟩) hcR
    simpa only [mul_inv_cancel_left] using h

/-- The actual quotient N_G(A₁)/A₁, with its full natural rank-one geometry. -/
def planeQuotientRankOneEquiv (hcount : (F.fusion F.plane).ncard = 21) : planeQuotient F ≃* rankOneGroup :=
  MulEquiv.ofBijective
    ((quotientCodeAction F).codRestrict rankOneGroup (quotientCodeAction_rankOne F hcount))
    ⟨fun _ _ h => quotientCodeAction_injective F (congrArg Subtype.val h), by
      intro f
      have hf : f.val ∈ (quotientCodeAction F).range := (planeCodeAction_range F hcount).symm ▸ f.property
      obtain ⟨q, hq⟩ := hf
      exact ⟨q, Subtype.ext hq⟩⟩

/-- The isomorphism retains the literal quotient map and original conjugation. -/
theorem planeQuotientRankOneEquiv_action (hcount : (F.fusion F.plane).ncard = 21)
    (n : sourcePlaneNormalizer F) (x : Code) :
    element F ((planeQuotientRankOneEquiv F hcount (QuotientGroup.mk n)).val x) =
      (n : G) * element F x * (n : G)⁻¹ := by
  change element F (quotientCodeAction F (QuotientGroup.mk n) x) = _
  rw [quotientCodeAction_mk, normalizerAction_element]


/-- The actual 21-point rectangle quotient, with its original denominator. -/
def planeQuotientEquiv (hcount : (F.fusion F.plane).ncard = 21) : planeQuotient F ≃*
    (((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) × Equiv.Perm (Fin 3)) :=
  (planeQuotientRankOneEquiv F hcount).trans PlaneCensus.rankOneGroupEquivLinearSymmetric

/-- The quotient identification is the natural tensor action of ambient conjugation. -/
theorem planeQuotientEquiv_action (hcount : (F.fusion F.plane).ncard = 21)
    (n : planeNormalizer F) (i : Fin 3) (v : Fin 3 → ZMod 2) :
    element F (PlaneCensus.tensorCode
      ((planeQuotientEquiv F hcount (QuotientGroup.mk n)).2 i)
      ((planeQuotientEquiv F hcount (QuotientGroup.mk n)).1 v)) =
    (n : G) * element F (PlaneCensus.tensorCode i v) * (n : G)⁻¹ := by
  rw [← planeQuotientRankOneEquiv_action F hcount n]
  congr 1
  exact (PlaneCensus.rankOneGroupEquivLinearSymmetric_action
    (planeQuotientRankOneEquiv F hcount (QuotientGroup.mk n)) i v).symm

/-- The orientation's 21-point count discharges the first rectangle field of
source 40.5(2), independently of the 45-point classification. -/
theorem oriented_plane_quotient (hcounts : MathieuFusionOrientation F) :
    Nonempty (planeQuotient F ≃*
      (((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) × Equiv.Perm (Fin 3))) :=
  ⟨planeQuotientEquiv F hcounts.1⟩

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
