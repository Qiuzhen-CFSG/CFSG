module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.CoreGroup
public import Theory.GroupTheory.NormalSupplementGluing

/-!
# Gluing the original two-residual comparison

The extraspecial core and the perfect cubic centralizer intersect in the
marked central involution. Their constructed isomorphisms agree on that
intersection and intertwine conjugation. Normal-supplement gluing therefore
compares their actual product, with both restriction equations retained.
The existing `planeEven_eq_twoResidual` identifies this product with O²(H).

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.3), p.606.
This is the index-two subgroup of H; extending across its original
involutory splitting remains part of the full plane-group comparison.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry Sporadic.Mathieu PerfectCentralCovering
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))
variable {G' : Type*} [Group G'] [Finite G'] {z' : G'}
variable (h' : IsTypeJ4 z')
variable (e' : CubicAutomorphismQuotient (centralizer z' ⧸ core z'))
variable (X' : Sylow 3 (CubicLift.subgroup e'))
variable [IsExtraspecial 2 (core z)] [IsExtraspecial 2 (core z')]

include h h' in
private theorem core_cover_agree
    (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
    (hφz : φ (cubicMarker e X) = cubicMarker e' X')
    (ψ : core z ≃* core z')
    (c : cubicCentralizerInH e X) (hc : c.val ∈ core z) :
    (ψ ⟨c.val,hc⟩ : centralizer z') = (φ c).val := by
  let q : core z := ⟨c.val,hc⟩
  have hq : q ∈ center (core z) := (core_cubic_centralizer h e X).le c.property
  have hcases : q = 1 ∨ q = coreMarker h := by
    by_cases hq1 : q=1
    · exact Or.inl hq1
    · obtain ⟨w,_,hw⟩ := (Nat.card_eq_two_iff' (1 : center (core z))).mp
        (IsExtraspecial.center_order_p 2 (core z))
      exact Or.inr (congrArg Subtype.val ((hw ⟨q,hq⟩ (fun he => hq1 (congrArg Subtype.val he))).trans
        (hw ⟨_,coreMarker_central h⟩ (fun he => coreMarker_ne_one h (congrArg Subtype.val he))).symm))
  rcases hcases with he | he
  · have hc1 : c=1 := Subtype.ext (congrArg (fun q : core z => (q : centralizer z)) he)
    change (ψ q : centralizer z') = _
    rw [he,hc1,map_one,map_one]
    rfl
  · have hcz : c = cubicMarker e X := Subtype.ext (congrArg (fun q : core z => (q : centralizer z)) he)
    change (ψ q : centralizer z') = _
    rw [he,coreEquiv_marker h h' ψ,hcz,hφz]
    rfl

/-- Glue specified compatible core and six-cover maps on their actual product. -/
theorem exists_planeEven_equiv_of_compatible
    (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X')
    (hφ : ∀ c, cubicNativeProjection h' e' X' (φ c) = cubicNativeProjection h e X c)
    (hφz : φ (cubicMarker e X) = cubicMarker e' X')
    (ψ : core z ≃* core z')
    (hψ : ∀ c : cubicCentralizerInH e X, ∀ q : core z,
      ψ (MulAut.conjNormal c.val q) = MulAut.conjNormal (φ c).val (ψ q)) :
    ∃ E : planeEven e ≃* planeEven e',
      (∀ q : core z, ∀ hq : q.val ∈ planeEven e, (E ⟨q.val,hq⟩ : centralizer z') = ψ q) ∧
      ∀ c : cubicCentralizerInH e X, ∀ hc : c.val ∈ planeEven e,
        (E ⟨c.val,hc⟩ : centralizer z') = (φ c).val := by
  have hQ : core z ≤ planeEven e := by rw [planeEven_eq_sup h e X]; exact le_sup_left
  have hC : cubicCentralizerInH e X ≤ planeEven e := by rw [planeEven_eq_sup h e X]; exact le_sup_right
  have hQ' : core z' ≤ planeEven e' := by rw [planeEven_eq_sup h' e' X']; exact le_sup_left
  have hC' : cubicCentralizerInH e' X' ≤ planeEven e' := by rw [planeEven_eq_sup h' e' X']; exact le_sup_right
  let Q₀ := (core z).subgroupOf (planeEven e)
  let C₀ := (cubicCentralizerInH e X).subgroupOf (planeEven e)
  let Q₁ := (core z').subgroupOf (planeEven e')
  let C₁ := (cubicCentralizerInH e' X').subgroupOf (planeEven e')
  let q₀ : Q₀ ≃* core z := subgroupOfEquivOfLe hQ
  let c₀ : C₀ ≃* cubicCentralizerInH e X := subgroupOfEquivOfLe hC
  let q₁ : Q₁ ≃* core z' := subgroupOfEquivOfLe hQ'
  let c₁ : C₁ ≃* cubicCentralizerInH e' X' := subgroupOfEquivOfLe hC'
  let φ₀ := c₀.trans (φ.trans c₁.symm)
  let ψ₀ := q₀.trans (ψ.trans q₁.symm)
  let f := C₁.subtype.comp φ₀.toMonoidHom
  have hf : f.range = C₁ := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr φ₀.surjective,←MonoidHom.range_eq_map,range_subtype]
  have hg : Q₀ ⊔ C₀ = ⊤ := by
    rw [←subgroupOf_sup hQ hC,←planeEven_eq_sup h e X,subgroupOf_self]
  have hg' : Q₁ ⊔ f.range = ⊤ := by
    rw [hf,←subgroupOf_sup hQ' hC',←planeEven_eq_sup h' e' X',subgroupOf_self]
  obtain ⟨E,hEq,hEc⟩ := NormalSupplementGluing.exists_equiv Q₀ C₀ Q₁ ψ₀ f hg hg'
    (fun c => by
      change (φ (c₀ c)).val ∈ core z' ↔ (c₀ c).val ∈ core z
      rw [←QuotientGroup.eq_one_iff,←QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' (core z') (φ (c₀ c)).val = 1 ↔
        QuotientGroup.mk' (core z) (c₀ c).val = 1
      rw [cubicNativeComparison_core h e X h' e' X' φ hφ]
      exact (coreQuotientComparison h e X h' e' X').map_eq_one_iff)
    (fun c hc => by
      apply Subtype.ext
      exact core_cover_agree h e X h' e' X' φ hφz ψ (c₀ c) hc)
    (fun c q => by
      apply Subtype.ext
      change (ψ (MulAut.conjNormal (c₀ c).val (q₀ q)) : centralizer z') =
        (φ (c₀ c)).val * (ψ (q₀ q)).val * (φ (c₀ c)).val⁻¹
      have he := congrArg Subtype.val (hψ (c₀ c) (q₀ q))
      simpa only [MulAut.conjNormal_apply] using he)
  refine ⟨E,fun q hq => ?_,fun c hc => ?_⟩
  · exact congrArg Subtype.val (hEq ⟨⟨q.val,hq⟩,q.property⟩)
  · exact congrArg Subtype.val (hEc ⟨⟨c.val,hc⟩,c.property⟩)

variable (hp : Group.IsPerfect (cubicCentralizerInH e X))
variable (hp' : Group.IsPerfect (cubicCentralizerInH e' X'))
include hp hp' in
/-- The marked two-residuals are isomorphic, with both core and cover
restriction equations and the original native quotient marking retained. -/
theorem exists_planeEven_equiv :
    ∃ (φ : cubicCentralizerInH e X ≃* cubicCentralizerInH e' X') (ψ : core z ≃* core z')
      (E : planeEven e ≃* planeEven e'),
      (∀ c, cubicNativeProjection h' e' X' (φ c) = cubicNativeProjection h e X c) ∧
      φ (cubicMarker e X) = cubicMarker e' X' ∧
      (∀ q, Additive.ofMul (QuotientGroup.mk' (center (core z')) (ψ q)) =
        coreSpaceComparison h e X h' e' X'
          (Additive.ofMul (QuotientGroup.mk' (center (core z)) q))) ∧
      ψ (coreMarker h) = coreMarker h' ∧
      (∀ q : core z, ∀ hq : q.val ∈ planeEven e, (E ⟨q.val,hq⟩ : centralizer z') = ψ q) ∧
      ∀ c : cubicCentralizerInH e X, ∀ hc : c.val ∈ planeEven e,
        (E ⟨c.val,hc⟩ : centralizer z') = (φ c).val := by
  obtain ⟨φ,ψ,hφ,hφz,hψq,hψz,hψ⟩ := exists_cubic_coreGroup_equiv h e X h' e' X' hp hp'
  obtain ⟨E,hEq,hEc⟩ := exists_planeEven_equiv_of_compatible h e X h' e' X' φ hφ hφz ψ hψ
  exact ⟨φ,ψ,E,hφ,hφz,hψq,hψz,hEq,hEc⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
