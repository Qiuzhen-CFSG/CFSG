module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.SecondStabilizer
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ReturningIntersections

/-!
# The returning involution class and its exact quotient two-core

A distinct conjugate of the central marker returning to the extraspecial core
has a normal elementary crossing image of order 32 in its literal stabilizer
in H/Q. This excludes the second source orbit, whose two-core has order 16.
The first orbit therefore gives precisely all returning conjugates except the
central marker. Equality of orders also identifies the crossing image with
the intrinsic two-core of that stabilizer, through the original quotient map.

This proves Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), (4.3)(1), p.597, DOI 10.1007/BF01232280, and the two-core
identification used in its proof. The three-space assertion of (4.3)(2) is
not asserted here.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
variable {G : Type*} [Group G] [Finite G] {z : G} (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient ((centralizer z) ⧸ core z))
variable (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e))
variable [IsExtraspecial 2 (core z)]

omit [IsExtraspecial 2 (core z)] in
include h in
private theorem returning_order (r : core z) (hr : IsConj z ((r : centralizer z) : G)) :
    orderOf r = 2 := by
  have he : orderOf ((r : centralizer z) : G) = 2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hr
    rw [← hg]
    exact ((MulAut.conj g).orderOf_eq z).trans h.involution
  exact ((orderOf_injective (core z).subtype Subtype.val_injective r).symm.trans
    (orderOf_injective (centralizer z).subtype Subtype.val_injective (r : centralizer z)).symm).trans he

omit [IsExtraspecial 2 (core z)] in
include h in
private theorem returning_noncentral (r : core z)
    (hr : IsConj z ((r : centralizer z) : G))
    (hne : ((r : centralizer z) : G) ≠ z) : r ∉ center (core z) := by
  intro hc
  have hm : ((r : centralizer z) : G) ∈ zpowers z := by
    rw [← LocalGeometry.core_center_image h]
    exact mem_map_of_mem _ (mem_map_of_mem _ hc)
  have hz1 : z ≠ 1 := by intro he; simpa [he] using h.involution
  have hr1 : ((r : centralizer z) : G) ≠ 1 := by
    intro he
    exact hz1 (isConj_one_left.mp (he ▸ hr))
  obtain ⟨w,_,hw⟩ := (Nat.card_eq_two_iff' (1 : zpowers z)).mp
    ((Nat.card_zpowers z).trans h.involution)
  exact hne (congrArg Subtype.val ((hw ⟨_,hm⟩
    (fun he => hr1 (congrArg Subtype.val he))).trans
      (hw ⟨z,mem_zpowers z⟩ (fun he => hz1 (congrArg Subtype.val he))).symm))

/-- A distinct returning conjugate lies in the first, order-3840 stabilizer orbit.
The normal order-32 crossing image excludes the second elementary order-16 core. -/
theorem returning_label_four (r : core z) (hr : IsConj z ((r : centralizer z) : G))
    (hne : ((r : centralizer z) : G) ≠ z) :
    VectorOrbits.label (coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r))) = 4 := by
  have hrc := returning_noncentral h r hr hne
  obtain ⟨r₁,r₂,_,_,_,_,e₁,e₂,hcov⟩ := source_involution_orbit_cover h e X
  rcases hcov r (returning_order h r hr) hrc with hc | hc
  · have he := core_label_of_isConj h e X r r₁ hc
    rw [e₁,VectorOrbits.label_decode] at he
    exact he
  · have he := core_label_of_isConj h e X r r₂ hc
    rw [e₂,VectorOrbits.label_decode] at he
    have hs := (coreCentralizerImage_structure_seven h e X r hrc he).2.1
    have hb := returning_stabilizer_twoCore_card h r hr hne
    rw [hs] at hb
    omega

include h in
/-- For every returning conjugate the normal crossing image is exactly the
intrinsic two-core of the literal element-centralizer image in H/Q. -/
theorem returningImage_eq_twoCore (r : core z) (hr : IsConj z ((r : centralizer z) : G))
    (hne : ((r : centralizer z) : G) ≠ z) :
    let C := (Subgroup.centralizer ({(r : centralizer z)} : Set (centralizer z))).map
      (QuotientGroup.mk' (core z))
    (returningImage z ((r : centralizer z) : G)).subgroupOf C = pCore 2 C := by
  obtain ⟨e⟩ := h.cubic_quotient
  obtain ⟨X⟩ := (inferInstance : Nonempty (Sylow 3 (LocalGeometry.CubicLift.subgroup e)))
  let I := returningImage z ((r : centralizer z) : G)
  let C := (Subgroup.centralizer ({(r : centralizer z)} : Set (centralizer z))).map
    (QuotientGroup.mk' (core z))
  have hrQ : ((r : centralizer z) : G) ∈ ambientCore z :=
    mem_map_of_mem (centralizer z).subtype r.property
  let := returningImage_normal h r hr
  let := returningImage_elementary h hr hrQ
  have hp : IsPGroup 2 (I.subgroupOf C) :=
    (IsElementaryAbelian.isPGroup 2 I).comap_subtype
  have hle : I.subgroupOf C ≤ pCore 2 C := le_sSup ⟨inferInstance,hp⟩
  apply eq_of_le_of_card_ge hle
  have hs := (coreVectorStabilizer_structure_four h e X r
    (returning_noncentral h r hr hne) (returning_label_four h e X r hr hne)).2.1
  rw [coreVectorStabilizer_eq_centralizer_image h r (returning_noncentral h r hr hne)] at hs
  rw [Nat.card_congr (subgroupOfEquivOfLe (returningImage_le r)).toEquiv,
    (returning_intersection_image_orders h hr hrQ hne).2, hs]

omit [IsExtraspecial 2 (core z)] in
include h in
/-- Source (4.3)(1): the returning fusion in Q is exactly the central marker
and one full H-class. Its representative has the first source stabilizer. -/
theorem source_returning_class :
    ∃ r₁ : core z,
      orderOf r₁ = 2 ∧ r₁ ∉ center (core z) ∧
      IsConj z ((r₁ : centralizer z) : G) ∧
      (let C := (Subgroup.centralizer ({(r₁ : centralizer z)} : Set (centralizer z))).map
        (QuotientGroup.mk' (core z))
       Nat.card C = 3840 ∧ IsElementaryAbelian 2 (pCore 2 C) ∧
         Nat.card (pCore 2 C) = 32 ∧
         Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 5))) ∧
      ∀ r : core z, IsConj z ((r : centralizer z) : G) ↔
        ((r : centralizer z) : G) = z ∨ IsConj (r : centralizer z) (r₁ : centralizer z) := by
  let := h.extraspecial
  obtain ⟨e⟩ := h.cubic_quotient
  obtain ⟨X⟩ := (inferInstance : Nonempty (Sylow 3 (LocalGeometry.CubicLift.subgroup e)))
  obtain ⟨r₁,r₂,h₁,h₂,h₁c,h₂c,e₁,e₂,hcov⟩ := source_involution_orbit_cover h e X
  have hl₁ : VectorOrbits.label (coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r₁))) = 4 := by
    rw [e₁,VectorOrbits.label_decode]
    rfl
  have hconj (r : core z) (hr : IsConj z ((r : centralizer z) : G))
      (hne : ((r : centralizer z) : G) ≠ z) :
      IsConj (r : centralizer z) (r₁ : centralizer z) :=
    core_isConj_of_label h e X r r₁ (returning_noncentral h r hr hne)
      ((returning_label_four h e X r hr hne).trans hl₁.symm)
  obtain ⟨g,r,hr,hne⟩ := h.exists_returning_conjugate
  have hrG : IsConj z ((r : centralizer z) : G) := isConj_iff.mpr ⟨g,hr.symm⟩
  have h₁G : IsConj z ((r₁ : centralizer z) : G) :=
    hrG.trans ((centralizer z).subtype.map_isConj (hconj r hrG hne))
  refine ⟨r₁,h₁,h₁c,h₁G,?_,?_⟩
  · dsimp only
    rw [← coreVectorStabilizer_eq_centralizer_image h r₁ h₁c]
    exact ⟨coreVectorStabilizer_card_four h e X r₁ hl₁,
      coreVectorStabilizer_structure_four h e X r₁ h₁c hl₁⟩
  · intro r
    constructor
    · intro hr
      by_cases he : ((r : centralizer z) : G) = z
      · exact Or.inl he
      · exact Or.inr (hconj r hr he)
    · rintro (he | hr)
      · rw [he]
      · exact h₁G.trans ((centralizer z).subtype.map_isConj hr.symm)

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
