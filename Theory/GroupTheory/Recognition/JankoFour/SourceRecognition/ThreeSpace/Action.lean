module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.Generated

/-!
# Cubic invariance of the original three-space

The preimage in the extraspecial core of the native binary two-space is
exactly the triple-core intersection constructed in `ThreeSpace.Generated`.
Its containment of the core center makes it normal in the core; the original
cubic scalar preserves its two-dimensional image, hence normalizes the
ambient three-space. The scalar is proved to generate the chosen cubic
Sylow, so the invariance concerns the full original cubic subgroup.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (4.3)(2) and the setup for (4.4), p.597,
DOI 10.1007/BF01232280.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Janko4.InvolutionCentralizers.First.QuotientExtension
open M22TripleCover.Ambient
open scoped commutatorElement
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open VectorOrbits
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e))
variable [IsExtraspecial 2 (core z)]

noncomputable def scalarPlane : Subgroup (core z) where
  carrier := {q : core z | coreNativeEquiv h e X
    (Additive.ofMul (QuotientGroup.mk' (center (core z)) q)) ∈ ThreeSpace.Native.line}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    change coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) a) +
       Additive.ofMul (QuotientGroup.mk' (center (core z)) b)) ∈ ThreeSpace.Native.line
    rw [map_add]
    exact ThreeSpace.Native.line.add_mem ha hb
  inv_mem' {a} ha := by
    change coreNativeEquiv h e X
      (-Additive.ofMul (QuotientGroup.mk' (center (core z)) a)) ∈ ThreeSpace.Native.line
    rw [map_neg]
    exact ThreeSpace.Native.line.neg_mem ha

theorem center_le_scalarPlane : center (core z) ≤ scalarPlane h e X := by
  intro q hq
  change coreNativeEquiv h e X (Additive.ofMul (QuotientGroup.mk' (center (core z)) q)) ∈
    ThreeSpace.Native.line
  have he : QuotientGroup.mk' (center (core z)) q = 1 := (QuotientGroup.eq_one_iff q).mpr hq
  rw [he]
  change coreNativeEquiv h e X 0 ∈ ThreeSpace.Native.line
  rw [map_zero]
  exact ThreeSpace.Native.line.zero_mem

theorem scalarPlane_eq_intersection (r : core z)
    (hr : IsConj z ((r : centralizer z) : G)) (hne : ((r : centralizer z) : G) ≠ z)
    (hmark : coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) = VectorOrbits.decode 4)
    (a : centralizer z)
    (ha : coreAmbientHom h e X (QuotientGroup.mk' (core z) a) = scalarElement) :
    scalarPlane h e X = coreIntersection z ((r : centralizer z) : G) ⊓
      coreIntersection z ((a : G)⁻¹ * ((r : centralizer z) : G) * (a : G)) := by
  have hs : IsConj z ((a : G)⁻¹ * ((r : centralizer z) : G) * (a : G)) :=
    hr.trans (isConj_iff.mpr ⟨(a : G)⁻¹, by simp⟩)
  have hsQ : (a : G)⁻¹ * ((r : centralizer z) : G) * (a : G) ∈ ambientCore z := by
    simpa [ambientCore] using (mem_map_of_mem (centralizer z).subtype (MulAut.conjNormal a⁻¹ r).property)
  have hz := le_inf (center_le_coreIntersection h hr (mem_map_of_mem _ r.property))
    (center_le_coreIntersection h hs hsQ)
  ext q
  change coreNativeEquiv h e X
    (Additive.ofMul (QuotientGroup.mk' (center (core z)) q)) ∈ ThreeSpace.Native.line ↔ _
  rw [← triple_nativeImage h e X r hr hne hmark a ha,
    nativeImage_mem_iff h e X _ hz]

theorem scalarPlane_normal : (scalarPlane h e X).Normal := by
  apply Subgroup.Normal.of_commutator_le
  rw [IsExtraspecial.commutator_eq_center (p := 2)]
  exact center_le_scalarPlane h e X

theorem scalarPlane_stable (a : centralizer z)
    (ha : coreAmbientHom h e X (QuotientGroup.mk' (core z) a) = scalarElement)
    (q : core z) (hq : q ∈ scalarPlane h e X) :
    MulAut.conjNormal a q ∈ scalarPlane h e X := by
  have he := coreAmbientHom_intertwines h e X (QuotientGroup.mk' (core z) a)
    (Additive.ofMul (QuotientGroup.mk' (center (core z)) q))
  rw [coreBinaryRepresentation_apply,toMul_ofMul,coreQuotientAction_mk,ha] at he
  change coreNativeEquiv h e X
    (Additive.ofMul (QuotientGroup.mk' (center (core z)) (MulAut.conjNormal a q))) ∈ ThreeSpace.Native.line
  rw [he]
  exact ThreeSpace.Native.scalar_line _ hq

noncomputable def ambientScalarPlane : Subgroup G := (scalarPlane h e X).map (coreInclusion z)

theorem scalarPlane_cubic_normalizes (a : centralizer z)
    (ha : coreAmbientHom h e X (QuotientGroup.mk' (core z) a) = scalarElement) :
    (a : G) ∈ normalizer (ambientScalarPlane h e X : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,⟨q,hq,rfl⟩,rfl⟩
    exact ⟨MulAut.conjNormal a q,scalarPlane_stable h e X a ha q hq,rfl⟩
  · rw [card_map_of_injective (MulAut.conj (a : G)).injective]

theorem scalarPlane_core_normalizes :
    ambientCore z ≤ normalizer (ambientScalarPlane h e X : Set G) := by
  let := scalarPlane_normal h e X
  rintro _ ⟨q,hq,rfl⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,⟨v,hv,rfl⟩,rfl⟩
    refine ⟨(⟨q,hq⟩ : core z) * v * (⟨q,hq⟩ : core z)⁻¹,?_,rfl⟩
    exact (inferInstance : (scalarPlane h e X).Normal).conj_mem v hv _
  · rw [card_map_of_injective (MulAut.conj (q : G)).injective]

/-- The actual scalar lift generates the original cubic Sylow image. -/
theorem cubicSylowImage_eq_zpowers (a : centralizer z)
    (haX : a ∈ cubicSylowImage e X)
    (ha : coreAmbientHom h e X (QuotientGroup.mk' (core z) a) = scalarElement) :
    cubicSylowImage e X = zpowers a := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hc : Nat.card (cubicSylowImage e X) = 3 := by
    rw [cubicSylowImage,card_map_of_injective (LocalGeometry.CubicLift.subgroup e).subtype_injective]
    exact cubicSylow_card e h X
  have ha1 : a ≠ 1 := by
    intro he
    rw [he,map_one,map_one] at ha
    have ho := congrArg orderOf ha
    rw [orderOf_one,scalarElement_order] at ho
    omega
  have he := zpowers_eq_top_of_prime_card hc
    (show (⟨a,haX⟩ : cubicSylowImage e X) ≠ 1 from fun he => ha1 (congrArg Subtype.val he))
  have hm := congrArg (Subgroup.map (cubicSylowImage e X).subtype) he
  simpa only [MonoidHom.map_zpowers, Subgroup.subtype_apply, ← MonoidHom.range_eq_map, range_subtype] using hm.symm

/-- The entire original cubic Sylow, not only its chosen lift, normalizes Z. -/
theorem scalarPlane_cubicSylow_normalizes (a : centralizer z)
    (haX : a ∈ cubicSylowImage e X)
    (ha : coreAmbientHom h e X (QuotientGroup.mk' (core z) a) = scalarElement) :
    (cubicSylowImage e X).map (centralizer z).subtype ≤
      normalizer (ambientScalarPlane h e X : Set G) := by
  rw [cubicSylowImage_eq_zpowers h e X a haX ha,MonoidHom.map_zpowers]
  exact zpowers_le.mpr (scalarPlane_cubic_normalizes h e X a ha)

/-- The invariant preimage is the same literal ambient triple intersection. -/
theorem ambientScalarPlane_eq_triple (r : core z)
    (hr : IsConj z ((r : centralizer z) : G)) (hne : ((r : centralizer z) : G) ≠ z)
    (hmark : coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) = VectorOrbits.decode 4)
    (a : centralizer z)
    (ha : coreAmbientHom h e X (QuotientGroup.mk' (core z) a) = scalarElement) :
    ambientScalarPlane h e X = ambientCore z ⊓ ambientCore ((r : centralizer z) : G) ⊓
      ambientCore ((a : G)⁻¹ * ((r : centralizer z) : G) * (a : G)) := by
  rw [ambientScalarPlane,scalarPlane_eq_intersection h e X r hr hne hmark a ha,
    Subgroup.map_inf _ _ _ (Subtype.val_injective.comp Subtype.val_injective),
    coreIntersection_map,coreIntersection_map]
  ext g
  simp only [returningIntersection,Subgroup.mem_inf]
  tauto

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
