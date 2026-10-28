module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.Linear
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ReturningClass

/-!
# The original triple-core intersection

A returning core meets the original extraspecial core in an elementary
subgroup of order 128. Its image modulo the original center is singular and
invariant under the actual vector stabilizer. The native displacement
identities identify it with the unique six-space. Lifting the actual scalar
from the original cubic Sylow makes the second intersection transverse; its
image is a binary two-space, so the ambient triple intersection has order eight.
All quotient maps, conjugations and cubic lifts are the original ones.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (4.3)(2), p.597, DOI 10.1007/BF01232280.
This module proves the intersection and order calculation; the generated
three-space is identified in `ThreeSpace.Generated`.
-/

@[expose] public section
open Subgroup Sporadic.Mathieu
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Inclusion of the original extraspecial core in the ambient group. -/
def coreInclusion (z : G) : core z →* G := (centralizer z).subtype.comp (core z).subtype

/-- The returning intersection, retained as a subgroup of the first core. -/
def coreIntersection (z r : G) : Subgroup (core z) :=
  (ambientCore r).comap (coreInclusion z)

omit [Finite G] in
theorem coreIntersection_map (z r : G) :
    (coreIntersection z r).map (coreInclusion z) = returningIntersection z r := by
  ext g
  constructor
  · rintro ⟨q,hq,rfl⟩
    exact ⟨mem_map_of_mem (centralizer z).subtype q.property,hq⟩
  · rintro ⟨⟨a,ha,he⟩,hr⟩
    refine ⟨⟨a,ha⟩,?_,he⟩
    change (a : G) ∈ ambientCore r
    change (a : G) = g at he
    exact he.symm ▸ hr

noncomputable def coreIntersectionEquiv (z r : G) :
    coreIntersection z r ≃* returningIntersection z r :=
  ((coreIntersection z r).equivMapOfInjective (coreInclusion z)
    (Subtype.val_injective.comp Subtype.val_injective)).trans
      (MulEquiv.subgroupCongr (coreIntersection_map z r))

theorem center_le_coreIntersection (h : IsTypeJ4 z) {r : G}
    (hr : IsConj z r) (hrQ : r ∈ ambientCore z) : center (core z) ≤ coreIntersection z r := by
  intro q hq
  have hm : ((q : centralizer z) : G) ∈ zpowers z := by
    rw [← LocalGeometry.core_center_image h]
    exact mem_map_of_mem _ (mem_map_of_mem _ hq)
  exact (zpowers_le.mpr (returning_core_reciprocity h hr hrQ)) hm

theorem coreIntersection_card (h : IsTypeJ4 z) {r : G}
    (hr : IsConj z r) (hrQ : r ∈ ambientCore z) (hne : r ≠ z) :
    Nat.card (coreIntersection z r) = 128 :=
  (Nat.card_congr (coreIntersectionEquiv z r).toEquiv).trans
    (returning_intersection_image_orders h hr hrQ hne).1

theorem coreIntersection_elementary (h : IsTypeJ4 z) {r : G}
    (hr : IsConj z r) (hne : r ≠ z) : IsElementaryAbelian 2 (coreIntersection z r) := by
  let := returningIntersection_elementary h hr hne
  exact IsElementaryAbelian.of_injective (coreIntersectionEquiv z r).toMonoidHom
    (coreIntersectionEquiv z r).injective

variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (LocalGeometry.CubicLift.subgroup e))
variable [IsExtraspecial 2 (core z)]

noncomputable def nativeImage (A : Subgroup (core z)) :
    Submodule (ZMod 2) M22TripleCover.BinarySpace :=
  (ExtraspecialSquare.imageSpace (core z) A).map (coreNativeEquiv h e X).toLinearMap

theorem nativeImage_card (A : Subgroup (core z)) (hz : center (core z) ≤ A) :
    2 * Nat.card (nativeImage h e X A) = Nat.card A := by
  have he := Nat.card_congr (Submodule.equivMapOfInjective
    (coreNativeEquiv h e X).toLinearMap (coreNativeEquiv h e X).injective
      (ExtraspecialSquare.imageSpace (core z) A)).toEquiv
  change Nat.card (ExtraspecialSquare.imageSpace (core z) A) =
    Nat.card (nativeImage h e X A) at he
  rw [← he]
  exact ExtraspecialSquare.imageSpace_card (core z) A hz

theorem nativeImage_mem_iff (A : Subgroup (core z)) (hz : center (core z) ≤ A)
    (q : core z) : coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) q)) ∈ nativeImage h e X A ↔ q ∈ A := by
  have hi : Additive.ofMul (QuotientGroup.mk' (center (core z)) q) ∈
      ExtraspecialSquare.imageSpace (core z) A ↔ q ∈ A := by
    change q ∈ (A.map (QuotientGroup.mk' (center (core z)))).comap
      (QuotientGroup.mk' (center (core z))) ↔ q ∈ A
    rw [comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hz)]
  constructor
  · rintro ⟨v,hv,he⟩
    exact hi.mp ((coreNativeEquiv h e X).injective he ▸ hv)
  · intro hq
    exact Submodule.mem_map_of_mem (hi.mpr hq)

/-- The original intersection modulo the original center, with its native marking. -/
noncomputable def nativeIntersection (r : G) : Submodule (ZMod 2) M22TripleCover.BinarySpace :=
  nativeImage h e X (coreIntersection z r)

theorem nativeIntersection_card {r : G} (hr : IsConj z r) (hrQ : r ∈ ambientCore z)
    (hne : r ≠ z) : Nat.card (nativeIntersection h e X r) = 64 := by
  have hc := nativeImage_card h e X (coreIntersection z r)
    (center_le_coreIntersection h hr hrQ)
  rw [coreIntersection_card h hr hrQ hne] at hc
  change 2 * Nat.card (nativeIntersection h e X r) = 128 at hc
  omega

theorem nativeIntersection_singular {r : G} (hr : IsConj z r) (hne : r ≠ z) :
    ∀ v ∈ nativeIntersection h e X r, M22TripleCover.Unitary.quadraticForm v = 0 := by
  let := coreIntersection_elementary h hr hne
  rintro v ⟨w,hw,rfl⟩
  change M22TripleCover.Unitary.quadraticForm (coreNativeEquiv h e X w) = 0
  rw [coreNativeEquiv_quadratic h e X]
  exact ExtraspecialSquare.imageSpace_singular (core z) (coreIntersection z r) w hw

theorem intersectionImage_stable (r : core z)
    (hr : IsConj z ((r : centralizer z) : G)) (hrc : r ∉ center (core z))
    (g : centralizer z ⧸ core z) (hg : g ∈ coreVectorStabilizer h r)
    (v : CoreSpace (z := z))
    (hv : v ∈ ExtraspecialSquare.imageSpace (core z)
      (coreIntersection z ((r : centralizer z) : G))) :
    coreBinaryRepresentation h g v ∈ ExtraspecialSquare.imageSpace (core z)
      (coreIntersection z ((r : centralizer z) : G)) := by
  rw [coreVectorStabilizer_eq_centralizer_image h r hrc] at hg
  obtain ⟨a,ha,rfl⟩ := hg
  obtain ⟨q,hq,hqv⟩ := hv
  have hv : v = Additive.ofMul (QuotientGroup.mk' (center (core z)) q) :=
    congrArg Additive.ofMul hqv.symm
  rw [hv,coreBinaryRepresentation_apply,toMul_ofMul,coreQuotientAction_mk]
  refine ⟨MulAut.conjNormal a q,?_,rfl⟩
  obtain ⟨b,hb⟩ := isConj_iff.mp hr
  have ht : IsTypeJ4 ((r : centralizer z) : G) := by
    rw [← hb]
    exact type_map h (MulAut.conj b)
  have hn : (a : G) ∈ normalizer (ambientCore ((r : centralizer z) : G) : Set G) := by
    rw [LocalGeometry.normalizer_ambientCore ht]
    exact mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (mem_centralizer_singleton_iff.mp ha))
  change (a : G) * ((q : centralizer z) : G) * (a : G)⁻¹ ∈
    ambientCore ((r : centralizer z) : G)
  exact (mem_normalizer_iff.mp hn ((q : centralizer z) : G)).mp hq

theorem nativeIntersection_stable (r : core z)
    (hr : IsConj z ((r : centralizer z) : G)) (hrc : r ∉ center (core z)) :
    ∀ g ∈ nativeVectorStabilizer (coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r))),
    ∀ v ∈ nativeIntersection h e X ((r : centralizer z) : G),
      M22TripleCover.Ambient.binaryAction g v ∈
        nativeIntersection h e X ((r : centralizer z) : G) := by
  intro g hg v hv
  rw [← coreVectorStabilizer_native_image h e X r] at hg
  obtain ⟨g,hg,rfl⟩ := hg
  obtain ⟨w,hw,rfl⟩ := hv
  change M22TripleCover.Ambient.binaryAction (coreAmbientHom h e X g)
    (coreNativeEquiv h e X w) ∈ nativeIntersection h e X ((r : centralizer z) : G)
  rw [← coreAmbientHom_intertwines h e X]
  exact Submodule.mem_map_of_mem (intersectionImage_stable h r hr hrc g hg w hw)

theorem nativeIntersection_eq (r : core z)
    (hr : IsConj z ((r : centralizer z) : G)) (hne : ((r : centralizer z) : G) ≠ z)
    (hmark : coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) = VectorOrbits.decode 4) :
    nativeIntersection h e X ((r : centralizer z) : G) = ThreeSpace.Native.space := by
  have hrc : r ∉ center (core z) := by
    intro hc
    have he : Additive.ofMul (QuotientGroup.mk' (center (core z)) r) =
        (0 : CoreSpace (z := z)) := congrArg Additive.ofMul ((QuotientGroup.eq_one_iff r).mpr hc)
    rw [he,map_zero] at hmark
    exact (by decide +kernel : (0 : M22TripleCover.BinarySpace) ≠ VectorOrbits.decode 4) hmark
  apply ThreeSpace.Native.singular_stable_eq
  · exact nativeIntersection_card h e X hr
      (mem_map_of_mem (centralizer z).subtype r.property) hne
  · exact nativeIntersection_singular h e X hr hne
  · rw [← hmark]
    exact nativeIntersection_stable h e X r hr hrc


theorem coreIntersection_iff_native (r : core z)
    (hr : IsConj z ((r : centralizer z) : G)) (hne : ((r : centralizer z) : G) ≠ z)
    (hmark : coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) = VectorOrbits.decode 4)
    (q : core z) : q ∈ coreIntersection z ((r : centralizer z) : G) ↔
      coreNativeEquiv h e X (Additive.ofMul (QuotientGroup.mk' (center (core z)) q)) ∈
        ThreeSpace.Native.space := by
  rw [← nativeIntersection_eq h e X r hr hne hmark]
  exact (nativeImage_mem_iff h e X _ (center_le_coreIntersection h hr
    (mem_map_of_mem (centralizer z).subtype r.property)) q).symm

/-- The chosen source Sylow cubic contains a lift of the actual native scalar. -/
theorem exists_scalar_lift : ∃ a : centralizer z, a ∈ cubicSylowImage e X ∧
    coreAmbientHom h e X (QuotientGroup.mk' (core z) a) =
      Janko4.InvolutionCentralizers.First.QuotientExtension.scalarElement := by
  have hm : Janko4.InvolutionCentralizers.First.QuotientExtension.scalarElement ∈
      e.projection.ker.map (coreAmbientHom h e X) := by
    rw [coreAmbientHom_kernel_image h e X]
    exact Janko4.InvolutionCentralizers.First.QuotientExtension.scalarGenerator.property
  obtain ⟨k,hk,he⟩ := hm
  obtain ⟨x,hx⟩ := (cubicKernelEquiv e h X).surjective ⟨k,hk⟩
  refine ⟨((x : LocalGeometry.CubicLift.subgroup e) : centralizer z),
    mem_map_of_mem _ x.property,?_⟩
  have hx' := congrArg Subtype.val hx
  rw [cubicKernelEquiv_apply] at hx'
  exact (congrArg (coreAmbientHom h e X) hx').trans he

omit [IsExtraspecial 2 (core z)] in
theorem coreIntersection_conjugate (a : centralizer z) (r : G) (q : core z) :
    q ∈ coreIntersection z ((a : G)⁻¹ * r * (a : G)) ↔
      MulAut.conjNormal a q ∈ coreIntersection z r := by
  change ((q : centralizer z) : G) ∈ ambientCore ((a : G)⁻¹ * r * (a : G)) ↔
    ((MulAut.conjNormal a q : centralizer z) : G) ∈ ambientCore r
  have he : (a : G)⁻¹ * r * (a : G) = MulAut.conj (a : G)⁻¹ r := by simp
  rw [he,← ambientCore_map (MulAut.conj (a : G)⁻¹) r,mem_map_equiv]
  simp

/-- The scalar-transverse intersection in the literal core quotient. -/
theorem triple_nativeImage (r : core z)
    (hr : IsConj z ((r : centralizer z) : G)) (hne : ((r : centralizer z) : G) ≠ z)
    (hmark : coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) = VectorOrbits.decode 4)
    (a : centralizer z)
    (ha : coreAmbientHom h e X (QuotientGroup.mk' (core z) a) =
      Janko4.InvolutionCentralizers.First.QuotientExtension.scalarElement) :
    nativeImage h e X (coreIntersection z ((r : centralizer z) : G) ⊓
      coreIntersection z ((a : G)⁻¹ * ((r : centralizer z) : G) * (a : G))) =
      ThreeSpace.Native.line := by
  let r' : core z := MulAut.conjNormal a⁻¹ r
  have hr' : IsConj z ((r' : centralizer z) : G) :=
    hr.trans (isConj_iff.mpr ⟨(a : G)⁻¹,by simp [r']⟩)
  have hz : center (core z) ≤ coreIntersection z ((r : centralizer z) : G) ⊓
      coreIntersection z ((a : G)⁻¹ * ((r : centralizer z) : G) * (a : G)) :=
    le_inf (center_le_coreIntersection h hr (mem_map_of_mem _ r.property))
      (by simpa [r'] using (center_le_coreIntersection h hr' (mem_map_of_mem _ r'.property)))
  ext v
  obtain ⟨q,hq⟩ := QuotientGroup.mk'_surjective (center (core z))
    ((coreNativeEquiv h e X).symm v).toMul
  have hv : coreNativeEquiv h e X (Additive.ofMul (QuotientGroup.mk' (center (core z)) q)) = v := by
    rw [hq]
    exact (coreNativeEquiv h e X).apply_symm_apply v
  rw [← hv,nativeImage_mem_iff h e X _ hz,Subgroup.mem_inf,coreIntersection_conjugate,
    coreIntersection_iff_native h e X r hr hne hmark,
    coreIntersection_iff_native h e X r hr hne hmark]
  have he := coreAmbientHom_intertwines h e X (QuotientGroup.mk' (core z) a)
    (Additive.ofMul (QuotientGroup.mk' (center (core z)) q))
  rw [coreBinaryRepresentation_apply,toMul_ofMul,coreQuotientAction_mk,ha] at he
  rw [he,← ThreeSpace.Native.scalar_intersection]
  rfl


/-- A lift of the original cubic scalar gives an ambient intersection of order eight. -/
theorem triple_core_card (r : core z)
    (hr : IsConj z ((r : centralizer z) : G)) (hne : ((r : centralizer z) : G) ≠ z)
    (hmark : coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) = VectorOrbits.decode 4)
    (a : centralizer z)
    (ha : coreAmbientHom h e X (QuotientGroup.mk' (core z) a) =
      Janko4.InvolutionCentralizers.First.QuotientExtension.scalarElement) :
    Nat.card (ambientCore z ⊓ ambientCore ((r : centralizer z) : G) ⊓
      ambientCore ((a : G)⁻¹ * ((r : centralizer z) : G) * (a : G)) : Subgroup G) = 8 := by
  let r' : core z := MulAut.conjNormal a⁻¹ r
  have hr' : IsConj z ((r' : centralizer z) : G) :=
    hr.trans (isConj_iff.mpr ⟨(a : G)⁻¹,by simp [r']⟩)
  let A := coreIntersection z ((r : centralizer z) : G) ⊓
    coreIntersection z ((a : G)⁻¹ * ((r : centralizer z) : G) * (a : G))
  have hz : center (core z) ≤ A :=
    le_inf (center_le_coreIntersection h hr (mem_map_of_mem _ r.property))
      (by simpa [r'] using (center_le_coreIntersection h hr' (mem_map_of_mem _ r'.property)))
  have hc := nativeImage_card h e X A hz
  rw [triple_nativeImage h e X r hr hne hmark a ha,ThreeSpace.Native.line_card] at hc
  have hf : Function.Injective (coreInclusion z) :=
    Subtype.val_injective.comp Subtype.val_injective
  have hm : A.map (coreInclusion z) = ambientCore z ⊓
      ambientCore ((r : centralizer z) : G) ⊓
      ambientCore ((a : G)⁻¹ * ((r : centralizer z) : G) * (a : G)) := by
    dsimp only [A]
    rw [Subgroup.map_inf _ _ _ hf,coreIntersection_map,coreIntersection_map]
    ext g
    simp only [returningIntersection,Subgroup.mem_inf]
    tauto
  rw [← hm,card_map_of_injective hf]
  exact hc.symm


end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
