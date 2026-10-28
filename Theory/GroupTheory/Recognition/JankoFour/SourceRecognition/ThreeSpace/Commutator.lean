module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.ThreeSpace.Action

/-!
# The cubic commutator description of the three-space

The two commutators of the marked returning involution with a cubic scalar
and its inverse have native quotient vectors spanning the scalar line.
Adding the original core center therefore gives the entire three-space.
Conversely, cubic invariance puts both cyclic commutator subgroups inside
that same three-space. The formula uses the chosen Sylow subgroup of the
original cubic lift and the original inclusion in the ambient group.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*,
Invent. Math. 105 (1991), (4.3)(2), p.597, DOI 10.1007/BF01232280:
`Z = ⟨z, [r₁, X]⟩`.
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

theorem scalarPlane_eq_commutator (r : core z)
    (hmark : coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) = VectorOrbits.decode 4)
    (a : centralizer z) (haX : a ∈ cubicSylowImage e X)
    (ha : coreAmbientHom h e X (QuotientGroup.mk' (core z) a) = scalarElement) :
    ambientScalarPlane h e X = zpowers z ⊔
      ⁅zpowers ((r : centralizer z) : G), (cubicSylowImage e X).map (centralizer z).subtype⁆ := by
  let U := (cubicSylowImage e X).map (centralizer z).subtype
  let B : Subgroup G := zpowers z ⊔ ⁅zpowers ((r : centralizer z) : G), U⁆
  have hz : zpowers z ≤ ambientScalarPlane h e X := by
    rw [← LocalGeometry.core_center_image h,Subgroup.map_map]
    exact map_mono (center_le_scalarPlane h e X)
  have hr : r ∈ scalarPlane h e X := by
    change coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r)) ∈ ThreeSpace.Native.line
    rw [hmark]
    change vector 4 ∈ ThreeSpace.Native.line
    exact ⟨![1,0],by simp [ThreeSpace.Native.lineMap]⟩
  have hBz : center (core z) ≤ B.comap (coreInclusion z) := by
    intro q hq
    have hm : ((q : centralizer z) : G) ∈ zpowers z := by
      rw [← LocalGeometry.core_center_image h]
      exact mem_map_of_mem _ (mem_map_of_mem _ hq)
    exact (le_sup_left : zpowers z ≤ B) hm
  have haU : (a : G) ∈ U := mem_map_of_mem _ haX
  let q₁ : core z := r * (MulAut.conjNormal a r)⁻¹
  let q₂ : core z := r * (MulAut.conjNormal a⁻¹ r)⁻¹
  have h₁B : q₁ ∈ B.comap (coreInclusion z) := by
    have hc := commutator_mem_commutator (mem_zpowers ((r : centralizer z) : G)) haU
    change coreInclusion z q₁ ∈ B
    have he : coreInclusion z q₁ = ⁅((r : centralizer z) : G),(a : G)⁆ := by
      simp [q₁,coreInclusion,commutatorElement_def,mul_assoc]
    rw [he]
    exact (le_sup_right : ⁅zpowers ((r : centralizer z) : G), U⁆ ≤ B) hc
  have h₂B : q₂ ∈ B.comap (coreInclusion z) := by
    have hc := commutator_mem_commutator (mem_zpowers ((r : centralizer z) : G)) (U.inv_mem haU)
    change coreInclusion z q₂ ∈ B
    have he : coreInclusion z q₂ = ⁅((r : centralizer z) : G),(a : G)⁻¹⁆ := by
      simp [q₂,coreInclusion,commutatorElement_def,mul_assoc]
    rw [he]
    exact (le_sup_right : ⁅zpowers ((r : centralizer z) : G), U⁆ ≤ B) hc
  have h₁v : coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) q₁)) = vector 1471 := by
    have he := coreAmbientHom_intertwines h e X (QuotientGroup.mk' (core z) a)
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) r))
    rw [coreBinaryRepresentation_apply,toMul_ofMul,coreQuotientAction_mk,ha,hmark] at he
    have heq : Additive.ofMul (QuotientGroup.mk' (center (core z)) q₁) =
        Additive.ofMul (QuotientGroup.mk' (center (core z)) r) -
        Additive.ofMul (QuotientGroup.mk' (center (core z)) (MulAut.conjNormal a r)) := by
      simp only [q₁,map_mul,map_inv,ofMul_mul,ofMul_inv,sub_eq_add_neg]
    rw [heq,map_sub,hmark,he,ThreeSpace.Native.scalar_action]
    decide +kernel
  have h₂v : coreNativeEquiv h e X
      (Additive.ofMul (QuotientGroup.mk' (center (core z)) q₂)) = vector 1467 := by
    have heq : Additive.ofMul (QuotientGroup.mk' (center (core z)) q₂) =
        Additive.ofMul (QuotientGroup.mk' (center (core z)) r) -
        Additive.ofMul (QuotientGroup.mk' (center (core z)) (MulAut.conjNormal a⁻¹ r)) := by
      simp only [q₂,map_mul,map_inv,ofMul_mul,ofMul_inv,sub_eq_add_neg]
    rw [heq,map_sub,hmark,scalar_conjugate_mark h e X r hmark a ha]
    decide +kernel
  have him : ThreeSpace.Native.line ≤ nativeImage h e X (B.comap (coreInclusion z)) := by
    have h₁ := (nativeImage_mem_iff h e X _ hBz q₁).mpr h₁B
    have h₂ := (nativeImage_mem_iff h e X _ hBz q₂).mpr h₂B
    rw [h₁v] at h₁
    rw [h₂v] at h₂
    have h₄ : vector 4 ∈ nativeImage h e X (B.comap (coreInclusion z)) := by
      have hm := (nativeImage h e X (B.comap (coreInclusion z))).add_mem h₁ h₂
      rw [← vector_xor] at hm
      exact hm
    rintro v ⟨u,rfl⟩
    exact (nativeImage h e X (B.comap (coreInclusion z))).add_mem
      (Submodule.smul_mem _ _ h₄) (Submodule.smul_mem _ _ h₂)
  apply le_antisymm
  · rintro _ ⟨q,hq,rfl⟩
    exact (nativeImage_mem_iff h e X _ hBz q).mp (him hq)
  · apply sup_le hz
    have hrle : zpowers ((r : centralizer z) : G) ≤ ambientScalarPlane h e X :=
      zpowers_le.mpr (mem_map_of_mem (coreInclusion z) hr)
    have hnorm : ⁅ambientScalarPlane h e X,U⁆ ≤ ambientScalarPlane h e X :=
      le_normalizer_iff_commutator_le_left.mp (scalarPlane_cubicSylow_normalizes h e X a haX ha)
    exact (commutator_mono hrle (le_refl U)).trans hnorm

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
