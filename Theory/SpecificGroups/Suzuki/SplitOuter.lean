module
public import Theory.SpecificGroups.Suzuki.BorelFieldQuotient
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex
public import Theory.GroupTheory.SolvableOuterQuotient
/-!
# A section of the actual Suzuki outer quotient

An inner field automorphism preserves the root subgroup, so its inner
element lies in the Borel. Inner action on the abelian Borel quotient is
trivial, while field action there is the literal action on field units.
It follows that this field automorphism is identity. Inner-field coverage
therefore identifies the field automorphism group with the actual outer
quotient and constructs a homomorphic section.

This handles fields whose degree shares an odd prime with the Suzuki
order. The Chapter 10 Suzuki pair-index argument uses this section to
exclude that prime from the quotient above the original component pair.
Source: GLS3, Theorem 2.5.12(b--f); Aschbacher--Smith 1.2.2(a), p.504.
-/

public noncomputable section
open Subgroup BenderSuzuki.PFAppendixIII
namespace BenderSuzuki.MatrixGroups
open SuzukiBorelFieldQuotient

theorem suzuki_field_inner_eq_one (m : ℕ) (hm : 0 < m)
    (σ : BinaryGaloisField (2*m+1) ≃ₐ[ZMod 2] BinaryGaloisField (2*m+1))
    (hσ : suzukiFieldAut m σ ∈ MulAut.innerSubgroup (SuzukiMatrixGroup m)) : σ = 1 := by
  obtain ⟨g,hg⟩ := hσ
  have hgB : g ∈ SuzukiBorelSubgroup m := by
    rw [←suzukiRootSubgroup_normalizer m hm]
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [hg]
    exact field_map_root m σ
  let b : SuzukiBorelSubgroup m := ⟨g,hgB⟩
  have hact : borelActor m b⁻¹ σ = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [borelActor_apply]
    change (MulAut.conj g⁻¹ * suzukiFieldAut m σ) x = x
    rw [←hg,map_inv,inv_mul_cancel]
    rfl
  have hfix (u : (BinaryGaloisField (2*m+1))ˣ) : Units.map σ.toRingEquiv.toMonoidHom u = u := by
    obtain ⟨x,rfl⟩ := projection_surjective m hm u
    rw [←projection_borelActor m hm b⁻¹ σ x,hact]
    rfl
  ext x
  change σ x = x
  by_cases hx : x = 0
  · simp [hx]
  · exact congrArg Units.val (hfix (Units.mk0 x hx))

@[expose] def suzukiOuterFieldMap (m : ℕ) :=
  (QuotientGroup.mk' (MulAut.innerSubgroup (SuzukiMatrixGroup m))).comp (suzukiFieldAutHom m)

theorem suzukiOuterFieldMap_bijective (m : ℕ) (hm : 0 < m) :
    Function.Bijective (suzukiOuterFieldMap m) := by
  constructor
  · apply (injective_iff_map_eq_one _).mpr
    intro σ hσ
    apply suzuki_field_inner_eq_one m hm σ
    change QuotientGroup.mk' _ (suzukiFieldAutHom m σ) = 1 at hσ
    rw [suzukiFieldAutHom_apply,QuotientGroup.mk'_apply] at hσ
    exact (QuotientGroup.eq_one_iff _).mp hσ
  · intro x
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective _ x
    obtain ⟨g,σ,rfl⟩ := suzukiAut_eq_inner_mul_field m (by omega) a
    refine ⟨σ,?_⟩
    have hg : QuotientGroup.mk' (MulAut.innerSubgroup (SuzukiMatrixGroup m)) (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨g,rfl⟩
    change QuotientGroup.mk' _ (suzukiFieldAutHom m σ) = _
    rw [map_mul,hg,one_mul,suzukiFieldAutHom_apply]

@[expose] def suzukiOuterSection (m : ℕ) (hm : 0 < m) :
    MulAut.Outer (SuzukiMatrixGroup m) →* MulAut (SuzukiMatrixGroup m) :=
  (suzukiFieldAutHom m).comp (MulEquiv.ofBijective (suzukiOuterFieldMap m)
    (suzukiOuterFieldMap_bijective m hm)).symm.toMonoidHom

theorem suzukiOuterSection_rightInverse (m : ℕ) (hm : 0 < m)
    (x : MulAut.Outer (SuzukiMatrixGroup m)) :
    QuotientGroup.mk' (MulAut.innerSubgroup (SuzukiMatrixGroup m)) (suzukiOuterSection m hm x) = x :=
  (MulEquiv.ofBijective (suzukiOuterFieldMap m) (suzukiOuterFieldMap_bijective m hm)).apply_symm_apply x
end BenderSuzuki.MatrixGroups
