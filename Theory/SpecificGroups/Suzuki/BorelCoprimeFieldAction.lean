module

public import Theory.SpecificGroups.Suzuki.BorelFieldQuotient
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex

/-!
# Coprime Suzuki automorphisms preserving the root subgroup

An automorphism preserving the standard root subgroup has an inner--field
factorization with its inner factor in the standard Borel. If its order is
coprime to the Suzuki group order, a nonidentity automorphism must have a
nonidentity field factor: an inner automorphism has order dividing the group
order. This keeps the actual inner factor instead of assuming an invariant
torus.

Source: Aschbacher--Smith 11.5.6(3), printed p.781, using the Suzuki
inner--field automorphism theorem (GLS3, Theorem 2.5.12).
-/

open Subgroup BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open BenderSuzuki.MatrixGroups.SuzukiBorelFieldQuotient

public noncomputable section
namespace BenderSuzuki.MatrixGroups

/-- A nontrivial coprime root stabilizer acts nontrivially on field coefficients. -/
theorem exists_borel_inner_field_of_coprime (m : ℕ) (hm : 0 < m)
    (α : MulAut (SuzukiMatrixGroup m)) (hne : α ≠ 1)
    (hc : Nat.Coprime (orderOf α) (Nat.card (SuzukiMatrixGroup m)))
    (hr : (SuzukiRootSubgroup m).map α.toMonoidHom = SuzukiRootSubgroup m) :
    ∃ b : SuzukiBorelSubgroup m,
      ∃ σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1),
        σ ≠ 1 ∧ α = MulAut.conj (b : SuzukiMatrixGroup m) * suzukiFieldAut m σ := by
  obtain ⟨g, σ, he⟩ := suzukiAut_eq_inner_mul_field m hm α
  have hg : g ∈ SuzukiBorelSubgroup m := by
    rw [← suzukiRootSubgroup_normalizer m hm]
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hh : α.toMonoidHom = (MulAut.conj g).toMonoidHom.comp
        (suzukiFieldAut m σ).toMonoidHom := congrArg MulEquiv.toMonoidHom he
    rw [hh, ← map_map, field_map_root] at hr
    exact hr
  refine ⟨⟨g,hg⟩, σ, ?_, he⟩
  intro hs
  have hf : suzukiFieldAut m 1 = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    ext i j
    exact suzukiFieldAut_apply_entry m 1 x i j
  have he' : α = MulAut.conj g := by simpa only [hs, hf, mul_one] using he
  apply hne
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes hc (dvd_refl _)
  rw [he']
  exact (orderOf_map_dvd MulAut.conj g).trans (orderOf_dvd_natCard g)

end BenderSuzuki.MatrixGroups
