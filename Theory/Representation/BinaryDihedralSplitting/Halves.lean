module
public import Theory.Representation.BinaryDihedralSplitting
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryOffender.ComponentSum
public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.MaximalIntersection
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The two conjugate reflection halves of a binary dihedral action

For an odd-prime rotation r and reflection t, the moved space of r is
U ⊕ rU, where U is its t-fixed subspace. Apply the binary dihedral splitting
to t and its conjugate rtr⁻¹. Their product is r⁻², which generates the same
odd-order rotation group. Conjugation transports the second fixed half.

This is the precise A.1.44 splitting used in the proof of G.9.2, with the
actual rotation, reflection and coinvariant kernel conventions.
Source: Aschbacher--Smith A.1.44 and G.9.2, printed pp.32 and351--353.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender DihedralGroup
namespace Representation.BinaryDihedralSplitting
universe v

private theorem fixed_cyclic_eq_kernel {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V) (g : G) :
    fixedSpace ρ (zpowers g) = LinearMap.ker (ρ g - 1) := by
  ext v
  rw [mem_fixedSpace_zpowers_iff, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]

/-- The actual reflection-fixed half and its rotation image split the moved space. -/
theorem rotation_reflection_halves {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (σ : Representation (ZMod 2) (DihedralGroup p) W) :
    let M := Coinvariants.ker (σ.comp (zpowers (r 1)).subtype)
    let C := LinearMap.ker (σ (r 1) - 1)
    let U := M ⊓ LinearMap.ker (σ (sr 0) - 1)
    IsCompl C M ∧ Disjoint U (U.map (σ (r 1))) ∧ U ⊔ U.map (σ (r 1)) = M := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let R : DihedralGroup p := r 1
  let t : DihedralGroup p := sr 0
  let u : DihedralGroup p := sr (-2)
  have htu : t * u = (R ^ 2)⁻¹ := by simp [t, u, R, pow_two]; ring
  have hz : zpowers (t * u) = zpowers R := by
    rw [htu, zpowers_inv]
    apply le_antisymm
    · exact zpowers_le.mpr (pow_mem (mem_zpowers R) 2)
    · apply zpowers_le.mpr
      rw [mem_zpowers_pow_iff, show orderOf R = p by exact orderOf_r_one]
      exact (Nat.coprime_two_left.mpr ho).gcd_eq_one
  have hh := BinaryDihedralSplitting.splitting_of_odd_product σ t u
    (sr_mul_self _) (sr_mul_self _) (by
      rw [htu, orderOf_inv]
      exact ho.of_dvd_nat (by simpa [R] using orderOf_pow_dvd (x := R) 2))
  rw [hz] at hh
  let M := subspaceCommutator σ ⊤ (zpowers R)
  let U := M ⊓ fixedSpace σ (zpowers t)
  have hu := BinaryDihedralSplitting.splitting_of_odd_product σ u t
    (sr_mul_self _) (sr_mul_self _) (by
      have he : u * t = (t * u)⁻¹ := by simp [t, u]
      rw [he, orderOf_inv, htu, orderOf_inv]
      exact ho.of_dvd_nat (by simpa [R] using orderOf_pow_dvd (x := R) 2))
  have hzu : zpowers (u * t) = zpowers R := by
    have he : u * t = (t * u)⁻¹ := by simp [t, u]
    rw [he, zpowers_inv, hz]
  rw [hzu] at hu
  have hR : M.map (σ R) = M := by
    change (subspaceCommutator σ ⊤ (zpowers R)).map (σ R) = _
    rw [moved_map_conjugate, MonoidHom.map_zpowers]
    congr 1
    simp
  have hRt : (zpowers t).map (MulAut.conj R).toMonoidHom = zpowers u := by
    rw [MonoidHom.map_zpowers]
    congr 1
    simp [R, t, u, MulAut.conj_apply]
    ring
  have hU : U.map (σ R) = M ⊓ fixedSpace σ (zpowers u) := by
    rw [Submodule.map_inf _ (σ.apply_bijective R).injective, hR]
    rw [← Representation.RegularCyclicNormalClosure.FactorConstruction.fixedSpace_map_conj, hRt]
  have hmove : Coinvariants.ker (σ.comp (zpowers R).subtype) = M := by
    exact (subspaceCommutator_top_eq_coinvariants σ (zpowers R)).symm
  change IsCompl (LinearMap.ker (σ R - 1)) (Coinvariants.ker (σ.comp (zpowers R).subtype)) ∧ _
  rw [hmove, ← fixed_cyclic_eq_kernel σ R, ← fixed_cyclic_eq_kernel σ t]
  change IsCompl _ M ∧ Disjoint U (U.map (σ R)) ∧ U ⊔ U.map (σ R) = M
  rw [hU]
  dsimp only [U, M]
  rw [hh.2.2.2, hu.2.2.2]
  exact ⟨hh.1.symm, hh.2.1, hh.2.2.1⟩

end Representation.BinaryDihedralSplitting
