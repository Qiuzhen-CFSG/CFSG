module

public import Theory.SpecificGroups.GL2.FiveWreathSylow
public import Theory.SpecificGroups.GL2.SignedFiveOvergroups

/-!
# The squaring scalar in large two-subgroups of GL₂(5)

The scalar 2I is the square of an explicit element of the monomial Sylow
subgroup. Every subgroup of order sixteen or thirty-two in that Sylow
contains this square. Sylow conjugacy preserves the central scalar, so
it belongs to every two-subgroup of either order, without a marking.
-/

public noncomputable section
namespace Matrix.GeneralLinearGroup.FiveLargeTwoScalar
open Subgroup FiveWreathSylow
open scoped Pointwise Matrix
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev L := GL (Fin 2) (ZMod 5)
private abbrev u : (ZMod 5)ˣ := Units.mk0 (2 : ZMod 5) (by decide)
private abbrev scalar : L := SignedFive.scalar

private theorem scalar_conj (g : L) : (MulAut.conj g) scalar = scalar := by
  have hc : g * scalar = scalar * g := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SignedFive.scalar,diagonalPair_val,Matrix.mul_apply,Fin.sum_univ_two,mul_comm]
  change g * scalar * g⁻¹ = scalar
  rw [hc,mul_inv_cancel_right]

private theorem sylow_scalar_square (S : Sylow 2 L) :
    ∃ x : S, (x : L) ^ 2 = scalar := by
  let w : UnitWreath := ⟨fun x => if x = 1 then u else 1,tau⟩
  let x : L := monomialHom w
  have hx : x ∈ monomialSubgroup := by
    refine ⟨wreathUnitEquiv.symm w,?_⟩
    change monomialHom (wreathUnitEquiv (wreathUnitEquiv.symm w)) = monomialHom w
    rw [wreathUnitEquiv.apply_symm_apply]
  have hx2 : x ^ 2 = scalar := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [x,u,monomialHom,monomial,w,switch,pow_two,tau_ne_one,
        SignedFive.scalar,diagonalPair_val,coordinateSwap_val,Matrix.mul_apply,Fin.sum_univ_two]
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq L monomialSylow S
  have hmem : (MulAut.conj g) x ∈ S := by
    rw [←hg]
    change (MulAut.conj g) • x ∈ (MulAut.conj g) • (monomialSylow : Set L)
    exact Set.smul_mem_smul_set hx
  refine ⟨⟨(MulAut.conj g) x,hmem⟩,?_⟩
  rw [←map_pow,hx2,scalar_conj]

/-- Every two-subgroup of order sixteen or thirty-two contains the literal
central scalar 2I. No choice of coordinates for the subgroup is assumed. -/
theorem scalar_mem (P : Subgroup (GL (Fin 2) (ZMod 5)))
    (hp : IsPGroup 2 P) (hc : Nat.card P = 16 ∨ Nat.card P = 32) :
    SignedFive.scalar ∈ P := by
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  have hSc : Nat.card S = 32 :=
    (Nat.card_congr (S.equiv monomialSylow).toEquiv).trans monomialSubgroup_card
  let U := P.subgroupOf S
  have hUc : Nat.card U = Nat.card P := Nat.card_congr (subgroupOfEquivOfLe hS).toEquiv
  have hi : U.index = 1 ∨ U.index = 2 := by
    have hh := U.card_mul_index
    rw [hUc,hSc] at hh
    rcases hc with hc | hc <;> rw [hc] at hh <;> omega
  obtain ⟨x,hx⟩ := sylow_scalar_square S
  have hxU : x ^ 2 ∈ U := by
    rcases hi with hi | hi
    · rw [index_eq_one.mp hi]
      exact mem_top _
    · exact U.sq_mem_of_index_two hi x
  change (x : L) ^ 2 ∈ P at hxU
  rwa [hx] at hxU

end Matrix.GeneralLinearGroup.FiveLargeTwoScalar
