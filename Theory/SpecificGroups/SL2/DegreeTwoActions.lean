module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import Theory.SpecificGroups.GL2.ProjectiveFourGroupObstruction
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.FieldTheory.Finiteness

/-!
# Nontrivial actions of SL₂(5) in degree two

A nontrivial two-dimensional representation of SL₂(5) over a field of odd
characteristic sends the central involution to minus the identity. Perfectness
forces determinant one. If the central involution were killed, the image of
`w = !![0,1; -1,0]` would be a determinant-one involution and hence scalar.
Then the kernel would contain the noncentral commutator of w with
`u = !![1,1; 0,1]`. Quasisimplicity would force the whole action to be trivial.

The group-action version uses the canonical vector space structure of an
elementary abelian group of order p². A basis identifies its automorphisms
with GL₂, and the matrix conclusion transports back to inversion on the
original group. No irreducibility or faithfulness hypothesis is required.

This supplies the degree-two action step used in Aschbacher–Smith, combined
1 March 2004 manuscript, proof of A.3.6, printed pp.44–45. The basis conversion
follows `Theory.ElementaryAbelian.AutomorphismLinearModelEight`.
-/

open Subgroup Theory.GroupTheory Matrix
open scoped IsMulCommutative MatrixGroups commutatorElement
namespace Matrix.SpecialLinearGroup.DegreeTwo

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private abbrev SL5 := SL(2, ZMod 5)
private instance sl5_quasisimple : IsQuasisimple SL5 where
  toIsPerfect := ⟨Matrix.SL2.commutator_eq_top (a := (2 : ZMod 5)) (by decide) (by decide)⟩
  simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := ZMod 5) (by norm_num)

private def w : SL5 := ⟨!![0, 1; -1, 0], by decide⟩
private def u : SL5 := ⟨!![1, 1; 0, 1], by decide⟩
private theorem w_sq : w ^ 2 = -1 := by decide +kernel
private theorem commutator_not_central : ⁅w, u⁆ ∉ center SL5 := by
  intro h
  have hh := Subgroup.mem_center_iff.mp h u
  have hne : u * ⁅w, u⁆ ≠ ⁅w, u⁆ * u := by decide +kernel
  exact hne hh

private theorem det_eq_one {F : Type*} [Field F]
    (f : SL5 →* GeneralLinearGroup (Fin 2) F) (g : SL5) : (f g).det = 1 := by
  let d := GeneralLinearGroup.det.comp f
  have h : d = 1 := by
    apply MonoidHom.ker_eq_top_iff.mp
    apply top_unique
    rw [← Group.IsPerfect.commutator_eq_top (G := SL5)]
    exact Abelianization.commutator_subset_ker d
  exact DFunLike.congr_fun h g

/-- A nontrivial degree-two representation in odd characteristic detects the
central involution as minus the identity. -/
public theorem map_neg_one_of_nontrivial {F : Type*} [Field F] (hF : (2 : F) ≠ 0)
    (f : SL(2, ZMod 5) →* GeneralLinearGroup (Fin 2) F) (hf : f ≠ 1) : f (-1) = -1 := by
  have hne : f (-1) ≠ 1 := by
    intro hz
    have hwsq : f w ^ 2 = 1 := by rw [← map_pow, w_sq, hz]
    have hw := GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one
      hF (f w) hwsq (det_eq_one f w)
    have hcomm : ⁅w, u⁆ ∈ f.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      rcases hw with hw | hw <;> rw [hw] <;> simp
    rcases IsQuasisimple.normal_le_center_or_eq_top f.ker with h | h
    · exact commutator_not_central (h hcomm)
    · exact hf (MonoidHom.ker_eq_top_iff.mp h)
  have hsq : f (-1) ^ 2 = 1 := by rw [← map_pow]; norm_num
  exact (GeneralLinearGroup.eq_one_or_neg_one_of_sq_eq_one_of_det_eq_one
    hF (f (-1)) hsq (det_eq_one f (-1))).resolve_left hne

/-- The central involution inverts every elementary abelian plane on which
SL₂(5) acts nontrivially, in odd characteristic. -/
public theorem action_neg_one_of_nontrivial {V : Type*} [Group V] [Finite V]
    {p : ℕ} [Fact p.Prime] [IsElementaryAbelian p V]
    (hp : Odd p) (hc : Nat.card V = p ^ 2)
    (ρ : SL(2, ZMod 5) →* MulAut V) (hρ : ρ ≠ 1) : ∀ v, ρ (-1) v = v⁻¹ := by
  classical
  have hpow : p ^ Module.finrank (ZMod p) (Additive V) = p ^ 2 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive V)
    change Nat.card V = _ at hsize
    simpa only [Nat.card_zmod, hc] using hsize.symm
  have hdim : Module.finrank (ZMod p) (Additive V) = 2 :=
    Nat.pow_right_injective (Fact.out : p.Prime).one_lt hpow
  let autLinear : MulAut V ≃* (Additive V ≃ₗ[ZMod p] Additive V) :=
    { toFun := fun aut =>
        { aut.toAdditive with map_smul' := ZMod.map_smul aut.toAdditive }
      invFun := fun aut => MulEquiv.toAdditive.symm aut.toAddEquiv
      left_inv := by intro aut; ext; rfl
      right_inv := by intro aut; ext; rfl
      map_mul' := by intro aut other; ext; rfl }
  let b := Module.finBasisOfFinrankEq (ZMod p) (Additive V) hdim
  let d : GeneralLinearGroup (Fin 2) (ZMod p) ≃* (Additive V ≃ₗ[ZMod p] Additive V) :=
    (GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod p) (Additive V))
  let e : MulAut V ≃* GeneralLinearGroup (Fin 2) (ZMod p) := autLinear.trans d.symm
  have hf : e.toMonoidHom.comp ρ ≠ 1 := by
    intro h
    apply hρ
    ext g : 1
    apply e.injective
    simpa using DFunLike.congr_fun h g
  have hp2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have he : p = 2 := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hd
    subst p
    norm_num at hp
  have he := map_neg_one_of_nontrivial hp2 (e.toMonoidHom.comp ρ) hf
  have hlin : autLinear (ρ (-1)) =
      (GeneralLinearGroup.toLin' b (-1)).toLinearEquiv := by
    change autLinear (ρ (-1)) = d (-1)
    simpa [e] using congrArg d he
  intro v
  have hv := congrArg (fun a : Additive V ≃ₗ[ZMod p] Additive V => a (Additive.ofMul v)) hlin
  change Additive.ofMul (ρ (-1) v) = _ at hv
  rw [GeneralLinearGroup.toLin'_apply] at hv
  have hm : (↑(-1 : GeneralLinearGroup (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) = -1 := rfl
  rw [hm, Matrix.neg_mulVec, Matrix.one_mulVec, map_neg] at hv
  simpa [Fintype.linearCombination_apply] using congrArg Additive.toMul hv

end Matrix.SpecialLinearGroup.DegreeTwo
