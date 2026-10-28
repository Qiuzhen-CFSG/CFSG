module
public import CFSG.Quasithin.ChapterE.Section02.ModuleBounds.OrbitLift
public import Theory.Representation.BinaryFourOrbit

/-!
# The original field-two symplectic core orbit

At actor rank at most two, P/Z has dimension four. Its faithful action
image has order divisible by |X/J|=720 because the original action kernel
lies in J. The binary four-space orbit count gives transitivity on the
fifteen nonzero vectors, and the original conjugation lift makes P
elementary. No module recognition or central-cover premise is needed.

Source: the Sp₄(2) equality case of Aschbacher–Smith E.2.15, printed p.228.
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement Representation
open Representation.BinaryOffender Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
  {T : Sylow 2 X} {V M : Subgroup X} {g : X}

theorem P_elementary_of_symplectic_four_binary_rank_le
    (h : Hypotheses T V M g) (hproper : V ≠ ⊤)
    (hfit : generalizedFitting X = pCore 2 X)
    (hcard : Nat.card F = 2) (ξ : (X ⧸ J M) ≃* Sp F)
    (hrank : Nat.log 2 ((Z V g).relIndex (A V M g)) ≤ 2) :
    IsElementaryAbelian 2 (P V M g) := by
  let := h.Z_normal
  let := h.core_geometry.1
  let q := QuotientGroup.mk' (Z V g)
  let U := (P V M g).map q
  let := h.quotient_direct_sum.1
  let ρ := (normalRepresentation U).comp q
  have hd : Module.finrank (ZMod 2) (Additive U) = 4 := by
    have hh := h.quotient_core_finrank_eq_twice_actor
    have hl := h.actor_rank_ge_symplectic_four hfit 1 (by decide)
      (by simpa using hcard) ξ
    dsimp only [U,q] at ⊢
    omega
  have hker : ρ.ker ≤ J M := by
    intro x hx
    apply h.twoCore_le_J
    apply h.quotient_core_centralizer_le hfit
    intro y hy
    have he := congrArg (fun f : Module.End (ZMod 2) (Additive U) =>
      ((f (Additive.ofMul ⟨y,hy⟩)).toMul : X ⧸ Z V g)) hx
    change q x * y * (q x)⁻¹ = y at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have he : ρ.ker.index = Nat.card (actionImage ρ) := by
    have ht : (actionHom ρ).range = ⊤ :=
      MonoidHom.range_eq_top.mpr (Representation.asGroupHom ρ).rangeRestrict_surjective
    rw [← actionHom_ker_eq ρ,index_ker,ht]
    exact Nat.card_congr (Subgroup.topEquiv :
      (⊤ : Subgroup (actionImage ρ)) ≃* actionImage ρ).toEquiv
  have hdiv : 45 ∣ Nat.card (actionImage ρ) := by
    rw [← he]
    apply (show 45 ∣ (J M).index from ?_).trans (index_dvd_of_le hker)
    rw [index_eq_card,Nat.card_congr ξ.toEquiv,card_sp,hcard]
    norm_num
  apply h.P_elementary_of_quotient_nonzero_transitive hproper hfit
  intro a b ha hb
  exact BinaryFourOrbit.representation_transitive ρ hd hdiv ha hb
end CFSG.Quasithin.ChapterE.TwoConjugate.Hypotheses
