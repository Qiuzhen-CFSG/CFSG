module

public import Theory.Representation.OrthogonalFourMinusRankOne.HermitianQuinticQuotient
public import Theory.SpecificGroups.SL2.OddBorelMarking
import Mathlib.Tactic

/-!
# Quintic quotients with the supplied Hermitian Sylow subgroup

The simultaneous inner marking of an SL₂ Sylow subgroup and an odd subgroup
of its normalizer transports the actual invariant kernel to the canonical
upper-root coordinates. The full Hermitian quotient bound therefore applies
to the supplied Sylow and quintic actor, without replacing either action.
-/

public noncomputable section
namespace Representation.OrthogonalFourMinus.RankOne
open FiniteModel BinaryOffender Subgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

local instance : Algebra (ZMod 2) (fixedField 2) := ZMod.algebra _ 2
local instance : Module (ZMod 2) (Space 2) :=
  Module.compHom (Space 2) (algebraMap (ZMod 2) (fixedField 2))

private theorem action_conjugate (a g : SL(2,Field 2)) (X : Space 2) :
    SL2.BinarySmall.hermitian 2 (a*g*a⁻¹) (SL2.BinarySmall.hermitian 2 a X) =
      SL2.BinarySmall.hermitian 2 a (SL2.BinarySmall.hermitian 2 g X) := by
  rw [←Module.End.mul_apply, ←map_mul]
  simp only [mul_assoc, inv_mul_cancel, mul_one, map_mul, Module.End.mul_apply]

/-- The cardinal bound retains an arbitrary supplied Sylow subgroup and its
actual order-five normalizer element acting on the same full Hermitian module. -/
theorem sixtyFour_le_card_sylow_quintic_moving_quotient
    (P : Sylow 2 SL(2,Field 2)) (g : SL(2,Field 2))
    (hg : g ∈ normalizer (P : Set SL(2,Field 2))) (ho : orderOf g = 5)
    (W : Submodule (ZMod 2) (Space 2))
    (hP : ∀ p ∈ P, ∀ X ∈ W, SL2.BinarySmall.hermitian 2 p X ∈ W)
    (hW : ∀ X ∈ W, SL2.BinarySmall.hermitian 2 g X ∈ W)
    (hm : ∃ X : Space 2, SL2.BinarySmall.hermitian 2 g X - X ∉ W) :
    64 ≤ Nat.card ((Space 2) ⧸ W) := by
  let D := zpowers g
  have hD : D ≤ normalizer (P : Set SL(2,Field 2)) := zpowers_le.mpr hg
  have hDo : Odd (Nat.card D) := by rw [Nat.card_zpowers, ho]; decide
  obtain ⟨a,d,ha,hd⟩ := sylow_odd_subgroup_diagonal_coordinates P D hD hDo
  have hdi : Function.Injective d := by
    intro x y hxy
    apply Subtype.ext
    apply (MulAut.conj a).injective
    change a * x * a⁻¹ = a * y * a⁻¹
    rw [hd x, hd y, hxy]
  let gD : D := ⟨g,mem_zpowers g⟩
  have hd5 : orderOf (d gD) = 5 := by
    rw [orderOf_injective d hdi]
    simpa only [gD, Subgroup.orderOf_mk] using ho
  have hgdiag : a*g*a⁻¹ = CartanFixed.diagonal 2 (d gD) := hd gD
  let ρ := SL2.BinarySmall.hermitian 2
  let E : Space 2 ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofBijective (ρ a) (ρ.apply_bijective a)
  let W' := W.map (ρ a)
  have hmem (X : Space 2) : ρ a X ∈ W' ↔ X ∈ W := by
    constructor
    · rintro ⟨Y,hY,hYX⟩
      exact (E.injective hYX) ▸ hY
    · intro hX
      exact ⟨X,hX,rfl⟩
  have hU : ∀ (u : Field 2) (Y : Space 2), Y ∈ W' → ρ (upper 2 u) Y ∈ W' := by
    intro u Y hY
    obtain ⟨X,hX,rfl⟩ := hY
    have hu : upper 2 u ∈ (P : Subgroup SL(2,Field 2)).map (MulAut.conj a).toMonoidHom := by
      rw [ha]
      exact (mem_upperUnipotent _ _).mpr ⟨u,rfl⟩
    obtain ⟨p,hp,he⟩ := hu
    change a*p*a⁻¹ = upper 2 u at he
    rw [←he, action_conjugate]
    exact (hmem _).mpr (hP p hp X hX)
  have hD' : ∀ Y ∈ W', ρ (CartanFixed.diagonal 2 (d gD)) Y ∈ W' := by
    rintro Y ⟨X,hX,rfl⟩
    rw [←hgdiag, action_conjugate]
    exact (hmem _).mpr (hW X hX)
  have hm' : ∃ Y : Space 2, ρ (CartanFixed.diagonal 2 (d gD)) Y - Y ∉ W' := by
    obtain ⟨X,hX⟩ := hm
    refine ⟨ρ a X,?_⟩
    rw [←hgdiag, action_conjugate]
    change ρ a (ρ g X) - ρ a X ∉ W'
    rw [←map_sub, hmem]
    exact hX
  have hbound := sixtyFour_le_card_quintic_moving_quotient (d gD) hd5 W' hU hD' hm'
  have hcard : Nat.card ((Space 2) ⧸ W) = Nat.card ((Space 2) ⧸ W') :=
    Nat.card_congr (Submodule.Quotient.equiv W W' E rfl).toEquiv
  exact hcard ▸ hbound

/-- Every element of the supplied quintic normalizer subgroup fixes a small
quotient preserved by that subgroup and the supplied Sylow subgroup. -/
theorem quintic_fixes_quotient_of_card_le_thirtyTwo
    (P : Sylow 2 SL(2,Field 2)) (D : Subgroup SL(2,Field 2))
    (hD : D ≤ normalizer (P : Set SL(2,Field 2))) (hDcard : Nat.card D = 5)
    (W : Submodule (ZMod 2) (Space 2))
    (hP : ∀ p ∈ P, ∀ X ∈ W, SL2.BinarySmall.hermitian 2 p X ∈ W)
    (hW : ∀ d ∈ D, ∀ X ∈ W, SL2.BinarySmall.hermitian 2 d X ∈ W)
    (hcard : Nat.card ((Space 2) ⧸ W) ≤ 32) :
    ∀ d ∈ D, ∀ X : Space 2, SL2.BinarySmall.hermitian 2 d X - X ∈ W := by
  intro d hd X
  by_cases hone : d = 1
  · subst d
    simp
  have ho : orderOf d = 5 := by
    have hdiv := orderOf_dvd_natCard (⟨d,hd⟩ : D)
    rw [Subgroup.orderOf_mk, hDcard] at hdiv
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hdiv with he | he
    · exact False.elim (hone (orderOf_eq_one_iff.mp he))
    · exact he
  by_contra hm
  have hb := sixtyFour_le_card_sylow_quintic_moving_quotient P d (hD hd) ho W hP
    (hW d hd) ⟨X,hm⟩
  omega

end Representation.OrthogonalFourMinus.RankOne
