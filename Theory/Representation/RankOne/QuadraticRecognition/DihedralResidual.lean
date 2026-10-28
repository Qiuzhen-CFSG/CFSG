module
public import Theory.Representation.RankOne.QuadraticRecognition.SmallSolvableActors
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Residual-fixed-free actions of the order-ten group

A representation of a core-free group of order ten with no residual-fixed
vectors is faithful: a kernel containing the five-part contains the entire
two-residual, while the remaining possible kernel is a normal two-group.
The faithful dihedral quadratic square bound therefore applies to the
original action. This includes the smallest binary dihedral module, whose
involution has fixed-space index four.

Source: DGS, Groups and Graphs (1985), the separate D10 row of Hypothesis B′
and the quadratic comparison used in 9.3, printed p.142.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace Representation.RankOne.QuadraticRecognition

/-- The residual-fixed-free action of a core-free order-ten group is faithful. -/
theorem faithful_of_card_ten_of_residual_fixed_eq_bot
    {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [Nontrivial W]
    (hc : Nat.card D = 10) (hcore : pCore 2 D = ⊥)
    (ρ : Representation (ZMod 2) D W)
    (hres : fixedSpace ρ (pResidual 2 D) = ⊥) : Function.Injective ρ := by
  have hnot : ¬ pResidual 2 D ≤ ρ.ker := by
    intro h
    have he : fixedSpace ρ (pResidual 2 D) = ⊤ := by
      apply top_unique
      intro v _ g
      change ρ g v = v
      rw [show ρ g = 1 from h g.property]
      rfl
    exact top_ne_bot (he.symm.trans hres)
  apply ρ.ker_eq_bot_iff.mp
  by_cases hd : 5 ∣ Nat.card ρ.ker
  · have hi : ρ.ker.index ∣ 2 := by
      apply Nat.dvd_of_mul_dvd_mul_right (by decide : 0 < 5)
      have hm := Nat.mul_dvd_mul_right hd ρ.ker.index
      rw [ρ.ker.card_mul_index, hc, mul_comm 5 ρ.ker.index] at hm
      exact hm
    have hp : IsPGroup 2 (D ⧸ ρ.ker) :=
      IsPGroup.of_card_dvd_pow (n := 1)
        (by simpa only [pow_one, ←Subgroup.index_eq_card] using hi)
    exact (hnot ((pResidual_le_iff_isPGroup_quotient 2 ρ.ker).mpr hp)).elim
  · have hkcard : Nat.card ρ.ker ∣ 2 := by
      apply ((Nat.prime_five.coprime_iff_not_dvd.mpr hd).symm).dvd_of_dvd_mul_right
      simpa only [hc] using ρ.ker.card_subgroup_dvd_card
    have hp : IsPGroup 2 ρ.ker :=
      IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hkcard)
    have hk : ρ.ker ≤ pCore 2 D := le_sSup ⟨inferInstance, hp⟩
    exact bot_unique (hk.trans hcore.le)

/-- The square bound retains the actual residual-fixed-free action and actor. -/
theorem card_ten_residual_fixed_quadratic_square_bound
    {D W : Type*} [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W] [Nontrivial W] [Finite W]
    (hc : Nat.card D = 10) (hcore : pCore 2 D = ⊥)
    (ρ : Representation (ZMod 2) D W)
    (hres : fixedSpace ρ (pResidual 2 D) = ⊥)
    (A : Subgroup D) (hp : IsPGroup 2 A) (hq : IsQuadratic ρ A) :
    Nat.card A ^ 2 ≤ Nat.card (W ⧸ fixedSpace ρ A) := by
  exact ten_or_twenty_quadratic_square_bound (Or.inl hc) hcore ρ
    (faithful_of_card_ten_of_residual_fixed_eq_bot hc hcore ρ hres) A hp hq

end Representation.RankOne.QuadraticRecognition
