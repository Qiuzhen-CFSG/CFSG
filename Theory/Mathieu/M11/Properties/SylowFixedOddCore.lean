module
public import Theory.Mathieu.M11.Properties.FourNormalizer
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.Mathieu.M11.Properties.SylowTwo
public import Theory.GroupTheory.SemidihedralFourSubgroup
public import Theory.SpecificGroups.GL2.ThreeCharacteristicTwo
public import Theory.GroupAction.SylowFixedInvolutionOddCore
public import Theory.GroupTheory.SelfCentralizingCore

/-!
# Odd cores for Sylow-fixing involutions acting on M₁₁

Every Mathieu automorphism is inner. An actual four-subgroup of the specified
semidihedral Sylow is self-centralizing, so every pointwise Sylow fixer is
implemented inside that Sylow. Inner involution fixed groups are GL₂(3),
whose odd core is trivial. The faithful-overgroup transfer keeps the actors.

Source: Aschbacher–Smith E.6.19, printed p.252; 2.5.8(5), pp.556–557,
and 16.1.5(3), p.1171. The carrier remains the original Witt-design M₁₁.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu

/-- Every full pointwise Sylow fixer is inner by an element of the same Sylow. -/
theorem m11_sylow_fixed_inner (S : Sylow 2 M11) (α : MulAut M11)
    (hfix : ∀ x ∈ S, α x = x) : ∃ z ∈ S, α = MulAut.conj z := by
  obtain ⟨P,a,b,ha,hb,hc,hgen⟩ := m11_exists_semidihedral_sylow
  let e := P.equiv S
  have hagen : closure ({e a,e b} : Set S) = ⊤ := by
    have hh := congrArg (Subgroup.map e.toMonoidHom) hgen
    rw [MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton,
      map_top_of_surjective _ e.surjective] at hh
    exact hh
  have hconj : e b * e a * (e b)⁻¹ = (e a)^3 := by
    rw [← map_inv,← map_mul,← map_mul,hc,map_pow]
  obtain ⟨F,hF,hcard,hFS⟩ := Semidihedral.exists_four_le (S : Subgroup M11)
    (n := 4) (by decide) (e a) (e b) ((e.orderOf_eq a).trans ha)
      ((e.orderOf_eq b).trans hb) hconj hagen
  let := hF
  let : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour F := ⟨hcard,IsElementaryAbelian.exponent_eq_prime⟩
  obtain ⟨z,rfl⟩ := automorphism_inner_of_equiv_m11 (MulEquiv.refl _) α
  have hz : z ∈ centralizer (F : Set M11) := by
    intro x hx
    exact (mul_inv_eq_iff_eq_mul.mp (hfix x (hFS hx))).symm
  rw [m11_four_centralizer F] at hz
  exact ⟨z,hFS hz,rfl⟩

/-- The original acting group's involution centralizer has trivial odd core. -/
theorem m11_sylowFixedInvolution_oddCore_eq_bot
    {H : Type*} [Group H] [Finite H] {φ : H →* MulAut M11} {E : Subgroup H}
    (d : Theory.GroupAction.SylowFixedInvolution φ E) :
    pPrimeCore 2 (centralizer (E : Set H)) = ⊥ := by
  apply d.oddCore_eq_bot_of_inner m11_center_eq_bot m11_sylow_fixed_inner
  intro S z hz _
  have ha : orderOf (MulAut.conj z) = 2 :=
    (MulAut.conj_orderOf_of_center_eq_bot m11_center_eq_bot z).trans hz
  have ho := pPrimeCore_eq_bot_of_equiv (m11InvolutoryAutFixedEquiv (MulAut.conj z) ha)
    (pPrimeCore_eq_bot_of_centralizer_pCore_le 2
      Matrix.GeneralLinearGroup.three_centralizer_twoCore_le)
  rwa [MulAut.fixedSubgroup_conj] at ho
end Sporadic.Mathieu
