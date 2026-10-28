module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Even
public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.Representation.GeneralLinearNatural

/-!
# Odd-order multiplicity images and the even endpoint

A Sylow subgroup in the literal action kernel makes the quotient have odd
order. A faithful two-dimensional representation in characteristic two
then makes the quotient abelian, by the proved odd-order linear theorem.
Transport to the original action image supplies the even outside-H
contradiction without assuming X₁-centralization or V-invariance.

Constructing the GL₂ embedding, its Sylow kernel, and the order-three
moved subgroup remains an explicit source obligation. This is a conditional
consumer, not the complete even branch of 11.5.7.
Source: Aschbacher--Smith, 11.5.7, printed p.782.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

theorem action_quotient_odd_of_sylow_kernel (A : Subgroup G) (hA : A ≤ E.G₁)
    (S : Sylow 2 A) (hS : (S : Subgroup A) ≤ actionCentralizer E A hA) :
    Odd (Nat.card (A ⧸ actionCentralizer E A hA)) := by
  rw [← index_eq_card]
  apply Nat.not_even_iff_odd.mp
  intro he
  exact S.not_dvd_index ((even_iff_two_dvd.mp he).trans (index_dvd_of_le hS))

theorem image_commutative_of_odd_linear_action
    (A : Subgroup G) (hA : A ≤ E.G₁)
    {F : Type*} [Field F] [CharP F 2]
    (ρ : Representation F (A ⧸ actionCentralizer E A hA) (Fin 2 → F))
    (hρ : Function.Injective ρ)
    (ho : Odd (Nat.card (A ⧸ actionCentralizer E A hA))) :
    IsMulCommutative (quotientAction E A hA).range := by
  have hq : IsMulCommutative (A ⧸ actionCentralizer E A hA) :=
    Representation.theorem_2_6_a ho (by simp) hρ
      (by rw [ringChar.eq F 2]; exact ho.not_two_dvd_nat)
  apply isMulCommutative_iff.mpr
  rintro ⟨a,g,rfl⟩ ⟨b,h,rfl⟩
  apply Subtype.ext
  let q := QuotientGroup.mk' (actionCentralizer E A hA)
  have hfa (x : A) : faithfulAction E A hA (q x) = quotientAction E A hA x := rfl
  have he := congrArg (faithfulAction E A hA) ((isMulCommutative_iff.mp hq) (q g) (q h))
  rw [map_mul, map_mul, hfa, hfa] at he
  exact he

theorem contradiction_of_plane_embedding
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hHG : E.H ≤ E.G₁) (hXG : E.X ≤ E.G₁)
    (S : Sylow 2 (C E))
    (hS : (S : Subgroup (C E)) ≤ actionCentralizer E (C E)
      (C_le_point_normalizer E (hH.1.1.2.trans hHG) hHG hXG))
    {F : Type*} [Field F] [CharP F 2]
    (ι : ((C E) ⧸ actionCentralizer E (C E)
      (C_le_point_normalizer E (hH.1.1.2.trans hHG) hHG hXG)) →* GL (Fin 2) F)
    (hι : Function.Injective ι)
    (X₀ : Subgroup G) (hX : X₀ ≤ X₁ E) (hmove : ⁅E.W,X₀⁆ = V) : False := by
  have ho := action_quotient_odd_of_sylow_kernel E (C E)
    (C_le_point_normalizer E (hH.1.1.2.trans hHG) hHG hXG) S hS
  have hab := image_commutative_of_odd_linear_action E (C E)
    (C_le_point_normalizer E (hH.1.1.2.trans hHG) hHG hXG)
    ((Representation.generalLinearNatural 2).comp ι)
    ((Representation.generalLinearNatural_injective 2).comp hι) ho
  exact contradiction_of_moved_seed E hH hHG hXG hab X₀ hX hmove

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside
