module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models.Transport
public import CFSG.Quasithin.Chapter11.Section01To02.SourceDefs
public import Theory.GroupTheory.CComponent.SL2OddCoreImage
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The odd-kernel SL₂ branch of the chief-image comparison

The case `K/O_{2,2'}(K) ≅ SL₂(p)` must retain the odd core and the central
involution of the full special-linear group.  A simple image of the intrinsic
C-component cannot detect its generalized Fitting subgroup: if the component
were quasisimple, the central quotient map would carry `O₂` onto the
nontrivial central two-core of `SL₂`; hence it is non-quasisimple, and
C-component minimality makes its generalized Fitting subgroup solvable.

This file provides the conditional source consumer.  The chief-section
construction supplies the nontrivial quotient map and its generalized-Fitting
survival; the model owner supplies simplicity of the actual image.  No
replacement by `PSL₂` or order-only argument is used.
Source: Aschbacher--Smith 11.1.2(1), 11.4.1(2), and the last paragraph of
11.5.8, printed p.784.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models
open Chapter12.Section02

private theorem odd_characteristic {F : Type*} [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (hlarge : 2 < p) (hc : Nat.card F = p) : (2 : F) ≠ 0 := by
  let := Fintype.ofFinite F
  let : Fact p.Prime := ⟨hp⟩
  let : CharP F p := charP_of_card_eq_prime_pow (f := 1)
    (by simpa only [Nat.card_eq_fintype_card, pow_one] using hc)
  intro hz
  exact Nat.not_dvd_of_pos_of_lt (by decide) hlarge ((CharP.cast_eq_zero_iff F p 2).mp hz)

/-- The genuine source prime and full special-linear marking suffice to kill
F* in any simple quotient. No characteristic or central-kernel premise is added. -/
theorem source_oddSL2_simple_image_kills
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Closure.Geometry D)
    (hK : Source.NormalComponentIn E.G₁ E.K)
    {p : ℕ} (hp : p = 5 ∨ (p.Prime ∧ 11 ≤ p))
    (hSL : Source.IsSL (Source.TwoOddQuotient E.K) 2 p)
    {J : Type*} [Group J] [IsSimpleGroup J]
    (f : (E.K ⧸ pCore 2 E.K) →* J) (hf : Function.Surjective f) :
    generalizedFitting (E.K ⧸ pCore 2 E.K) ≤ f.ker := by
  have hprime : p.Prime := hp.elim (fun h => h ▸ (by decide : Nat.Prime 5)) And.left
  have hlarge : 2 < p := by rcases hp with h | h <;> omega
  obtain ⟨F, hfield, hfinite, hcard, ⟨e⟩⟩ := hSL
  exact generalizedFitting_le_ker_of_odd_SL2_quotient
    (quotient_component_top E hK) (pCore_quotient_pCore_eq_bot 2)
    (odd_characteristic hprime hlarge hcard) e f hf

/-- An actual quotient action detecting F* cannot have simple range in the
odd-kernel source branch. The range restriction retains the original map. -/
theorem source_oddSL2_range_not_simple
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Closure.Geometry D)
    (hK : Source.NormalComponentIn E.G₁ E.K)
    {p : ℕ} (hp : p = 5 ∨ (p.Prime ∧ 11 ≤ p))
    (hSL : Source.IsSL (Source.TwoOddQuotient E.K) 2 p)
    {J : Type*} [Group J] (f : (E.K ⧸ pCore 2 E.K) →* J)
    (hF : ¬ generalizedFitting (E.K ⧸ pCore 2 E.K) ≤ f.ker) :
    ¬ IsSimpleGroup f.range := by
  intro hsimple
  let := hsimple
  have hk := source_oddSL2_simple_image_kills E hK hp hSL
    f.rangeRestrict f.rangeRestrict_surjective
  apply hF
  intro x hx
  exact congrArg Subtype.val (hk hx)

/-- The obstruction on the exact descended section action. The core-killing
premise is supplied by `componentAction_kills_twoCore` for an irreducible
chief section. Final chief construction and the G.6.4 simplicity conclusion
remain with `qt-d-1222-amalgam-chief-section`. -/
theorem quotientAction_oddSL2_not_simple
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Closure.Geometry D) (g : G)
    (hK : Source.NormalComponentIn E.G₁ E.K)
    {p : ℕ} (hp : p = 5 ∨ (p.Prime ∧ 11 ≤ p))
    (hSL : Source.IsSL (Source.TwoOddQuotient E.K) 2 p)
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) (actor E g) W)
    (hk : pCore 2 E.K ≤ (componentAction E g σ).ker)
    (hF : ¬ markedFitting E g ≤ σ.ker) :
    ¬ IsSimpleGroup (quotientAction E g σ hk).range := by
  apply source_oddSL2_range_not_simple E hK hp hSL
  exact fun hf => hF ((markedFitting_killed_iff E g σ hk).mpr hf)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models
