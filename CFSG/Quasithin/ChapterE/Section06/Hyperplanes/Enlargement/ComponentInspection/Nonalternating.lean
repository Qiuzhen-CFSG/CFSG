module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection.Transport
public import Theory.SpecificGroups.BinaryLinear.SylowFixedComponents
public import Theory.SpecificGroups.SymplecticFour.FieldFourComponents
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.FullGroup
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
public import Theory.SpecificGroups.Alternating.SmallFixedComponents
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.SpecificGroups.GL2.ThreeSolvable
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Nonalternating component inspections for E.6.22

The binary linear and field-four symplectic calculations exclude components
using the actual fixed group's two-core. For the binary symplectic endpoint,
the polar equivalence identifies the actual derived subgroup with A₆, whose
involution fixed groups are solvable. The M₁₁ fixed group is the actual GL₂(3).
The transport retains the chosen Sylow subgroup and order-two action.

Source: Aschbacher–Smith, E.6.8, pp.247–248, and its use in E.6.22, p.254.
The Borel and odd-linear inspections remain separate obligations.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
open Components Theory.SpecificGroups.SymplecticFour
variable {Y : Type*} [Group Y] [Finite Y]

/-- The actual PSL₄(2) model satisfies the nonexceptional inspection. -/
theorem linear_four_noCentralInvolutionComponent (hY : ClassicalGroup.IsPSL Y 4 2) :
    NoCentralInvolutionComponent Y := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hY
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  let c := (e.trans (Atlas.fieldEquivPSL 4 eF)).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 4))
  apply noCentralInvolutionComponent_of_fixedSubgroup c
  intro a ha S hS D
  have hne : a ≠ 1 := by intro he; simp [he] at ha
  exact BinaryLinear.OuterCyclic.sylow_fixed_no_component (Or.inl rfl) S a hne hS D

/-- Both permitted derived symplectic parameters retain their actual carriers. -/
theorem symplectic_noCentralInvolutionComponent {G : Type*} [Group G] [Finite G]
    (L : Subgroup G) (n : ℕ) (hn : n ≤ 2) (hm : SymplecticDerivedModel L n) :
    NoCentralInvolutionComponent L := by
  obtain ⟨hn0, F, _, _, hF, ⟨e⟩⟩ := hm
  have hn' : n = 1 ∨ n = 2 := by omega
  rcases hn' with rfl | rfl
  · have htwo : Nat.card F = 2 := hF
    apply noCentralInvolutionComponent_of_fixedSubgroup
      (e.trans (Binary.derivedEquivAlternatingSix htwo))
    intro a ha _ _ D
    let := alternatingGroup.SmallFixedComponents.six_fixed_solvable a ha
    exact not_isComponent_of_solvable D
  · let : CharP F 2 := EvenProjective.charTwo_of_card hF
    have hfour : Nat.card F = 4 := hF
    apply noCentralInvolutionComponent_of_fixedSubgroup
      (e.trans (derivedEquivFull_of_card_gt_two (by omega)))
    intro a ha S hS D
    exact fieldFour_sylow_fixed_no_component hfour S a ha hS D

/-- Every involution fixed group in the specified M₁₁ model is solvable. -/
theorem mathieu_eleven_noCentralInvolutionComponent
    (e : Y ≃* Sporadic.Mathieu.M11) : NoCentralInvolutionComponent Y := by
  apply noCentralInvolutionComponent_of_fixedSubgroup e
  intro a ha _ _ D
  let : Group.IsSolvable (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :=
    Matrix.GeneralLinearGroup.three_isSolvable
  let c := Sporadic.Mathieu.m11InvolutoryAutFixedEquiv a ha
  let : Group.IsSolvable a.fixedSubgroup :=
    Group.isSolvable_of_isSolvable_injective (f := c.toMonoidHom) c.injective
  exact not_isComponent_of_solvable D

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.ComponentInspection
