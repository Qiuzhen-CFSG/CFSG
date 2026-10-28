module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.Models
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Descent
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.Binary160Application
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.ThirtySix
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.SixtyFour
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.EightyFour
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels.OneSixty
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.Presentation
import Mathlib.Tactic.FinCases

/-!
# The five larger Hall--Janko modular actions

The degree-36, degree-64 pair, degree-84 and degree-160 constructions are
assembled into the exact `LargeModelsExist` contract used by modular saturation.
Dimension distinguishes every pair except the two degree-64 actions, which have
unequal checked traces on the same word of the literal carrier generators.

The accompanying `Descent` module constructs literal carrier actions from
checked presentation relations and proves absolute irreducibility from rank-one
certificates over arbitrary characteristic-two fields. `modelsExist` discharges
all four numerical model inputs, retaining only presentation injectivity as its
earlier-source hypothesis. It supplies five pairwise inequivalent irreducible
actions over every algebraically closed characteristic-two field, in every
universe. Completeness of the modular catalogue remains a separate result.

Sources: the ATLAS J2 characteristic-two matrix candidates and J2G1-P2,
attributed and preserved in `LargeModels/source/README.md`.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels
open Sporadic.LeechRelated.J2
universe v

/-- Assemble the independently constructed simple models. Cross-degree
inequivalence follows from dimension; the degree-64 pair is kept intact. -/
theorem largeModelsExist_of_components
    (h36 : ModelsExist.{v} (fun _ : Fin 1 => 36))
    (h64 : ModelsExist.{v} (fun _ : Fin 2 => 64))
    (h84 : ModelsExist.{v} (fun _ : Fin 1 => 84))
    (h160 : ModelsExist.{v} (fun _ : Fin 1 => 160)) : LargeModelsExist.{v} := by
  intro F _ _ _
  obtain ⟨r36, hi36, _⟩ := h36 F
  obtain ⟨r64, hi64, hne64⟩ := h64 F
  obtain ⟨r84, hi84, _⟩ := h84 F
  obtain ⟨r160, hi160, _⟩ := h160 F
  let ρ : ∀ i, Representation F Carrier (Fin (largeDegree i) → F) := fun i =>
    match i with
    | ⟨0, _⟩ => r36 0
    | ⟨1, _⟩ => r64 0
    | ⟨2, _⟩ => r64 1
    | ⟨3, _⟩ => r84 0
    | ⟨4, _⟩ => r160 0
  refine ⟨ρ, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hi36 0
    · exact hi64 0
    · exact hi64 1
    · exact hi84 0
    · exact hi160 0
  · intro i j hij
    constructor
    intro e
    have hd := e.toLinearEquiv.finrank_eq
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hd
    have hcases : i = 1 ∧ j = 2 ∨ i = 2 ∧ j = 1 := by
      fin_cases i <;> fin_cases j <;> simp_all [largeDegree]
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact (hne64 (by decide : (0 : Fin 2) ≠ 1)).false e
    · exact (hne64 (by decide : (1 : Fin 2) ≠ 0)).false e

/-- Five actual pairwise inequivalent simple actions of the literal Hall--Janko
carrier, of dimensions 36, 64, 64, 84 and 160. The matrix relations, absolute
irreducibility and degree-64 trace separation are all proved by the component
constructions; only the earlier presentation exactness remains an input. -/
theorem modelsExist
    (hp : Function.Injective G2FourModule.Embedding.InnerRealization.Presentation.toCarrier) :
    LargeModelsExist.{v} :=
  largeModelsExist_of_components (ThirtySix.modelsExist hp) (SixtyFour.modelsExist hp)
    (EightyFour.modelsExist hp) (OneSixty.modelsExist hp)

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.LargeModels
