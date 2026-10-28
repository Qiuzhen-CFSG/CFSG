module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.LargeGoldschmidt.ThirtyTwo
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.WreathedModels

/-!
# Complete component models for the full wreathed two-part

The literal Theorem C catalogue is filtered using the actual wreathed
Sylow invariants. This leaves precisely odd prime degree-three linear or
unitary central quotients. Their Sylow shapes fix the signs; scalar-cover
recognition identifies the original component and preserves its field.
The whole-group source application discharges the quotient Sylow-order
premise using the three-primary component center.

Source: Aschbacher--Smith F.6.18(10), printed pp.309--310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    {κ : GroupClass.{u}} {K : Subgroup G}

/-- The full catalogue, cover and field-sign calculation for the actual
component. Only the equality of its two-part with the ambient Sylow remains. -/
theorem component_models_of_full_wreathed_sylow
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (K ⧸ center K))
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G K) (T : Sylow 2 G) (eT : T ≃* WreathedThirtyTwo)
    (P : Sylow 2 (K ⧸ center K)) (hP : Nat.card P = 32) :
    ∃ p : ℕ, p.Prime ∧
      ((p % 8 = 5 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
        (Nonempty (K ≃* SL(3,F)) ∨ Nonempty (K ≃* PSL(3,F)))) ∨
       (p % 8 = 3 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F)
        (J : HermitianForm 3 F), Nat.card F = p ^ 2 ∧ (∀ x, J.conj x = x ^ p) ∧
        (Nonempty (K ≃* J.specialSubgroup) ∨
          Nonempty (K ≃* ProjectiveSpecialUnitaryMatrixGroup J)))) := by
  obtain ⟨p, hp, ho, hm⟩ := component_quotient_degree_three_of_wreathed32 hA hC hH e hK T eT P hP
  refine ⟨p, hp, ?_⟩
  rcases hm with hm | hm
  · obtain ⟨F, hF, hfin, hc, ⟨j⟩⟩ := hm
    obtain ⟨hs, hmodel⟩ := component_linear_three_wreathed_models hK T eT P hP hp ho hc j
    exact .inl ⟨hs, F, hF, hfin, hc, hmodel⟩
  · obtain ⟨F, hF, hfin, J, hc, hj, ⟨j⟩⟩ := hm
    obtain ⟨hs, hmodel⟩ := component_unitary_three_wreathed_models e hK T eT P hP J hp ho hc hj j
    exact .inr ⟨hs, F, hF, hfin, J, hc, hj, hmodel⟩

/-- With the source component equal to G, every catalogue, sign, Sylow-order
and scalar-cover witness is constructed from the original SQTK quotient. -/
theorem source_models_of_wreathed_and_component_top
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (K ⧸ center K))
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G K) (htop : K = ⊤)
    (T : Sylow 2 G) (eT : T ≃* WreathedThirtyTwo) :
    ∃ p : ℕ, p.Prime ∧
      ((p % 8 = 5 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
        (Nonempty (G ≃* SL(3,F)) ∨ Nonempty (G ≃* PSL(3,F)))) ∨
       (p % 8 = 3 ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F)
        (J : HermitianForm 3 F), Nat.card F = p ^ 2 ∧ (∀ x, J.conj x = x ^ p) ∧
        (Nonempty (G ≃* J.specialSubgroup) ∨
          Nonempty (G ≃* ProjectiveSpecialUnitaryMatrixGroup J)))) := by
  let P : Sylow 2 (K ⧸ center K) := default
  have hP : Nat.card P = 32 := (component_quotient_sylow_card_of_top e hK htop T P).trans
    ((Nat.card_congr eT.toEquiv).trans wreathedThirtyTwo_card)
  obtain ⟨p, hp, hm⟩ := component_models_of_full_wreathed_sylow hA hC hH e hK T eT P hP
  let j : G ≃* K := ((MulEquiv.subgroupCongr htop).trans topEquiv).symm
  refine ⟨p, hp, ?_⟩
  rcases hm with ⟨hs, F, hF, hfin, hc, hmodel⟩ | ⟨hs, F, hF, hfin, J, hc, hj, hmodel⟩
  · exact .inl ⟨hs, F, hF, hfin, hc,
      hmodel.imp (Nonempty.map (j.trans ·)) (Nonempty.map (j.trans ·))⟩
  · exact .inr ⟨hs, F, hF, hfin, J, hc, hj,
      hmodel.imp (Nonempty.map (j.trans ·)) (Nonempty.map (j.trans ·))⟩

end CFSG.Quasithin.ChapterF.SourceAssembly
