module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.Source523Application
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Exclusion of the intrinsic linear-three terminal residual

An intrinsic PSL₃(4) marking of the original two-residual quotient is
transported along the unique finite field of order four. The existing
terminal linear-residual contradiction then applies to the same H, central
line and chosen A₅ module, without an earlier classification premise.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

/-- An intrinsic PSL₃(4) quotient of the actual terminal residual is
impossible in the original chosen A₅ context. -/
theorem terminal_contradiction_of_intrinsic_linear_residual
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ centralizer (V₁ : Set G))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4) :
    False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hlinear
  let := Fintype.ofFinite F
  let := Fintype.ofFinite Components.F4
  let eF : F ≃+* Components.F4 := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF]
    exact (GaloisField.card 2 2 (by decide)).symm)
  exact terminal_contradiction_of_linear_residual d hCv houtside hcounter hH hHC
    (e.trans (Atlas.fieldEquivPSL 3 eF))

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
