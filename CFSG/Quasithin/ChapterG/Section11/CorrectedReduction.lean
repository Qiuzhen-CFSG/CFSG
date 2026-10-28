module
public import CFSG.Quasithin.ChapterG.Section11.ExchangedNaturalRanks
public import CFSG.Quasithin.ChapterG.Section11.ExchangedModelReduction

/-!
# The corrected low-rank reduction after full-linear recognition

All full-linear exchanged constituents are now recognized as the exceptional
whole S₈ natural-plus-dual action. The remaining exchanged constituents are
nondegenerate natural S₅, S₆ or S₈ modules. The S₇ row is excluded
by the rank of the literal index-two constituent stabilizer. The original thirteen-row conclusion
is preserved verbatim in `FullLinearFour.ConclusionWithFullLinearFour`.

This is a proved reduction from the original inputs, not an exhaustion theorem.
The solvable degree-six, whole-component, and nondegenerate exchanged branches
still need recognition. The strict quotient application uses the same literal
action, marked actor, form and relative Sylow-normality hypotheses.
Source: Aschbacher--Smith G.11.1--7, printed pp.364--367, with the
G.10.15 full-four source correction recorded in `docs/quasithin-proof-basis.md`.
-/

@[expose] public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11.ExchangedRecognition

/-- The exchanged remainder retains only nondegenerate natural symmetric
constituents, with the same original action and quotient map. -/
def RemainingComponentModels
    {D U : Type*} [Group D] [Finite D] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (B : LinearMap.BilinForm (ZMod 2) U)
    (v : U) (W : Submodule (ZMod 2) U) (X : Subgroup D)
    [IsElementaryAbelian 2 X] : Prop :=
  ∃ L : Subgroup D, IsComponent D L ∧ ⁅L,X⁆ ≠ ⊥ ∧
    Section10.ComponentOrthogonalData ρ B L ∧
    (Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X L (componentOrbit L ⊤)
      (finrank (ZMod 2) (Additive X)) ∨
      ∃ I : Submodule (ZMod 2) U,
        ∃ hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I,
          v ∉ I ∧ Section10.ExchangedConstituentGeometry ρ B v W X I ∧
          (∃ x : X, I.map (ρ x) ≠ I ∧ IsCompl I (I.map (ρ x))) ∧
          finrank (ZMod 2) U = 2 * finrank (ZMod 2) I ∧
          (finrank (ZMod 2) U = 8 ∨ finrank (ZMod 2) U = 12) ∧
          (B.restrict I).Nondegenerate ∧
          ∃ n, 5 ≤ n ∧ n ≤ 8 ∧ n ≠ 7 ∧ Section06.HasModelOn
            (kerRepresentation (Section09.constituentAction ρ (componentOrbit L ⊤)
              (X ⊓ subspaceStabilizer ρ I) I hI.invariant inf_le_right)) ⊤ ⊤
            (BinaryPermutation.naturalRepresentation (Fin n)))


variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

/-- The corrected catalogue or the precisely remaining recognition branches.
Every full-linear exchanged case is discharged without an extra premise. -/
theorem corrected_conclusion_or_remaining
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X) :
    FullLinearFour.ConclusionWithFullLinearFour ρ B v W X X₀ ∨
      (IsIrreducible ρ ∧ 6 ≤ finrank (ZMod 2) V ∧
        ((Group.IsSolvable G ∧ finrank (ZMod 2) (Additive X) = 2 ∧
            finrank (ZMod 2) V = 6) ∨
          (¬ Group.IsSolvable G ∧ RemainingComponentModels ρ B v W X))) := by
  rcases conclusion_or_whole_or_exchanged_models h cover hw hS with
    hc | ⟨hi,hd,hs | ⟨hn,L,hL,hm,horth,hwhole | hex⟩⟩
  · exact Or.inl (Or.inl hc)
  · exact Or.inr ⟨hi,hd,Or.inl hs⟩
  · exact Or.inr ⟨hi,hd,Or.inr ⟨hn,L,hL,hm,horth,Or.inl hwhole⟩⟩
  · obtain ⟨I,hI,hv,hgeo,hcompl,hdim,_,hmodels⟩ := hex
    rcases hmodels with ⟨n,hnl,_,hmodel⟩ | ⟨n,hnl,hnu,hmodel⟩
    · exact Or.inl (Or.inr
        (exchanged_full_linear_alternative h cover hw hS hn hL hm hI hgeo n hnl hmodel).2.2)
    · have hnd := exchanged_natural_nondegenerate h cover hw hS hn hL hm hI hgeo n
        (by omega) hmodel
      have hranks := exchanged_natural_ranks h cover hw hS hn hL hm hI hgeo n
        hnl hnu hmodel
      have hdims : (finrank (ZMod 2) V = 8 ∨ finrank (ZMod 2) V = 12) ∧ n ≠ 7 := by
        rcases hranks with hh | hh | hh <;> omega
      exact Or.inr ⟨hi,hd,Or.inr ⟨hn,L,hL,hm,horth,Or.inr
        ⟨I,hI,hv,hgeo,hcompl,hdim,hdims.1,hnd,n,hnl,hnu,hdims.2,hmodel⟩⟩⟩

end CFSG.Quasithin.ChapterG.Section11.ExchangedRecognition
