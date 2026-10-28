module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.LinearTwo
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.ComponentDecomposition

/-!
# Terminal consumers after the rank-one sieve

The unitary and large PSL₂ exclusions leave only the relatively normal
PSL₂(4) endpoint. Its exclusion now suffices to construct every individual
component model, the actual one/two-component alternatives with diagram
action, the residual factorization, and the full component sum on U/Z.

The endpoint premise is explicitly retained for the same owner,
qt-e-suitable-component-supports. These are conditional consumers, not a
completed source catalogue or natural-support decomposition. Directness,
natural-support recognition and suitable-vector assembly also remain there.
Original 14.6.18 remains with qt-e-14625-source.
Source: Aschbacher--Smith 14.6.20--23, printed pp.1037--1038.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.OneCohomology
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Classification
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
    (hm : ∀ K : Subgroup G, K ≤ Mc → (K.subgroupOf Mc).IsCComponent →
      (K.subgroupOf Mc).Normal → ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4)

include hG hempty hM hunique hmany hcard e hab hsolv hm

/-- Excluding the single remaining endpoint completes the original component models. -/
theorem source_all_component_models_of_no_four
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent) :
    ComponentQuotientModels K := by
  rcases Classification.Sieve.source_component_four_or_terminal_models
      hG T hempty hM hunique hmany hcard e hab hsolv Mc
      (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK with ⟨hn,hfour⟩ | hmK
  · exact (hm K hKM hK hn hfour).elim
  · exact hmK

/-- The actual one/two-component alternatives and diagram action after the
unitary and large linear exclusions, conditional only on the remaining endpoint. -/
theorem terminal_alternatives_with_diagram_of_no_four
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent) :
    TerminalComponentAlternatives T Mc K ∧ Classification.Sieve.ComponentModelDiagram T K :=
  Classification.Sieve.terminal_alternatives_with_diagram_of_component_models
    hG T hempty hM hunique hmany hcard e hab hsolv
    (source_all_component_models_of_no_four hG T hempty hM hunique hmany hcard e hab hsolv hm)
    K hKM hK

/-- The literal residual factorization retains only the normal PSL₂(4) exclusion. -/
theorem terminal_residual_structure_of_no_four :
    solvableResidual Mc = pResidual 2 Mc ∧
      (Mc : Set G) = ((solvableResidual Mc).map Mc.subtype : Set G) *
        ((T : Subgroup G) : Set G) :=
  terminal_residual_structure_of_component_models
    hG T hempty hM hunique hmany hcard e hab hsolv
    (source_all_component_models_of_no_four hG T hempty hM hunique hmany hcard e hab hsolv hm)

/-- The full component sum on the literal U/Z, conditional only on
excluding the relatively normal PSL₂(4) endpoint. -/
theorem source_canonical_component_sum_of_no_four :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    let _ : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc) :=
      h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
    let U := conjugateSpanBy (localModule T M) Mc
    let Z := centralInvolutions T
    ∃ ρ : Representation (ZMod 2) Mc (Additive (U ⧸ Z.subgroupOf U)),
      ∃ c : BinaryConjugationSection Mc U Z ρ,
        (⨆ K : {K : Subgroup Mc // K.IsCComponent},
          c.imageSpace ⁅U, K.val.map Mc.subtype⁆) ⊔ fixed ρ = ⊤ :=
  source_canonical_component_sum_of_models
    hG T hempty hM hunique hmany hcard e hab hsolv
    (source_all_component_models_of_no_four hG T hempty hM hunique hmany hcard e hab hsolv hm)

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports
