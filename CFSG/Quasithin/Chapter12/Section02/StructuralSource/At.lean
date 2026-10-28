module

public import CFSG.Quasithin.Chapter12.Section02.StructuralSource
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Definitions

/-!
# The structural source assembly at one ambient group and Sylow subgroup

The multiple-overgroup branch of Theorem D requires 12.2.2 only for the
original G and T. Independent normalization first constructs an Irr⁺ member;
the surviving FSU branches then give invariance, reducedness and TI for every
such member. No assertion about a singleton-overgroup ambient group is needed.

The seven module alternatives and 12.2.13 are separate local implications.
They are retained separately when selecting a module, with exactly its original
two-core quotient and conjugation action. All source inputs remain explicit.
Source: Aschbacher--Smith, 12.2.2--4 and 12.2.13, printed pp.795--799.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The exact structural conclusions, restricted to the same ambient G,T.
This definition asserts no source theorem and assumes no module classification. -/
def Structural1222At (K : GroupClass.{u}) (T : Sylow 2 G) : Prop :=
  ∀ L : Subgroup G, Hypothesis1223 K T L →
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
    Nonempty {V : Subgroup G // Nonempty (ChosenModule T L V)} ∧
    ∀ V : Subgroup G, ChosenModule T L V →
      (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      IsPReduced 2 (V.subgroupOf (L ⊔ (T : Subgroup G))) ∧
      (∀ g ∈ normalizer (L : Set G),
        V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V) ∧
      (normalizer (L : Set G) ≤ normalizer (V : Set G) ∨
        V ⊓ centralizer (L : Set G) = ⊥)

/-- Normalization before any choice of module. -/
def SourceNormalization1222At (K : GroupClass.{u}) (T : Sylow 2 G) : Prop :=
  ∀ L : Subgroup G, Hypothesis1223 K T L →
    (T : Subgroup G) ≤ normalizer (L : Set G)

/-- The surviving FSU branches, on the original chosen subgroups. -/
def SourceBranches1222At (K : GroupClass.{u}) (T : Sylow 2 G) : Prop :=
  ∀ L V : Subgroup G, Hypothesis1223 K T L → ChosenModule T L V →
    normalizer (L : Set G) ≤ normalizer (V : Set G) ∨
    ((T : Subgroup G) ≤ normalizer (V : Set G) ∧ V ⊓ centralizer (L : Set G) = ⊥)

/-- The separate seven-case classification at G,T. -/
def Theorem1222ModulesAt (K : GroupClass.{u}) (T : Sylow 2 G) : Prop :=
  ∀ L V : Subgroup G, Hypothesis1223 K T L →
    (D : ChosenModule T L V) → ModuleAlternatives1222 D

/-- All four recognition alternatives, on the same G,T,L,V. -/
def Theorem12213At (K : GroupClass.{u}) (T : Sylow 2 G) : Prop :=
  ∀ L V : Subgroup G, Hypothesis1223 K T L → ChosenModule T L V →
    Alternatives12213 T L V

/-- Compatibility with the preserved universal structural API. -/
theorem Structural1222.at {K : GroupClass.{u}} (h : Structural1222 K)
    (T : Sylow 2 G) : Structural1222At K T := h G T

/-- The existing guarded module producer specializes without removing its guard. -/
theorem Theorem1222ModulesOfMany.at {K : GroupClass.{u}}
    (h : Theorem1222ModulesOfMany K) (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    Theorem1222ModulesAt K T := fun L V => h G T L V hmany

/-- Compatibility with the preserved universal recognition API. -/
theorem Theorem12213.at {K : GroupClass.{u}} (h : Theorem12213 K)
    (T : Sylow 2 G) : Theorem12213At K T := h G T

/-- Conditional structural assembly at G,T. Existence uses independent
normalization; reducedness and TI are proved from the surviving FSU branches. -/
theorem structural1222At_of_source_branches {T : Sylow 2 G}
    (normalization : SourceNormalization1222At KnownSimple.IsKnownSimple T)
    (branches : SourceBranches1222At KnownSimple.IsKnownSimple T) :
    Structural1222At KnownSimple.IsKnownSimple T := by
  intro L h
  have hn := normalization L h
  obtain ⟨V, hV⟩ := h.toHypothesis1221.exists_chosen_of_normalizes hn
  refine ⟨hn, ⟨⟨V, hV⟩⟩, ?_⟩
  intro W D
  have hb := branches L W h D
  have hTW : (T : Subgroup G) ≤ normalizer (W : Set G) := by
    rcases hb with hM | hW
    · exact hn.trans hM
    · exact hW.1
  have hcases : normalizer (L : Set G) ≤ normalizer (W : Set G) ∨
      W ⊓ centralizer (L : Set G) = ⊥ := hb.imp id And.right
  exact ⟨hTW, D.reduced_of_sylow_normalizes h.toHypothesis1221 hTW,
    D.ti_of_normalizer_or_fixedSpace h.toHypothesis1221 hcases, hcases⟩

/-- Apply producers with the actual multiple-overgroup premise. Neither
producer is required outside that branch of the classification. -/
theorem structural1222At_of_source_branches_of_many {T : Sylow 2 G}
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (normalization : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      SourceNormalization1222At KnownSimple.IsKnownSimple T)
    (branches : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      SourceBranches1222At KnownSimple.IsKnownSimple T) :
    Structural1222At KnownSimple.IsKnownSimple T :=
  structural1222At_of_source_branches (normalization hmany) (branches hmany)

/-- Select a genuine Irr⁺ member and apply both independent classifications
to that same choice. This does not derive either classification from structure. -/
theorem exists_chosen_source_results_at {K : GroupClass.{u}} {T : Sylow 2 G}
    (structural : Structural1222At K T) (modules : Theorem1222ModulesAt K T)
    (recognition : Theorem12213At K T) {L : Subgroup G} (h : Hypothesis1223 K T L) :
    ∃ (V : Subgroup G) (D : ChosenModule T L V),
      ModuleAlternatives1222 D ∧ Alternatives12213 T L V := by
  obtain ⟨V, ⟨D⟩⟩ := (structural L h).2.1
  exact ⟨V, D, modules L V h D, recognition L V h D⟩

end CFSG.Quasithin.Chapter12.Section02
