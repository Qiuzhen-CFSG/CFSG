module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoverage
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondarySourceConstruction
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveSourceImages
/-!
# Source construction and sieve applications of radical coverage

The degree-two source constructor now derives R₂≤K from the original natural
module and Q=O₂(KS). Its cubic remains in the original core center and moves
Q, while the checked obstruction to whole-radical torus movement is retained.

The corrected exceptional-model sieve is applied under its literal full
normalQuotientAction, with generation proved by the natural-action calculation.
Model inspection, core centrality and prime exclusions remain the independent
sieve owner's inputs. The construction of MSData and the remaining source
geometry, corrected unitary marking and terminal representation arguments are
still owned by `qt-d-1222-rankone-uniqueness-nonblock`.
This does not assert the complete nonblock contradiction.

Source: Aschbacher--Smith, original 4.3.10--16 and conclusion of 4.3.2,
printed pp.617--619.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

/-- The degree-two source construction no longer assumes R₂≤K. The upper-bound
calculation supplies that assertion from the original natural module. -/
theorem MSData.exists_secondarySourceData_two_of_geometry
    (d : MSData c 2) (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier)
    (B : Subgroup (rootNormalizer c)) (hB : B.IsCComponent) (hBn : B.Normal)
    (hBq : IsQuasisimple (B ⧸ pCore 2 B))
    (hsec : secondary c ≤ B.map (rootNormalizer c).subtype)
    (hcore : (K c ⊔ S c).pCoreIn 2 = Q c)
    (henlarged : (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c)
    (hnorm : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G))
    (henlarges : secondary c < (B.map (rootNormalizer c).subtype).pCoreIn 2 ⊔ secondary c) :
    ∃ s : SecondarySourceData c 2, s.component = B ∧
      s.torus ≤ (K c).coreCenterIn 2 ∧ s.torus ≤ K c ∧
      Q c ⊓ Subgroup.centralizer (s.torus : Set G) = ⊥ ∧
      Q c ⊔ ⁅R₂ c, s.torus⁆ ≠ R₂ c := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  exact d.exists_secondarySourceData_two_of_marked_parabolic D hL hSL B hB hBn hBq hsec
    hcore (m.radical_le_original (by decide) D hcore) henlarged hnorm henlarges

namespace SecondarySourceData
open EndgameSieve
variable {n : ℕ}
/-- Apply the existing source sieve after discharging its whole-radical generation
premise under the same literal action. Model inspection and the remaining row
exclusions are the independent sieve owner's inputs; construction of MSData,
source geometry and the terminal representations remain with this owner. -/
theorem exceptional_of_model_inputs (s : SecondarySourceData c n)
    (d : MSData c n) (m : RootCoordinates d) (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hm : NonexceptionalModel (s.component ⧸ pCore 2 s.component) n ∨
      (ExceptionalModel (s.component ⧸ pCore 2 s.component) n ∧
        (s.torus.subgroupOf (rootNormalizer c)).map s.action ⊓
          MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥))
    (hc : NonexceptionalModel (s.component ⧸ pCore 2 s.component) n →
      (((secondary c).pCoreIn 2).subgroupOf (rootNormalizer c)).map s.action ≤
        centralizer (((secondary c).subgroupOf (rootNormalizer c)).map s.action : Set _))
    (he : NonexceptionalModel (s.component ⧸ pCore 2 s.component) n →
      ∀ p : ℕ, p.Prime → Odd p → p ∣ 2 ^ n - 1 →
      ∀ a ∈ (s.torus.subgroupOf (rootNormalizer c)).map s.action,
        a ∈ centralizer (((secondary c).subgroupOf (rootNormalizer c)).map s.action : Set _) →
          orderOf a ≠ p) :
    ExceptionalModel (s.component ⧸ pCore 2 s.component) n ∧
      (s.torus.subgroupOf (rootNormalizer c)).map s.action ⊓
        MulAut.innerSubgroup (s.component ⧸ pCore 2 s.component) = ⊥ := by
  let := s.normal
  exact SourceImages.exceptional_of_source_inputs c s.component hn s.torus
    (s.secondary_le.trans (map_subtype_le _)) s.radical_le s.torus_le s.radical_normalizer
    s.torus_card s.torus_secondary s.core_moved (m.source_action_generation hn D s)
    s.radical_action hm hc he
end SecondarySourceData
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
