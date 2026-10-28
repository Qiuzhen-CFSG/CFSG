module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.SourcePair
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# The A₅–Suzuki source pair for the full known-simple catalogue

The proved Theorems A and C and the completed covering calculations discharge
A.3.6 in the source-pair construction. The only remaining classification input
to component uniqueness is exclusion of the actual mixed A₅–Suzuki F.1.1 pair.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.6,
5.2.2–6, and 13.6.27.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open ChapterF.Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The genuine source pair for each additional component, with A.3.6
supplied by the proved full known-simple catalogue. -/
theorem centralizer_other_component_F11_knownSimple
    {z : G} (hz : zpowers z = V₁)
    {K D : Subgroup (centralizer ({z} : Set G))}
    (hK : K.IsCComponent) [K.Normal]
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))) K)
    (hD : D.IsCComponent) (hne : D ≠ K) (hthree : Nat.Coprime 3 (Nat.card D))
    (hout : ¬ D.map (centralizer ({z} : Set G)).subtype ≤ normalizer (L : Set G))
    (h25 : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J →
      J ≤ normalizer (L : Set G)) :
    let A := D.map (centralizer ({z} : Set G)).subtype
    (∃ m : ℕ, 1 ≤ m ∧
      Nonempty ((A ⧸ pCore 2 A) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) ∧
      HypothesisF11 ![L,A] (T : Subgroup G) ∧
      borel L (T : Subgroup G) ≤ normalizer
        ((pResidual 2 (A ⊔ (T : Subgroup G) : Subgroup G)).map
          (A ⊔ (T : Subgroup G)).subtype : Set G) :=
  centralizer_other_component_F11 d
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    hz hK hc hD hne hthree hout h25

/-- The component-uniqueness application with the known-simple classification
inputs discharged. The mixed rank-two pair exclusion remains explicit. -/
theorem component_unique_of_no_suzuki_pair_knownSimple
    {z : G} (hz : zpowers z = V₁)
    {K : Subgroup (centralizer ({z} : Set G))}
    (hK : K.IsCComponent) [K.Normal]
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer ({z} : Set G))) K)
    (hthree : ∀ D : Subgroup (centralizer ({z} : Set G)),
      D.IsCComponent → D ≠ K → Nat.Coprime 3 (Nat.card D))
    (hout : ∀ D : Subgroup (centralizer ({z} : Set G)),
      D.IsCComponent → ¬ D.map (centralizer ({z} : Set G)).subtype ≤ normalizer (L : Set G))
    (h25 : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J →
      J ≤ normalizer (L : Set G))
    (hExclude : ∀ A : Subgroup G, ∀ m : ℕ, 1 ≤ m →
      Nonempty ((A ⧸ pCore 2 A) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
      ¬ HypothesisF11 ![L,A] (T : Subgroup G)) :
    ∀ D : Subgroup (centralizer ({z} : Set G)), D.IsCComponent → D = K :=
  component_unique_of_no_suzuki_pair d
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    hz hK hc hthree hout h25 hExclude

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
