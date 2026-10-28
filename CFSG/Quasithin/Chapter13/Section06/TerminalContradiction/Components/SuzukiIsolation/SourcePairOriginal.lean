module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation.SourcePairKnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.OriginalTerminal

/-!
# The original terminal setup reduces to a mixed pair exclusion

The actual marked A₅ setup supplies the solvable-overgroup bound and escape
of every centralizer component from N(L). The selected component's three-rank
supplies the three-prime order of every other component. Applying the genuine
source-pair construction therefore reduces component uniqueness to exclusion
of an A₅–Suzuki F.1.1 pair, with no additional catalogue or orbit callback.
The final theorem applies this reduction to the literal 13.6.27 conclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 5.2.2–6
and 13.6.25–27. The mixed rank-two pair exclusion remains explicit.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open ChapterF.Source SourceParameters
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- All original-setup inputs to component uniqueness are discharged except
for the genuine mixed A₅–Suzuki pair exclusion. -/
theorem component_unique_of_original_setup_and_no_suzuki_pair
    (s : EarlierA5Setup T L V (normalizer (L : Set G)) (normalizer (V : Set G)))
    (hz : zpowers s.z.val = V₁) (L₁ : Subgroup G)
    (hH : centralizer ({s.z.val} : Set G) ∈ Section08.Source.Hz
      L₁ (T : Subgroup G) (centralizer ({s.z.val} : Set G)) (normalizer (L : Set G)))
    {K : Subgroup (centralizer ({s.z.val} : Set G))}
    (hK : K.IsCComponent) [K.Normal] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer ({s.z.val} : Set G))) K)
    (hExclude : ∀ A : Subgroup G, ∀ m : ℕ, 1 ≤ m →
      Nonempty ((A ⧸ pCore 2 A) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
      ¬ HypothesisF11 ![L,A] (T : Subgroup G)) :
    ∀ D : Subgroup (centralizer ({s.z.val} : Set G)), D.IsCComponent → D = K := by
  have hTC : (T : Subgroup G) ≤ centralizer ({s.z.val} : Set G) :=
    le_sup_right.trans hH.1.2
  have hthree := (ThreeStructure.local_three_exclusions
    (d.hypothesis.qtke.involution_centralizer_sqtk s.marked_order)
    (T.subtype hTC) hK hc).2
  exact component_unique_of_no_suzuki_pair_knownSimple d hz hK hc hthree
    (fun D hD => component_image_not_le_of_original_setup d.hypothesis.qtke s L₁ _ hH D hD)
    (source_13_6_25_knownSimple d.hypothesis.qtke s).2.2.1 hExclude

/-- The actual terminal component conclusion from the mixed-pair exclusion. -/
theorem terminal_component_conclusion_of_original_setup_and_no_suzuki_pair
    (s : EarlierA5Setup T L V (normalizer (L : Set G)) (normalizer (V : Set G)))
    (hz : zpowers s.z.val = V₁) (h1338 : Earlier1338Two T) (L₁ : Subgroup G)
    (hH : centralizer ({s.z.val} : Set G) ∈ Section08.Source.Hz
      L₁ (T : Subgroup G) (centralizer ({s.z.val} : Set G)) (normalizer (L : Set G)))
    {K : Subgroup (centralizer ({s.z.val} : Set G))}
    (hK : K.IsCComponent) [K.Normal] [IsQuasisimple (K ⧸ pCore 2 K)]
    (hc : Candidate ((T : Subgroup G).subgroupOf (centralizer ({s.z.val} : Set G))) K)
    (hExclude : ∀ A : Subgroup G, ∀ m : ℕ, 1 ≤ m →
      Nonempty ((A ⧸ pCore 2 A) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) →
      ¬ HypothesisF11 ![L,A] (T : Subgroup G)) :
    Conclusion ((T : Subgroup G).subgroupOf (centralizer ({s.z.val} : Set G))) :=
  terminal_component_conclusion_of_original_setup d.hypothesis.qtke s h1338 L₁ hH hK hc
    (component_unique_of_original_setup_and_no_suzuki_pair d s hz L₁ hH hK hc hExclude)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
