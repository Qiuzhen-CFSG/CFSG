module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters.Generators
public import CFSG.Quasithin.ChapterE.Section03.SourceContainment

/-!
# The solvable 13.6.25 and residual 13.6.26 source applications

The original A₅ setup supplies uniqueness over C_T(V), r=3 and w>1.
The proved solvable clause of E.3.35 puts every solvable member of H(T)
in M. Applying it to the literal residual subgroup joined to T proves
13.6.26(2) without a universal E.3.35 callback. The genuine earlier
A₅ setup, local module parameter and 13.3.8 source input remain explicit.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.6.25(3) and 13.6.26(2), printed pp.933–934.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
open Subgroup
open _root_.CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G]

namespace EarlierA5Setup
variable {T : Sylow 2 G} {L V M MV : Subgroup G} [IsElementaryAbelian 2 V]
    (s : EarlierA5Setup T L V M MV)
include s

/-- Original 13.6.25(3), with the general E.3.35 input discharged. -/
theorem solvable_HOver_le_source (ha : localA V = 1) :
    ∀ H ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable H → H ≤ M := by
  intro H hH hsolv
  let _ := hsolv
  apply SourceContainment.le_of_solvable s.hypothesisE322 (T.subtype hH.2)
    s.unique_over_core_normalizer
  · exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans
      (s.module_normalizer ▸ s.normalizer_le))
  · change (T : Subgroup G) ⊓ centralizer (V : Set G) ≤
      ((T : Subgroup G).subgroupOf H).map H.subtype
    rw [map_subgroupOf_eq_of_le hH.2]
    exact inf_le_left
  · apply lt_min (s.globalW_gt_one ha)
    rw [s.globalR_eq_three]
    norm_num

end EarlierA5Setup

/-- The original residual consumer, preserving its actual prime-to-p convention. -/
theorem source_13_6_26_2_of_solvable_source
    {T : Sylow 2 G} {L V M MV : Subgroup G} [IsElementaryAbelian 2 V]
    (s : EarlierA5Setup T L V M MV) (ha : localA V = 1)
    (h1338 : Earlier1338Two T) (L₁ G₁ : Subgroup G)
    {H : Subgroup G} (hH : H ∈ Chapter13.Section08.Source.Hz L₁ (T : Subgroup G) G₁ M)
    (p : ℕ) [Fact p.Prime] (hp : 3 < p) : O2p H p = Chapter13.Section08.Source.QH H :=
  source_13_6_26_2_of_13_6_25_3 T L L₁ G₁ M s.local_component
    s.local_normalizer h1338 (s.solvable_HOver_le_source ha) hH p hp

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceParameters
