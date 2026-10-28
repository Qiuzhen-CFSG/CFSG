module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.SplitSeed.FixedSpace
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Coordinates
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.SeedGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.SplitSeed.Placement.Normalizer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.SplitSeed.Placement.FixedControl
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication.SourceInputs

public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Literal placement of the marked cubic seed in U_K

Retain the full standing Hypothesis 13.3.1, the actual A₅ marking and
selected T_v-invariant component, the genuine earlier local conclusions,
and one doubled-natural coordinate system. The two permitted literal
Thompson and Baumann image equalities suffice to prove
[⟨z⟩,L_v] ≤ U_K under hypothetical centrality of K⁺ and L_v⁺.

We prove the stronger impossibility of that central branch. The Thompson
image puts the radical in the component Sylow, which fixes the seed by
centrality. The Baumann image and full-actor Frattini lift make the line
parabolic preserve the seed. FixedControl then makes K centralize it.
But z belongs to ⟨v⟩[⟨z⟩,L_v], K fixes v, and Y_z membership says that
K moves z. This contradiction gives the required ambient containment.

Every normalization and fixed-point comparison uses the original module
and quotient maps. Neither a parabolic-image conclusion nor a split point,
nonzero intersection, containment, or later 13.6.22 marking is assumed.
The full source hypothesis is kept explicitly; the independent earlier
source conclusions and the two permitted image equalities remain inputs.
The split-coordinate assembly remains with SplitSeed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Hypothesis 13.3.1 on p.884, marked local setup on p.926,
13.6.4–5 and 13.6.14 on pp.926–930, and 13.6.20 on p.931.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.SplitSeed.Placement
open ComponentSelection A5Module
variable {G : Type*} [Group G] [Finite G] {K L V : Subgroup G}

private theorem exists_component_sylow (T : Subgroup G) (v : G)
    (S : Sylow 2 (Gv v))
    (hS : (S : Subgroup (Gv v)).map (Gv v).subtype = Tv T v)
    (hK : K ≤ Gv v) (hn : Tv T v ≤ normalizer (K : Set G)) :
    ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype = K ⊓ Tv T v := by
  let N := Gv v ⊓ normalizer (K : Set G)
  have hKN : K ≤ N := le_inf hK K.le_normalizer
  have hSN : (S : Subgroup (Gv v)).map (Gv v).subtype ≤ N := by
    rw [hS]
    exact le_inf inf_le_right hn
  obtain ⟨Q, hQ⟩ := S.exists_map_subtype_eq_of_le (show N ≤ Gv v from inf_le_left) hSN
  obtain ⟨P, hP⟩ := Q.exists_map_subtype_eq_inf_of_normalizes hKN
    (show N ≤ normalizer (K : Set G) from inf_le_right)
  exact ⟨P, by simpa only [hQ, hS, inf_comm] using hP⟩

/-- The literal ambient seed placement in the central branch of 13.6.20.
The earlier hypotheses and the two permitted radical-image equalities
actually rule out the hypothetical centrality, by a fixed-point argument
on W_K before any intersection with U_K. -/
theorem seed_le_UK
    (T : Sylow 2 G) (_standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (s : A5Module.Marking L V)
    [IsElementaryAbelian 2 (Uv (markedZ s) (markedV s))]
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ s) (markedV s))
    (hn : Tv (T : Subgroup G) (markedV s) ≤ normalizer (K : Set G))
    (hL : Tv (T : Subgroup G) (markedV s) ≤ normalizer (Lv L (markedV s) : Set G))
    (hz : Tv (T : Subgroup G) (markedV s) ≤ centralizer ({markedZ s} : Set G))
    (d : DoubledCoordinates K L (T : Subgroup G) (markedZ s) (markedV s) hK.1.1 hL hz)
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))).map (Gv (markedV s)).subtype =
      Tv (T : Subgroup G) (markedV s))
    (h1364 : ChapterB.baumann (T : Subgroup G) =
      ChapterB.baumann (Tv (T : Subgroup G) (markedV s)))
    (h1365 : Gv (markedV s) ⊓ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      Mv (normalizer (L : Set G)) (markedV s))
    (hlocal : Mv (normalizer (L : Set G)) (markedV s) =
      normalizer (V : Set G) ⊓ Gv (markedV s))
    (hc : ⁅plusImage K L (T : Subgroup G) (markedZ s) (markedV s) hL hz K,
      plusImage K L (T : Subgroup G) (markedZ s) (markedV s) hL hz (Lv L (markedV s))⁆ = ⊥)
    (hJ : plusImage K L (T : Subgroup G) (markedZ s) (markedV s) hL hz
      (Stellmacher.elementaryAbelianMaxJ (Tv (T : Subgroup G) (markedV s))) =
      BinaryLinearThree.R.map (modelEmbedding d))
    (hB : plusImage K L (T : Subgroup G) (markedZ s) (markedV s) hL hz
      (ChapterB.baumann (T : Subgroup G)) = BinaryLinearThree.R.map (modelEmbedding d)) :
    (⁅zpowers (markedZ s), Lv L (markedV s)⁆ : Subgroup G) ≤
      UK K L (T : Subgroup G) (markedZ s) (markedV s) := by
  obtain ⟨P, hP⟩ := exists_component_sylow (T : Subgroup G) (markedV s) S hS hK.1.1 hn
  let : IsElementaryAbelian 2 (WK K L (T : Subgroup G) (markedZ s) (markedV s)) :=
    IsElementaryAbelian.of_le (WK_le_Uv K L (T : Subgroup G) _ _ hK.1.1)
  exfalso
  apply seed_not_le_component_centralizer s hK hn
  apply fixed_control hK.1.1 hL hz d P
    (radical_le_component_sylow d S hS P hP hJ) _ (seed_le_WK s)
    (parabolicPreimage_normalizes_seed s hK.1.1 hL hz d S hS h1364 h1365 hlocal hB)
  intro k hk q hq
  have hkt : (k : G) ∈ K ⊓ Tv (T : Subgroup G) (markedV s) := by
    rw [← hP]
    exact mem_map.mpr ⟨k, hk, rfl⟩
  exact mul_inv_eq_iff_eq_mul.mpr
    (mem_centralizer_iff.mp (seed_le_sylow_centralizer hL hz hc hq) k hkt)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.SplitSeed.Placement
