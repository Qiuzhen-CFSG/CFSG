module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.SplitSeed.FixedSpace
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Coordinates
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.SeedGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.Frattini

/-!
# Normalizer control of the literal marked cubic seed

The actual Baumann image and the Frattini lift in the full plus actor
show that every element of the model line-parabolic preimage in K
normalizes [⟨z⟩,L_v]. A lifted element has the same action on W_K as
the original component element; 13.6.5 and the local normalizer equality
make it preserve V and L_v, hence their commutator. This avoids assuming
that the lift belongs to N_K(Baum(T)).

The seed lies in W_K and is not centralized by K. The latter follows
from the actual marked reconstruction z ∈ ⟨v⟩[⟨z⟩,L_v] and Y_z
membership, with the star-kernel removed on the original module.

These source applications feed the fixed-point argument in Placement.lean,
which combines parabolic normalization, Sylow centralization and doubled
coordinates to prove literal seed containment. That final assembly retains
full Hypothesis 13.3.1.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
local marked module on printed p.926, 13.6.4–5 on p.926,
13.6.14 on pp.929–930 and the proof of 13.6.20 on p.931.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.SplitSeed.Placement
open ComponentSelection A5Module
variable {G : Type*} [Group G] [Finite G] {K L T V : Subgroup G}

omit [Finite G] in
/-- The entire ambient seed is in the conjugate span W_K, before any
intersection with U_K. -/
theorem seed_le_WK (s : A5Module.Marking L V) :
    ⁅zpowers (markedZ s), Lv L (markedV s)⁆ ≤ WK K L T (markedZ s) (markedV s) := by
  apply le_trans ?_ (Vv_le_WK K L T (markedZ s) (markedV s))
  exact (commutator_mono (le_conjugateSpanBy _ _) le_rfl).trans
    (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy _ _))

/-- The marked reconstruction and genuine Y_z moving condition prevent
K from centralizing the entire cubic seed. -/
theorem seed_not_le_component_centralizer
    (s : A5Module.Marking L V)
    [IsElementaryAbelian 2 (Uv (markedZ s) (markedV s))]
    (hK : K ∈ Yz L T (markedZ s) (markedV s))
    (hn : Tv T (markedV s) ≤ normalizer (K : Set G)) :
    ¬ ⁅zpowers (markedZ s), Lv L (markedV s)⁆ ≤ centralizer (K : Set G) := by
  intro hQ
  have hv : zpowers (markedV s) ≤ centralizer (K : Set G) := by
    apply zpowers_le.mpr
    intro k hk
    exact mem_centralizer_singleton_iff.mp (hK.1.1 hk)
  have hz : markedZ s ∈ centralizer (K : Set G) :=
    (sup_le hv hQ) (marked_seed_mem_line_sup_commutator s)
  have hkc : K ≤ centralizer ({markedZ s} : Set G) := by
    intro k hk
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hz k hk)
  have hx := (invariant_component_consequences K L T _ _ hK hn).1
  apply hx.2
  intro a ha
  obtain ⟨k, hk, c, hc, rfl⟩ := starPreimage_starImage_factor _ _ K ha
  exact (centralizer ({markedZ s} : Set G)).mul_mem (hkc hk)
    (centralizer_le (Set.singleton_subset_iff.mpr (z_mem_Uv _ _)) hc.2)

/-- Lift in the full plus actor, then transfer its action back to K.
Only the literal Baumann image is assumed; neither a component-normalizer
image nor seed placement in U_K is an input. -/
theorem parabolicPreimage_normalizes_seed
    (s : A5Module.Marking L V)
    (hK : K ≤ Gv (markedV s))
    (hL : Tv T (markedV s) ≤ normalizer (Lv L (markedV s) : Set G))
    (hz : Tv T (markedV s) ≤ centralizer ({markedZ s} : Set G))
    (d : DoubledCoordinates K L T (markedZ s) (markedV s) hK hL hz)
    (S : Sylow 2 (Gv (markedV s)))
    (hS : (S : Subgroup (Gv (markedV s))).map (Gv (markedV s)).subtype = Tv T (markedV s))
    (h1364 : ChapterB.baumann T = ChapterB.baumann (Tv T (markedV s)))
    (h1365 : Gv (markedV s) ⊓ normalizer (ChapterB.baumann T : Set G) ≤
      Mv (normalizer (L : Set G)) (markedV s))
    (hlocal : Mv (normalizer (L : Set G)) (markedV s) =
      normalizer (V : Set G) ⊓ Gv (markedV s))
    (hB : plusImage K L T (markedZ s) (markedV s) hL hz (ChapterB.baumann T) =
      BinaryLinearThree.R.map (modelEmbedding d)) :
    (Matrix.PSL3Two.lineParabolicSL.comap d.actionMap).map K.subtype ≤
      normalizer ((⁅zpowers (markedZ s), Lv L (markedV s)⁆ : Subgroup G) : Set G) := by
  have hlift := plusActor_baumann_normalizer_image K L T _ _ hK hL hz S hS h1364
  apply le_normalizer_iff.mpr
  intro k hk w hw
  obtain ⟨k, hk, rfl⟩ := hk
  have hm : modelEmbedding d (d.actionMap k) ∈
      normalizer (plusImage K L T (markedZ s) (markedV s) hL hz (ChapterB.baumann T) : Set _) := by
    rw [hB]
    apply (BinaryLinearThree.R.le_normalizer_map (modelEmbedding d))
    exact mem_map.mpr ⟨d.actionMap k, normalizer_radical.symm ▸ hk, rfl⟩
  rw [← hlift, modelEmbedding_actionMap] at hm
  obtain ⟨a, ha, he⟩ := hm
  have haM : (a : G) ∈ Mv (normalizer (L : Set G)) (markedV s) :=
    h1365 ⟨plusActor_le_Gv K L T (markedV s) hK a.property, ha.2⟩
  have haV : (a : G) ∈ normalizer (V : Set G) := (hlocal ▸ haM).1
  have haLv : (a : G) ∈ normalizer (Lv L (markedV s) : Set G) :=
    normalizes_Lv_of_normalizes_L (Mv (normalizer (L : Set G)) (markedV s)) L
      (markedV s) inf_le_left inf_le_right haM
  have han : (a : G) ∈ normalizer ((⁅V, Lv L (markedV s)⁆ : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp haV, mem_normalizer_iff_map_conj_eq.mp haLv]
  rw [local_commutator_eq_seed s] at han
  have hew := congrArg (fun g => (plusAction K L T (markedZ s) (markedV s) hL hz g
    ⟨w, seed_le_WK s hw⟩ : G)) he
  change (a : G) * w * (a : G)⁻¹ = (k : G) * w * (k : G)⁻¹ at hew
  exact hew ▸ (mem_normalizer_iff.mp han w).mp hw

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ParabolicGeometry.SplitSeed.Placement
