module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.Normalizer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.ResidualModule.Product

/-!
# Checked reductions for the L₃(2) central-action branch

The marked A₅ action proves [V,L_v] = [⟨z⟩,L_v]: the cubic and its
square applied to z give both generators of the moved plane. Combining
this with the actual normalizer calculation reduces the desired
noncentrality to the parabolic image and split-point geometry in one
compatible doubled-natural marking of U_K = [W_K,K].

These are conditional reductions, not the completed nonzero plus
commutator or Lemma 13.6.20. The B.5.1/B.5.6 specialization must still
construct the doubled marking under hypothetical centrality and exclude
the single-natural case. The Thompson/Baumann and Frattini argument must
still establish the parabolic image and compatible split-point formula.
Their assembly remains in `CentralAction`; no geometry record is assumed to
exist and no containment result is asserted.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript,
Lemma 13.6.20, printed p.931; the marked local module on p.926.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction
open Subgroup A5Module BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
open A5Module.ResidualCoordinates
open scoped commutatorElement
variable {G : Type*} [Group G] [Finite G] {L V : Subgroup G}

/-- The marked A₅ module identifies [V,L_v] with the commutator of the
single source seed z. Both inclusions use actual ambient subgroups. -/
theorem local_commutator_eq_seed (s : A5Module.Marking L V) :
    ⁅V, Lv L (markedV s)⁆ = ⁅zpowers (markedZ s), Lv L (markedV s)⁆ := by
  apply le_antisymm ?_ (commutator_mono
    (zpowers_le.mpr (map_mem s (Multiplicative.ofAdd z))) le_rfl)
  rw [residual_commutator_eq_moved s]
  have hdiff (g : cubicGroup) : s.map (Multiplicative.ofAdd (act g.val z - z)) ∈
      ⁅zpowers (markedZ s), Lv L (markedV s)⁆ := by
    obtain ⟨l, hl⟩ := residualCubicAction_surjective s g
    have he : residualAction s l = g.val := congrArg Subtype.val hl
    rw [← he, ← residual_commutator_formula, commutator_comm]
    exact commutator_mem_commutator l.property (mem_zpowers (markedZ s))
  have h1 := hdiff ⟨cubic, cubic_mem⟩
  have h2 := hdiff ⟨cubic ^ 2, cubicGroup.pow_mem cubic_mem 2⟩
  change s.map (Multiplicative.ofAdd deltaOne) ∈ _ at h1
  change s.map (Multiplicative.ofAdd deltaTwo) ∈ _ at h2
  rintro x ⟨y, hy, rfl⟩
  change s.map (Multiplicative.ofAdd y.toAdd) ∈ _
  rcases moved_cases y.toAdd hy with he | he | he | he <;> rw [he]
  · exact (map_one s.map) ▸ one_mem _
  · exact h1
  · exact h2
  · rw [ofAdd_add, map_mul]
    exact mul_mem h1 h2

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction
open Subgroup ComponentSelection A5Module Representation BinaryLinearThree.DoubledParabolic
variable {G : Type*} [_root_.Group G] [Finite G] {L V : Subgroup G}

/-- Apply the terminal obstruction using the source seed commutator.
The chosen marking must still be constructed with the two displayed
geometric properties; neither is an assumption of the desired source theorem. -/
theorem false_of_marked_seed_geometry
    (s : A5Module.Marking L V) (K T : Subgroup G)
    (hK : K ≤ Gv (markedV s))
    (hL : Tv T (markedV s) ≤ normalizer (Lv L (markedV s) : Set G))
    (hz : Tv T (markedV s) ≤ centralizer ({markedZ s} : Set G))
    (d : DoubledCoordinates K L T (markedZ s) (markedV s) hK hL hz)
    (h1365 : Gv (markedV s) ⊓ normalizer (ChapterB.baumann T : Set G) ≤
      Mv (normalizer (L : Set G)) (markedV s))
    (hlocal : Mv (normalizer (L : Set G)) (markedV s) =
      normalizer (V : Set G) ⊓ Gv (markedV s))
    (himage : (d.actionMap.comp
      (inclusion (show componentNormalizer K T ≤ K from inf_le_left))).range =
        Matrix.PSL3Two.lineParabolicSL)
    (x y : BinaryLinearThree.Vector) (hx : x 2 = 0) (hn : x ≠ 0)
    (hQ : ((⁅zpowers (markedZ s), Lv L (markedV s)⁆ : Subgroup G).subgroupOf
      (UK K L T (markedZ s) (markedV s))).map d.moduleEquiv.toMonoidHom =
        (splitPlane x y).toAddSubgroup.toSubgroup) : False := by
  apply false_of_componentNormalizer_geometry K L V T (markedZ s) (markedV s)
    hK hL hz d h1365 hlocal himage x y hx hn
  rwa [local_commutator_eq_seed s]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction
