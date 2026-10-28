module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.ParabolicPlacement.FixedPairPlacement.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.NormalBaumann.Source

/-!
# Moving blocks from failure of the two original fixed-pair alternatives

Both the first seed's centralizer and the second member's normalizer
contain the original Sylow subgroup. In a minimal parabolic, if both are
proper they lie in its unique maximal Sylow overgroup, so their join is
proper. The proved fixed-pair solvable theorem then supplies a moving A₃
block, for the same transported pair and the literal canonical module.

Source: Aschbacher--Smith, C.1.26 and 15.1.22(*), pp.132,1098--1099.
The full residual orbit and its restriction to P remain separate steps.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterB ChapterC.GlaubermanNiles ChapterC.RankOne.ChiProduct
open Section03 Section03.InitialSource ChapterA.Section05To06
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- Unique maximality turns failure of both alternatives into fixed-pair escape. -/
theorem fixed_pair_control_ne_top
    (R : Sylow 2 G) (hP : IsMinimalParabolicOver R ⊤)
    (D : CharacteristicPair (baumann (R : Subgroup G)))
    (hc : ¬ FixedPair.firstSeed R D ≤ center G)
    (hn : ¬ (D.second.map (baumann (R : Subgroup G)).subtype).Normal) :
    FixedPairSolvable.control R D ≠ ⊤ := by
  let C := centralizer (FixedPair.firstSeed R D : Set G)
  let N := normalizer (D.second.map (baumann (R : Subgroup G)).subtype : Set G)
  have hRC : (R : Subgroup G) ≤ C := by
    intro r hr z hz
    exact (((mem_omegaOneCenterAmbient_iff _ z).mp hz.1).2.2 r hr).symm
  have hRN : (R : Subgroup G) ≤ N := by
    let := D.second_characteristic
    exact ((R : Subgroup G).le_normalizer.trans
      (normalizer_le_normalizer_baumann _)).trans
        (normalizer_le_normalizer_characteristic_image _ D.second)
  have hC : C ≠ ⊤ := fun he => hc (centralizer_eq_top_iff_subset.mp he)
  have hN : N ≠ ⊤ := fun he => hn (normalizer_eq_top_iff.mp he)
  have hm := minimalParabolicMax_spec R hP
  have hCM : C ≤ minimalParabolicMax R hP :=
    hP.1.le_maximal ⟨hm.2,hm.1.covBy_top⟩ hRC (lt_top_iff_ne_top.mpr hC)
  have hNM : N ≤ minimalParabolicMax R hP :=
    hP.1.le_maximal ⟨hm.2,hm.1.covBy_top⟩ hRN (lt_top_iff_ne_top.mpr hN)
  intro he
  have hle : FixedPairSolvable.control R D ≤ minimalParabolicMax R hP := sup_le hCM hNM
  rw [he] at hle
  exact hm.1.ne_top (top_unique hle)

/-- The actual same-pair moving block in P₀. Its hypotheses do not exclude
all characteristic normal subgroups of the Sylow subgroup. -/
theorem IsSourceParabolic.moving_block_of_no_pair_alternative
    {d : CaseIComponentData T M Mc V} {P : Subgroup G} (hP : d.IsSourceParabolic P)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : PreparedChosenModule T M V)
    (R : Sylow 2 (d.parabolicClosure P))
    (hR : (R : Subgroup (d.parabolicClosure P)).map (d.parabolicClosure P).subtype = d.S)
    (hB : baumann d.S = baumann (T : Subgroup G))
    (D : CharacteristicPair (baumann (T : Subgroup G))) (hD : D.Universal.{u,u})
    (hi : ParabolicClosureStructure (d.parabolicClosure P) R)
    (hc : ¬ FixedPair.firstSeed R (d.localPair D (d.parabolicClosure P) R hR hB) ≤
      center (d.parabolicClosure P))
    (hn : ¬ ((d.localPair D (d.parabolicClosure P) R hR hB).second.map
      (baumann (R : Subgroup (d.parabolicClosure P))).subtype).Normal) :
    HasMovingAThreeBlock (d.parabolicClosure P) R := by
  let := hi.solvable
  exact FixedPairSolvable.NormalBaumann.minimal_parabolic_moving_alternatingThree_of_fixed_pair_escape
    R hi.minimal hi.fitting (d.localPair D (d.parabolicClosure P) R hR hB)
    (d.localPair_universal D hD _ R hR hB)
    (fixed_pair_control_ne_top R hi.minimal _ hc hn)
    ((hP.closure_sqtk hG h).stronglyQuasithin 3 Nat.prime_three (by decide))
    inferInstance

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
