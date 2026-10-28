module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.NumericalGeometry
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.AlternatingSixActionDefs
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.AlternatingSixSieve

/-!
# Applying the A₆ diagram exclusion to the terminal component

The actual component lies outside M. The proved parabolic exclusion therefore
contradicts its A₆ image once its radical is the two-core and the original
Sylow action is natural. In the small-actor branch, original 14.3.12 already
supplies that kernel equality; subnormality restricts it to the component.
The last theorem leaves the radical comparison only in the larger-actor branch.

The natural-action recovery (including G.11.2(10)'s tensor action) and the
larger-actor radical comparison remain explicit source obligations. These
conditional consumers do not assert the complete A₆ branch of 14.3.15.
Source: Aschbacher--Smith 14.3.6(2),14.3.12--15, printed pp.991--994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Restricted subnormal two-core control discharges the radical comparison. -/
theorem ComponentLift.radical_eq_twoCore_of_terminal_kernel
    {T : Sylow 2 G} {V : Subgroup G} {F : InvariantFlag T V 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (hsmall : SmallImageRow F K)
    (hk : F.terminalHatAction.ker = pCore 2 F.H) : solvableRadical K = pCore 2 K := by
  have hr := hK.terminal_kernel_eq_radical hsmall
  rw [ker_subgroupMap,QuotientGroup.ker_mk',hk] at hr
  change (pCore 2 F.H).comap (K.subgroupOf F.H).subtype = _ at hr
  rw [← pCore_subnormal_eq_comap 2 hK.component.subnormal] at hr
  let e := subgroupOfEquivOfLe hK.le_pointNormalizer
  have he := congrArg (Subgroup.map e.toMonoidHom) hr
  rw [pCore_map_iso,map_solvableRadical_equiv] at he
  exact he.symm

/-- Actual terminal A₆ exclusion once its two independent source inputs are supplied.
The action condition permits the natural outer transpositions of G.11.2(10). -/
theorem source_terminal_a6_false_of_radical_and_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    {F : InvariantFlag T (rankTwoSeed T M) 2} {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    (hR : solvableRadical K = pCore 2 K) (hA : hK.AlternatingSixNaturalAction e6) : False := by
  apply hK.not_le hM.1.2 e
  exact source_normalized_a6_le_of_natural_action hG T hempty hM hu hmany hcard e hnot
    K hK.local_component hA.normalizes (hK.alternatingSixMap e6)
    (hK.alternatingSixMap_surjective e6) ((hK.alternatingSixMap_ker e6).trans hR)
    (hK.alternatingSixAction e6 hA.normalizes)
    (hK.alternatingSixAction_equivariant e6 hA.normalizes) hA.natural_action

/-- In the small-actor branch original 14.3.12 supplies the entire kernel
comparison. Only the source recovery of the natural A₆ action remains. -/
theorem source_terminal_a6_false_of_small_actor_and_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hm : Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1)
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    (hA : hK.AlternatingSixNaturalAction e6) : False := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let d := Recognition.rankTwo_closure_geometry h F hne
  have hk := (Recognition.rankTwo_small_actor_geometry h F g d hne hgP hgH hyp hm).2.2.2.2
  exact source_terminal_a6_false_of_radical_and_action hG T hempty hM hu hmany hcard e hnot
    hK e6 (hK.radical_eq_twoCore_of_terminal_kernel (Or.inr ⟨e6⟩) hk) hA


/-- Assembly leaves the radical comparison only in the complementary larger-actor
branch. Both source inputs retain the same K, quotient map and Sylow action. -/
theorem source_terminal_a6_false_of_action_and_large_radical
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (g : G)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    {K : Subgroup G} (hK : ComponentLift F g K)
    (e6 : F.terminalDot K ≃* alternatingGroup (Fin 6))
    (hA : hK.AlternatingSixNaturalAction e6)
    (hlarge : ¬ (Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1) →
      solvableRadical K = pCore 2 K) : False := by
  by_cases hm : Module.finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤
      Module.finrank (ZMod 2) (Additive F.Uhat) / 2 - 1
  · exact source_terminal_a6_false_of_small_actor_and_action hG T hempty hM hu hmany hcard e hnot
      F hne g hgP hgH hyp hm hK e6 hA
  · exact source_terminal_a6_false_of_radical_and_action hG T hempty hM hu hmany hcard e hnot
      hK e6 (hlarge hm) hA

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
