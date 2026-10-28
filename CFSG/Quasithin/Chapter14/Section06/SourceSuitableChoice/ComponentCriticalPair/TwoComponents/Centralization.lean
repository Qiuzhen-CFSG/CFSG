module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.CriticalActions
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.Containment
public import Theory.GroupTheory.PCoreInRestriction
/-!
# The opposite component centralizes the actual critical actor image

Placing the point in one support puts the cross-centralizing component in
the conjugate terminal group. That group normalizes the critical module.
If the actor normalizes the component, their commutator is a normal
two-subgroup of that component and hence lies in the original two-core.

This proves the centralization used before the actor-rank bound in original
14.6.24(3), printed p.1040. The component-support placement and the actor
normalization remain explicit and must be supplied by the preceding argument.
-/

public section
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
open Subgroup Theory.GroupTheory Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]

/-- An opposite component which normalizes the critical module commutes
with its actor modulo the original core. Both normalizations are literal;
normality of a component in the ambient simple group is not used. -/
theorem critical_actor_commutator_le_core
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH]
    (i : h.CriticalEndpoint) (B : Subgroup G) (hBH : B ≤ D.H)
    (hB : (B.subgroupOf D.H).IsCComponent)
    (hBi : B ≤ i.conjugate D.H)
    (hiB : i.conjugate D.UH ≤ normalizer (B : Set G)) :
    ⁅i.conjugate D.UH,B⁆ ≤ D.QH := by
  let Ug := i.conjugate D.UH
  have hBUg : B ≤ normalizer (Ug : Set G) := by
    have hn := map_mono (f := (MulAut.conj i.representative).toMonoidHom)
      (le_normalizer_conjugateSpanBy D.Vplus D.H)
    rw [map_equiv_normalizer_eq] at hn
    exact hBi.trans hn
  let : IsElementaryAbelian 2 Ug := IsElementaryAbelian.map _
  have hcU : ⁅Ug,B⁆ ≤ Ug := le_normalizer_iff_commutator_le_left.mp hBUg
  have hcB : ⁅Ug,B⁆ ≤ B := le_normalizer_iff_commutator_le_right.mp hiB
  have hc : ⁅Ug,B⁆ ≤ B.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((IsElementaryAbelian.isPGroup 2 Ug).to_le hcU) hcB
      (normalizer_commutator_ge_right Ug B)
  have hp := map_mono (f := D.H.subtype) (pCoreIn_le_of_subnormal 2 hB.subnormal)
  rw [pCoreIn_subgroupOf 2 B D.H hBH,
    map_subgroupOf_eq_of_le ((pCoreIn_le 2 B).trans hBH)] at hp
  exact hc.trans hp

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- The placed critical point puts the opposite component in Mc^g; its
actual star image then centralizes the critical actor. This is the input
to the rank-two centralizer bound on printed p.1040. -/
theorem source_actor_commutator_le_core_of_point_support
    (K Kplus : Subgroup G)
    (i : (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab).CriticalEndpoint)
    (hiKplus : i.conjugate (conjugateSpanBy (localModule T M) Mc) ≤ normalizer (Kplus : Set G))
    (hpoint : i.conjugate (centralInvolutions T) ≤ ⁅conjugateSpanBy (localModule T M) Mc,K⁆)
    (hKplusM : Kplus ≤ Mc) (hKplus : (Kplus.subgroupOf Mc).IsCComponent)
    (hcross : ⁅⁅conjugateSpanBy (localModule T M) Mc,K⁆,Kplus⁆ = ⊥) :
    ⁅i.conjugate (conjugateSpanBy (localModule T M) Mc),Kplus⁆ ≤ Mc.pCoreIn 2 := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,Mc⟩
  let h : D.Hypothesis := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let : IsElementaryAbelian 2 D.UH :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBH : Kplus ≤ i.conjugate Mc :=
    le_conjugate_of_point_support Mc (centralInvolutions T) _ Kplus hMc
      i.representative hpoint
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcross))
  exact critical_actor_commutator_le_core h i Kplus hKplusM hKplus hBH hiKplus
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
