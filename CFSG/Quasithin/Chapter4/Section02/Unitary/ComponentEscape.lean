module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.OrdinaryOrder
public import CFSG.Quasithin.Chapter4.Section02.Unitary.ConstrainedExclusion
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.Normalizer
public import Theory.GroupTheory.CComponent.ContainedGeneralizedFitting
public import Theory.GroupTheory.GeneralizedFitting.PreimageMovement
public import Theory.GroupTheory.CComponent.OddRankNormal
/-!
# An escaping ordinary component in the normalized unitary source

If the preimage of the generalized Fitting subgroup were contained in M,
the original normalized residual would lift to an ambient C-component.
Its centerless unitary quotient has three-rank two, so the ambient
three-rank bound forces normality. The source normalizer equality would
then give H = M, contradicting strictness. Thus an escaping quasisimple
C-component exists. The constrained exclusions and the actual ordinary
catalogue leave a central quotient isomorphic to J₄ or Rudvalis.

Source: Aschbacher–Smith C.2.13, p.148, and A.3.8(3), p.46, specialized
to the original unitary 4.2.12–13 and 4.4.6 configuration. The actual
odd-actor application is in OriginalOddNormalizer.ComponentEscape.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}
local notation "D" => commutator (Atlas.G2.Model (ZMod 2))

/-- The exceptional contained branch of C.2.13 cannot occur for this unitary residual. -/
theorem unitary_generalizedFitting_not_le
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal) (a : L ⧸ pCore 2 L ≃* D)
    (hproper : M < H) :
    ¬ (generalizedFitting (H ⧸ pCore 2 H)).comap
      (QuotientGroup.mk' (pCore 2 H)) ≤ M.subgroupOf H := by
  intro hf
  let A := L.subgroupOf H
  let N := M.subgroupOf H
  have hLH := h.component_le.trans h.local_le
  have hMN : M ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.component_le).mp hn
  have hspan : conjugateSpanBy L M = L := h.normalized_span_eq hMN
  let e : A ≃* L := subgroupOfEquivOfLe hLH
  let eQ : (A ⧸ pCore 2 A) ≃* D :=
    (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans a
  let : IsSimpleGroup D := Atlas.G2.isSimple_commutator_binary
  let : Group.IsPerfect D := by
    rw [Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure]
    exact Atlas.G2.BinaryException.H_isPerfect
  let : IsQuasisimple D := {
    simple := by
      exact ((QuotientGroup.quotientMulEquivOfEq
        Theory.SpecificGroups.g2_derived_two_center_eq_bot).trans
        QuotientGroup.quotientBot).isSimpleGroup }
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv eQ.symm
  let : Group.IsPerfect L := hspan ▸ h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hAN : A ≤ N := comap_mono h.component_le
  have hNA : N ≤ normalizer (A : Set H) := by
    rw [←subgroupOf_normalizer_eq hLH]
    exact comap_mono hMN
  have hQN : pCore 2 H ≤ N := by
    intro x hx
    exact h.radical_le (h.ambient_core_le_radical (mem_map_of_mem H.subtype hx))
  have hcore : A.pCoreIn 2 ≤ pCore 2 H :=
    (pCoreIn_mono_of_normalizes hAN hNA).trans
      (pCoreIn_le_of_generalizedFitting_preimage_le N hf)
  have hU : (⁅pCore 2 A,(⊤ : Subgroup A)⁆).map A.subtype ≤ pCore 2 H :=
    (map_mono (commutator_le_left _ _)).trans hcore
  have hc := isCComponent_of_contained_generalizedFitting A N hAN hNA hQN hU hf
  have hcenter : center D = ⊥ := Theory.SpecificGroups.g2_derived_two_center_eq_bot
  have hcop : Nat.Coprime 3 (Nat.card (center (A ⧸ pCore 2 A))) := by
    rw [Nat.card_congr (centerCongr eQ).toEquiv,hcenter,card_bot]
    decide
  have hr : 2 ≤ primeRank 3 (A ⧸ pCore 2 A) := by
    rw [primeRank_congr 3 eQ]
    exact Atlas.G2.EvenThreeRank.two_le_primeRank_derived
  let : A.Normal := hc.normal_of_coprime_core_center_primeRank
    (by decide : Odd 3) hcop hr (h.sqtk.stronglyQuasithin 3 Nat.prime_three (by decide))
  have hHA : H ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hLH).mp inferInstance
  have he := h.normalizer_span_eq
  rw [hspan,inf_eq_left.mpr hHA] at he
  exact hproper.ne he.symm

open ChapterA.Section02 ClassificationModels

/-- A proper original local pair has an actual escaping J₄ or Rudvalis component. -/
theorem unitary_exists_ordinary_remaining_component
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal) (a : L ⧸ pCore 2 L ≃* D)
    (hproper : M < H) :
    ∃ K : Subgroup H, IsComponent H K ∧ ¬ K ≤ M.subgroupOf H ∧
      ∃ n : SporadicName, (n = .j4 ∨ n = .ru) ∧
        Nonempty (K ⧸ center K ≃* n.Carrier) := by
  obtain ⟨K,hK,hq,hout⟩ := h.outside_component_of_generalizedFitting_escape
    (h.unitary_generalizedFitting_not_le hn a hproper)
  have ho := h.unitary_escaping_component_isComponent hn a K hK hq hout
  exact ⟨K,ho,hout,h.unitary_ordinary_two_sporadic_models a K ho⟩
end CFSG.Quasithin.ChapterC.HypothesisC28
