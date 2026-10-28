module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ActionKernel
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import Stellmacher.BaumannMap
public import Theory.GroupTheory.ElementaryThompsonRelative

/-!
# Baumann and Thompson obstructions for the original escaping join

The exact Sylow action kernel gives Baum(T)=Baum(O₂(X)) as soon as J(T)
is normal in the original join X. Thus X normalizes Baum(T). A nontrivial
characteristic subgroup of Baum(T) normal in LT would then have its full
normalizer in N_G(L), contradicting X's escape. This eliminates alternative
13.2.2(10I) in the proof of 13.4.7(4), with relative normality retained.

The same unique-normalizer argument forces J(T) outside O₂(LT): otherwise
J(T)=J(O₂(LT)) is normal in LT. The linear-case application is supplied in
LinearResidualSource. Neither statement eliminates the block alternative
13.2.2(10II) or asserts the missing J₁ residual movement.
Source: Aschbacher–Smith 13.4.7(4), printed pp.902–903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G]

private theorem baumann_normal_of_thompson_normal
    (S : Sylow 2 G) (U : Subgroup G) (hr : IsPReduced 2 U)
    (hk : (S : Subgroup G) ⊓ centralizer (U : Set G) = pCore 2 G)
    (hn : (elementaryAbelianMaxJ (S : Subgroup G)).Normal) :
    ChapterB.baumann (S : Subgroup G) = ChapterB.baumann (pCore 2 G) ∧
      (ChapterB.baumann (S : Subgroup G)).Normal := by
  let := hr.normal
  let := hr.elementary
  let := hn
  have hJS : elementaryAbelianMaxJ (S : Subgroup G) ≤ (S : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hJQ : elementaryAbelianMaxJ (S : Subgroup G) ≤ pCore 2 G :=
    le_sSup ⟨hn,S.isPGroup'.to_le hJS⟩
  have hJ : ChapterB.thompsonJ (S : Subgroup G) 0 ≤ centralizer (U : Set G) := by
    rw [ChapterB.thompsonJ_zero]
    exact hJQ.trans (le_centralizer_iff.mp hr.le_centralizer_pCore)
  have hh := ChapterB.lemma_B_2_10_centralizing U (S : Subgroup G)
    ((IsElementaryAbelian.isPGroup 2 U).le_sylow_of_normal S)
    (pCore_isPGroup.le_sylow_of_normal S) hk.symm hJ
  exact ⟨hh.2.1,hh.2.2.2⟩

/-- Restrict and transport the source Baumann equality through the actual join. -/
theorem original_pair_baumann_of_thompson_normal
    {T : Sylow 2 G} {L V A B : Subgroup G}
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hn : A ⊔ B ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) :
    ChapterB.baumann (T : Subgroup G) = ChapterB.baumann ((A ⊔ B).pCoreIn 2) ∧
      A ⊔ B ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) := by
  let X := A ⊔ B
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
  let U := W.subgroupOf X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  let S := T.subtype hTX
  have hWX : W ≤ X := conjugateSpanBy_le (fun z hz =>
    hTX ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  obtain ⟨hr,_,_,hk⟩ := original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB
  have hJ : (elementaryAbelianMaxJ (S : Subgroup X)).map X.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective X.subtype X.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX]
  have hJn : (elementaryAbelianMaxJ (S : Subgroup X)).Normal := by
    have hJX : elementaryAbelianMaxJ (T : Subgroup G) ≤ X := by
      rw [←hJ]
      exact map_subtype_le _
    have hh := normal_subgroupOf_of_le_normalizer hn
    rw [←hJ,subgroupOf,comap_map_eq_self_of_injective X.subtype_injective] at hh
    exact hh
  have hker : (S : Subgroup X) ⊓ centralizer (U : Set X) = pCore 2 X := by
    apply map_injective X.subtype_injective
    rw [←map_inf_centralizer_of_injective X.subtype X.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX,map_subgroupOf_eq_of_le hWX]
    exact hk
  obtain ⟨hEq,hNorm⟩ := baumann_normal_of_thompson_normal S U hr hker hJn
  have hB : (ChapterB.baumann (S : Subgroup X)).map X.subtype =
      ChapterB.baumann (T : Subgroup G) := by
    change (((S : Subgroup X) ⊓ centralizer (omegaOneCenterAmbient
      (elementaryAbelianMaxJ (S : Subgroup X)) : Set X)).map X.subtype) = _
    rw [baumann_map_injective X.subtype X.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX]
    rfl
  refine ⟨?_,?_⟩
  · have hh := congrArg (Subgroup.map X.subtype) hEq
    rw [hB] at hh
    change ChapterB.baumann (T : Subgroup G) =
      (((pCore 2 X) ⊓ centralizer (omegaOneCenterAmbient
        (elementaryAbelianMaxJ (pCore 2 X)) : Set X)).map X.subtype) at hh
    rw [baumann_map_injective X.subtype X.subtype_injective] at hh
    exact hh
  · let := hNorm
    have hh := (ChapterB.baumann (S : Subgroup X)).le_normalizer_map X.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,hB] using hh

/-- Source 13.4.7(4) excludes alternative 13.2.2(10I), with characteristicness
inside the actual Baumann subgroup and normality relative to LT. -/
theorem no_characteristic_baumann_normal_of_outside_join
    {T : Sylow 2 G} {L V X : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hout : ¬ X ≤ normalizer (L : Set G))
    (hn : X ≤ normalizer (ChapterB.baumann (T : Subgroup G) : Set G))
    (C : Subgroup (ChapterB.baumann (T : Subgroup G))) [C.Characteristic]
    (hne : C ≠ ⊥) :
    ¬ ((C.map (ChapterB.baumann (T : Subgroup G)).subtype).subgroupOf
      (L ⊔ (T : Subgroup G))).Normal := by
  let S := ChapterB.baumann (T : Subgroup G)
  let E := C.map S.subtype
  have hEX : E ≤ L ⊔ (T : Subgroup G) :=
    (map_subtype_le C).trans (inf_le_left.trans le_sup_right)
  intro hnormal
  have hEn : L ⊔ (T : Subgroup G) ≤ normalizer (E : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hEX).mp hnormal
  have hE : E ≠ ⊥ := fun hz => hne ((map_eq_bot_iff_of_injective _ S.subtype_injective).mp hz)
  have hbound := D.normal_subgroup_normalizer_le h.toHypothesis1221 hEX hE hEn
  exact hout ((hn.trans (normalizer_le_normalizer_characteristic_image S C)).trans hbound)

/-- An outside normalizer of J(T) forces J(T) to move the original LT core
quotient. This excludes the centralizing case before the source trichotomy. -/
theorem thompson_not_le_original_core_of_outside_normalizer
    {T : Sylow 2 G} {L V X : Subgroup G}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hout : ¬ X ≤ normalizer (L : Set G))
    (hn : X ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let H := L ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  intro hJQ
  have hQT : Q ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype (show (T : Subgroup G) ≤ H from le_sup_right))
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)] at hh
    exact hh
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq Q (T : Subgroup G) hQT
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le (T : Subgroup G) Q hJQ
  have horder := le_antisymm hsmall.1 hlarge.1
  have he : J = elementaryAbelianMaxJ Q :=
    le_antisymm (hlarge.2 horder.symm) (hsmall.2 horder)
  have hHJ : H ≤ normalizer (J : Set G) := by
    rw [he]
    exact (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))).trans
        (normalizer_le_normalizer_elementaryAbelianMaxJ Q)
  have hJne : J ≠ ⊥ := by
    intro hz
    obtain ⟨E,hE⟩ := elementaryAbelianMaxSubgroups_nonempty (T : Subgroup G)
    have hEb : E = ⊥ := le_bot_iff.mp ((le_sSup hE : E ≤ J).trans_eq hz)
    have hc := hE.2.2 V D.le_sylow D.elementary
    rw [hEb,card_bot] at hc
    exact D.ne_bot (card_eq_one.mp (le_antisymm hc Nat.card_pos))
  have hbound := D.normal_subgroup_normalizer_le h.toHypothesis1221
    (hJQ.trans (H.pCoreIn_le 2)) hJne hHJ
  exact hout (hn.trans hbound)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
