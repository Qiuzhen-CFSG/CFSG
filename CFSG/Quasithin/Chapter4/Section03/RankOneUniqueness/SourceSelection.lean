module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Configuration
public import Theory.GroupTheory.PCoreRestriction

/-!
# The intermediate subgroup and crossing choice in original 4.3.2

The maximal two-signalizer description of O₂(LT) controls the core of
every intermediate subgroup above L. This gives I = L O₂(I), the radical
intersection identities, and the conditional choice of the crossing element
inside O₂(LT). The outside subgroup must be selected compatibly with I;
these lemmas do not replace that simultaneous choice.

Source: Aschbacher–Smith, 4.3.2–5, printed pp.613–614.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem normalizes_core (A : Subgroup G) : A ≤ normalizer (A.pCoreIn 2 : Set G) :=
  A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))

/-- The original local core contains the core of every intermediate subgroup above L. -/
theorem intermediate_core_le (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {I : Subgroup G} (hLI : L ≤ I) (hI : I ≤ L ⊔ (T : Subgroup G)) :
    I.pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let A := L ⊔ (T : Subgroup G)
  let Q := A.pCoreIn 2
  have hp := (source_hypothesis411 h (unique_sylow_join D h)).plus_perfect
  have hm := ChapterA.Section04.normal_sylow_core_isMaximal L A le_sup_left
    (sup_le L.le_normalizer D.sylow_normalizes_component) hp (T.subtype le_sup_right)
  have hTA : (T : Subgroup G) ≤ A := le_sup_right
  have he : ((T.subtype hTA : Sylow 2 A) : Subgroup A).map A.subtype =
      (T : Subgroup G) := map_subgroupOf_eq_of_le hTA
  rw [he] at hm
  have hqn : I.pCoreIn 2 ≤ normalizer (Q : Set G) :=
    (pCoreIn_le 2 I).trans (hI.trans (normalizes_core A))
  have hjoin : ChapterA.Section04.IsTwoSignalizer L A (Q ⊔ I.pCoreIn 2) := by
    apply (ChapterA.Section04.isTwoSignalizer_iff _ _ _).mpr
    refine ⟨sup_le (pCoreIn_le 2 A) ((pCoreIn_le 2 I).trans hI),
      (isPGroup_pCoreIn 2 A).to_sup_of_normal_left' (isPGroup_pCoreIn 2 I) hqn, ?_⟩
    exact (le_inf (le_sup_left.trans (normalizes_core A))
      (hLI.trans (normalizes_core I))).trans
        (normalizer_inf_normalizer_le_normalizer_sup Q (I.pCoreIn 2))
  exact le_sup_right.trans (((ChapterA.Section04.isMaximalTwoSignalizer_iff _ _ _).mp hm).2
    _ hjoin le_sup_left)

/-- Both identities stated immediately after the choice of I in original 4.3.2. -/
theorem intermediate_core_identities (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {I : Subgroup G} (hLI : L ≤ I)
    (hI : I ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    I = L ⊔ I.pCoreIn 2 ∧
      I.pCoreIn 2 = I ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let A := L ⊔ (T : Subgroup G)
  let Q := A.pCoreIn 2
  have hIA : I ≤ A := hI.trans (sup_le le_sup_left (pCoreIn_le 2 A))
  have hc : I.pCoreIn 2 = I ⊓ Q := le_antisymm
    (le_inf (pCoreIn_le 2 I) (intermediate_core_le D h hLI hIA))
    (inf_pCoreIn_le_of_le 2 hIA)
  refine ⟨le_antisymm ?_ (sup_le hLI (pCoreIn_le 2 I)),hc⟩
  intro x hx
  have hxprod : x ∈ (L : Set G) * (Q : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right L Q (le_sup_left.trans (normalizes_core A))]
    exact hI hx
  obtain ⟨l,hl,q,hq,he⟩ := hxprod
  have hqI : q ∈ I := by
    have hm := I.mul_mem (I.inv_mem (hLI hl)) hx
    rw [← he, inv_mul_cancel_left] at hm
    exact hm
  rw [← he]
  exact mul_mem_sup hl (hc.ge ⟨hqI,hq⟩)

/-- Select a maximal intermediate subgroup before making any outside choice. -/
theorem exists_maximal_intermediate (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hnot : ¬ UniqueMaximalOvergroup L (normalizer (L : Set G))) :
    ∃ I : Subgroup G, L ≤ I ∧ I ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      ¬ UniqueMaximalOvergroup I (normalizer (L : Set G)) ∧
      (∀ J : Subgroup G, I < J → J ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
        UniqueMaximalOvergroup J (normalizer (L : Set G))) ∧
      I = L ⊔ I.pCoreIn 2 ∧
      I.pCoreIn 2 = I ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  classical
  let s : Set (Subgroup G) := {I | L ≤ I ∧ I ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
    ¬ UniqueMaximalOvergroup I (normalizer (L : Set G))}
  obtain ⟨I,hI,hmax⟩ := Set.exists_max_image s (fun I => Nat.card I)
    s.toFinite ⟨L,le_rfl,le_sup_left,hnot⟩
  refine ⟨I,hI.1,hI.2.1,hI.2.2,?_,intermediate_core_identities D h hI.1 hI.2.1⟩
  intro J hIJ hJ
  by_contra hn
  exact hIJ.ne (eq_of_le_of_card_ge hIJ.le (hmax J ⟨hI.1.trans hIJ.le,hJ,hn⟩))

/-- Maximality of the same I gives original 4.3.4 once H has been aligned. -/
theorem selected_core_sylow (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {I H : Subgroup G} (hLI : L ≤ I)
    (hI : I ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hmax : ∀ J : Subgroup G, I < J → J ≤ L ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 →
      UniqueMaximalOvergroup J (normalizer (L : Set G)))
    (hH : IsMaximalTwoLocal H) (hIH : I ≤ H) (hout : ¬ H ≤ normalizer (L : Set G)) :
    I.pCoreIn 2 = ((T : Subgroup G) ⊓ H) ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      I.pCoreIn 2 = (I ⊔ ((T : Subgroup G) ⊓ H)).pCoreIn 2 := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let S := (T : Subgroup G) ⊓ H
  obtain ⟨he,hc⟩ := intermediate_core_identities D h hLI hI
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hRS : I.pCoreIn 2 ≤ S ⊓ Q := le_inf
    (le_inf ((hc.le.trans inf_le_right).trans hQT) ((pCoreIn_le 2 I).trans hIH))
    (hc.le.trans inf_le_right)
  have hIJ : I ≤ L ⊔ (S ⊓ Q) := by
    rw [he]
    exact sup_le_sup_left hRS L
  have hJI : L ⊔ (S ⊓ Q) ≤ I := by
    by_contra hn
    have hu := hmax _ (lt_of_le_not_ge hIJ hn) (sup_le_sup_left inf_le_right L)
    exact hout ((hu.2.2 H hH (sup_le (hLI.trans hIH) (inf_le_left.trans inf_le_right))).le)
  have hQR : S ⊓ Q ≤ I.pCoreIn 2 := by
    rw [hc]
    exact le_inf (le_sup_right.trans hJI) inf_le_right
  have hcore : I.pCoreIn 2 = S ⊓ Q := le_antisymm hRS hQR
  refine ⟨hcore,le_antisymm ?_ ?_⟩
  · have hSn : S ≤ normalizer (I.pCoreIn 2 : Set G) := by
      rw [hcore]
      exact (le_inf S.le_normalizer
        (inf_le_left.trans (le_sup_right.trans (normalizes_core (L ⊔ (T : Subgroup G)))))).trans
          inf_normalizer_le_normalizer_inf
    exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I)
      ((pCoreIn_le 2 I).trans le_sup_left) (sup_le (normalizes_core I) hSn)
  · have hJH : I ⊔ S ≤ H := sup_le hIH inf_le_right
    have hJA : I ⊔ S ≤ L ⊔ (T : Subgroup G) :=
      sup_le (hI.trans (sup_le le_sup_left (pCoreIn_le 2 _))) (inf_le_left.trans le_sup_right)
    have hb := intermediate_core_le D h (hLI.trans le_sup_left) hJA
    rw [hcore]
    exact le_inf (le_inf (hb.trans hQT) ((pCoreIn_le 2 _).trans hJH)) hb

/-- The source crossing element may be chosen in Q when R is proper in Q. -/
theorem exists_source_crossing_in_core {S Q R : Subgroup G}
    (hST : S < (T : Subgroup G)) (hQT : Q ≤ (T : Subgroup G))
    (hTQ : (T : Subgroup G) ≤ normalizer (Q : Set G)) (hR : R = S ⊓ Q) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ S ∧
      t ∈ normalizer (S : Set G) ∧ t ^ 2 ∈ S ∧
      (R < Q → t ∈ Q ∧ t ^ 2 ∈ R) := by
  by_cases hlt : R < Q
  · have hSQ : S < S ⊔ Q := by
      apply lt_of_le_not_ge le_sup_left
      intro hh
      have hQS : Q ≤ S := le_sup_right.trans hh
      exact hlt.ne (hR.trans (inf_eq_right.mpr hQS))
    obtain ⟨x,hx,hout,hn,hsq⟩ := exists_outside_normalizer_square_mem S (S ⊔ Q)
      (T.isPGroup'.to_le (sup_le hST.le hQT)) hSQ
    have hxprod : x ∈ (S : Set G) * (Q : Set G) := by
      rw [← coe_mul_of_left_le_normalizer_right S Q (hST.le.trans hTQ)]
      exact hx
    obtain ⟨s,hs,q,hq,he⟩ := hxprod
    have hqeq : q = s⁻¹ * x := by rw [← he]; simp
    have hqn : q ∈ normalizer (S : Set G) := by
      rw [hqeq]
      exact mul_mem (inv_mem (S.le_normalizer hs)) hn
    have hqout : q ∉ S := fun hqS => hout (he ▸ S.mul_mem hs hqS)
    have hq2 : q ^ 2 ∈ S := by
      rw [hqeq,pow_two]
      have hc := ((mem_normalizer_iff.mp hn) s⁻¹).mp (S.inv_mem hs)
      have hm := S.mul_mem (S.mul_mem (S.inv_mem hs) hc) hsq
      simpa only [pow_two, mul_assoc, inv_mul_cancel_left] using hm
    refine ⟨q,hQT hq,hqout,hqn,hq2,fun _ => ⟨hq,?_⟩⟩
    rw [hR]
    exact ⟨hq2,Q.pow_mem hq 2⟩
  · obtain ⟨t,ht,ho,hn,hs⟩ := exists_outside_normalizer_square_mem S (T : Subgroup G)
      T.isPGroup' hST
    exact ⟨t,ht,ho,hn,hs,fun hh => (hlt hh).elim⟩
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
