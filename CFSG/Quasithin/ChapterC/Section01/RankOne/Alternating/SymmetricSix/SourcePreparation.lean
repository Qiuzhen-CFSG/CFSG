module
public import Theory.SpecificGroups.SymmetricSix.TranspositionCubic
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# B.2.10 on the original six-letter action

The full permutation group has trivial two-core. Applying B.2.10 to the
original normal module gives its genuine normal Sylow kernel and the exact
intersection with R. Hence R/O₂(G) has order two. If its Thompson image is
trivial, the original Baumann subgroup is already normal; otherwise that
image contains the actual marked transposition.

Source: Aschbacher–Smith C.1.24(c), printed pp.130–131, using B.2.10.
-/

public section

open Subgroup Theory.GroupTheory Equiv Stellmacher
namespace CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.TranspositionCubic
variable {G : Type*} [Group G] [Finite G]

theorem symmetric_six_twoCore_eq_bot : pCore 2 Sym = ⊥ := by
  by_contra hn
  have hnt : Nontrivial (pCore 2 Sym) := (nontrivial_iff_ne_bot _).mpr hn
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 6)) hnt
  have hdiv : 360 ∣ Nat.card (pCore 2 Sym) := by
    have hc : Nat.card (alternatingGroup (Fin 6))=360 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]; decide
    exact hc ▸ card_dvd_of_le hle
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Sym)).exists_card_eq
  have ht : 3 ∣ 2^n := hn ▸ dvd_trans (by decide : 3 ∣ 360) hdiv
  exact (by decide : ¬3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow ht)

omit [Finite G] in
theorem core_quotient_image_card_two (R : Subgroup G)
    (q : G →* Sym) (hc : pCore 2 G=R ⊓ q.ker)
    (r : Sym) (hr : r.IsSwap) (hR : R.map q=zpowers r) :
    Nat.card (R.map (QuotientGroup.mk' (pCore 2 G)))=2 := by
  rw [←relIndex_ker,QuotientGroup.ker_mk',hc,inf_relIndex_left,relIndex_ker,hR,
    Nat.card_zpowers,hr.orderOf]

theorem normal_baumann_or_thompson_swap (V R : Subgroup G)
    [V.Normal] [IsElementaryAbelian 2 V] (hVR : V ≤ R) (hQR : pCore 2 G ≤ R)
    (q : G →* Sym) (hk : q.ker=centralizer (V : Set G))
    (hc : pCore 2 G=R ⊓ q.ker)
    (r : Sym) (hr : r.IsSwap) (hR : R.map q=zpowers r) :
    (ChapterB.baumann R).Normal ∨ r ∈ (elementaryAbelianMaxJ R).map q := by
  by_cases hJ : elementaryAbelianMaxJ R ≤ q.ker
  · left
    apply (ChapterB.lemma_B_2_10_centralizing V R hVR hQR (hk ▸ hc) ?_).2.2.2
    simpa only [ChapterB.thompsonJ_zero,hk] using hJ
  · right
    have hle : (elementaryAbelianMaxJ R).map q ≤ zpowers r := by
      rw [←hR];exact map_mono (sSup_le fun _ hA => hA.1)
    have hne : (elementaryAbelianMaxJ R).map q ≠ ⊥ := by
      exact fun hz => hJ ((Subgroup.map_eq_bot_iff _).mp hz)
    let J := ((elementaryAbelianMaxJ R).map q).subgroupOf (zpowers r)
    let : Fact (Nat.card (zpowers r)).Prime := ⟨by rw [Nat.card_zpowers,hr.orderOf];decide⟩
    rcases J.eq_bot_or_eq_top_of_prime_card with hb | ht
    · have hh := congrArg (map (zpowers r).subtype) hb
      rw [map_subgroupOf_eq_of_le hle,Subgroup.map_bot] at hh
      exact (hne hh).elim
    · have hh := congrArg (map (zpowers r).subtype) ht
      rw [map_subgroupOf_eq_of_le hle,←MonoidHom.range_eq_map,range_subtype] at hh
      rw [hh];exact mem_zpowers r

theorem original_action_preparation (V R : Subgroup G)
    [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* Sym) (hq : Function.Surjective q)
    (hk : q.ker=centralizer (V : Set G))
    (T : Sylow 2 G) (hQR : pCore 2 G ≤ R) (hRT : R ≤ T)
    (L : Subgroup G) (hL : L.IsCComponent) [IsQuasisimple (L ⧸ pCore 2 L)]
    (hm : ⁅V,L⁆ ≠ ⊥)
    (hg : ∀g:G,∃l∈L,∃t∈(T:Subgroup G),l*t=g)
    (r : Sym) (hr : r.IsSwap) (hR : R.map q=zpowers r) :
    (∃ P : Sylow 2 q.ker, (P : Subgroup q.ker).Normal ∧
      (P : Subgroup q.ker).map q.ker.subtype=pCore 2 G) ∧
    pCore 2 G=R ⊓ q.ker ∧
    Nat.card (R.map (QuotientGroup.mk' (pCore 2 G)))=2 ∧
    ((ChapterB.baumann R).Normal ∨ r ∈ (elementaryAbelianMaxJ R).map q) := by
  have hdata := ChapterB.lemma_B_2_10_two V R q hq hk T hQR hRT
    symmetric_six_twoCore_eq_bot L (Or.inl ⟨hL,inferInstance⟩) hm hg
  have hc : pCore 2 G=R ⊓ q.ker := by simpa only [hk] using hdata.2.1
  have hVR : V ≤ R := (show V ≤ pCore 2 G from
    le_sSup ⟨inferInstance,IsElementaryAbelian.isPGroup 2 V⟩).trans hQR
  refine ⟨?_,hc,core_quotient_image_card_two R q hc r hr hR,
    normal_baumann_or_thompson_swap V R hVR hQR q hk hc r hr hR⟩
  rw [hk]
  exact hdata.1
end CFSG.Quasithin.ChapterC.RankOne.SymmetricSix
