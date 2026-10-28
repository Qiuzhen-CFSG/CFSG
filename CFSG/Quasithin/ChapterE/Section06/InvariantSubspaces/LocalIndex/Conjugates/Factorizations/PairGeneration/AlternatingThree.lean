module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration.LocalAction
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.RankOne.Native
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Two conjugates for the alternating-three block

The defining block quotient has order three, and H/L is a two-group.
Consequently the supplied Sylow subgroup has index three. Thompson escape
from O₂(H) makes the three-coset action identify H/O₂(H) with S₃. The
noncentralizing conjugate module gives a nontrivial Baumann image; a
kernel-checked permutation calculation supplies its generating pair.
Local action transport lifts the conjugator into L and retains O₂(LS).

No covering-module split or additional natural-coordinate premise is used.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(2)
and C.5.6, printed pp.155–157 (PDF pp.166–168).
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {A H R L : Subgroup G}

private theorem a3_index (h : Configuration K A H R L)
    (ha : ChapterC.IsAlternatingBlock L 3) (T : Sylow 2 H)
    (hT : (T : Subgroup H).map H.subtype = R) : (T : Subgroup H).index = 3 := by
  obtain ⟨e⟩ := ha.2.2.quotient_iso
  have hL : (pCore 2 L).index = 3 := by
    change Nat.card (L ⧸ pCore 2 L) = 3
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  obtain ⟨a, ha⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
  have hcardL : Nat.card L = 3 * 2 ^ a := by
    rw [← (pCore 2 L).index_mul_card, hL, ha]
  let N := L.subgroupOf H
  let _ : N.Normal := Baumann.native_block_normal h
  have hq : IsPGroup 2 (H ⧸ N) := by
    exact (isPGroup_quotient_pResidual (G := H) 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq (Baumann.native_block_eq_residual h)).symm
  obtain ⟨b, hb⟩ := hq.exists_card_eq
  have hcardH : Nat.card H = 2 ^ (a + b) * 3 := by
    rw [← N.index_mul_card]
    change Nat.card (H ⧸ N) * Nat.card N = _
    rw [hb, Nat.card_congr (subgroupOfEquivOfLe
      (show L ≤ H from h.join_eq ▸ le_sup_left)).toEquiv, hcardL, pow_add]
    ring
  have hc : Nat.Coprime (T : Subgroup H).index (2 ^ (a + b)) :=
    (Nat.coprime_comm.mpr ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr
      T.not_dvd_index)).pow_right _
  have hd : (T : Subgroup H).index ∣ 3 :=
    hc.dvd_mul_left.mp (hcardH ▸ (T : Subgroup H).index_dvd_card)
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with ht | ht
  · have htop := index_eq_one.mp ht
    have hh : H ≤ normalizer (R : Set G) := by
      have hRH : R = H := by
        rw [← hT, htop, ← MonoidHom.range_eq_map, range_subtype]
      rw [hRH]
      exact H.le_normalizer
    exact (Baumann.sylow_not_normalized_by_H h hh).elim
  · exact ht

private theorem a3_quotient (h : Configuration K A H R L)
    (ha : ChapterC.IsAlternatingBlock L 3) :
    Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨T, hT⟩ := h.sylow
  apply sylow_index_three_core_quotient T (a3_index h ha T hT)
  apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal T)
  intro he
  apply Baumann.thompson_not_le_HCore h
  have hr : R = pCoreIn 2 H := by rw [← hT, ← he]; rfl
  rw [← hr]
  exact sSup_le fun _ hE => hE.1

private theorem perm_pair (B : Subgroup (Equiv.Perm (Fin 3)))
    (hB : IsPGroup 2 B) (hne : B ≠ ⊥) :
    ∃ g, B ⊔ B.map (MulAut.conj g).toMonoidHom = ⊤ := by
  have hcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hdiv : Nat.card B ∣ 6 := hcard ▸ B.card_subgroup_dvd_card
  have hcop : Nat.Coprime (Nat.card B) 3 := by
    obtain ⟨n, hn⟩ := hB.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have htwo : Nat.card B = 2 := by
    have hd : Nat.card B ∣ 2 := hcop.dvd_mul_right.mp hdiv
    exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left
      (fun h1 => hne (Subgroup.card_eq_one.mp h1))
  obtain ⟨⟨t, ht⟩, htn⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have htn : t ≠ 1 := fun he => htn (Subtype.ext he)
  have ht2 : t ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨t, ht⟩ : B))
    rw [htwo] at hh
    exact congrArg Subtype.val hh
  have cert : ∀ t : Equiv.Perm (Fin 3), t ^ 2 = 1 → t ≠ 1 →
      ∃ g : Equiv.Perm (Fin 3), ∀ z,
        z = 1 ∨ z = t ∨ z = g * t * g⁻¹ ∨
        z = t * (g * t * g⁻¹) ∨ z = (g * t * g⁻¹) * t ∨
        z = t * (g * t * g⁻¹) * t := by decide +kernel
  obtain ⟨g, hg⟩ := cert t ht2 htn
  refine ⟨g, top_unique ?_⟩
  intro z _
  have htJ : t ∈ B ⊔ B.map (MulAut.conj g).toMonoidHom := mem_sup_left ht
  have huJ : g * t * g⁻¹ ∈ B ⊔ B.map (MulAut.conj g).toMonoidHom :=
    mem_sup_right (mem_map.mpr ⟨t, ht, rfl⟩)
  rcases hg z with rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact htJ
  · exact huJ
  · exact mul_mem htJ huJ
  · exact mul_mem huJ htJ
  · exact mul_mem (mul_mem htJ huJ) htJ

/-- The A₃ block gives an actual S₃ action and the required pair modulo O₂(LS). -/
theorem alternatingThree_pair (h : Configuration K A H R L) (hb : BaumannStructure H R L)
    (ha : ChapterC.IsAlternatingBlock L 3) {x : G}
    (hnc : ¬ (U L).map (MulAut.conj x).toMonoidHom ≤ centralizer (U L : Set G))
    (hspan : S R = (U L).map (MulAut.conj x).toMonoidHom ⊔ Q R L) :
    ∃ y ∈ L, L ≤ ((U L).map (MulAut.conj x).toMonoidHom ⊔
      ((U L).map (MulAut.conj x).toMonoidHom).map (MulAut.conj y).toMonoidHom) ⊔ Q R L := by
  obtain ⟨e⟩ := a3_quotient h ha
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 H := by
    ext a
    change e (QuotientGroup.mk' _ a) = 1 ↔ a ∈ pCore 2 H
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff a
  apply pair_of_action h f hf hk ?_ hspan
  apply perm_pair
  · exact (((Chapter1.isSylowIn_iff.mp h.sylow).1.to_le
      (show S R ≤ R from inf_le_left)).comap_subtype).map f
  · intro he
    have hs := (Subgroup.map_eq_bot_iff _).mp he
    rw [hk] at hs
    apply hnc
    intro v hv
    have hvS : v ∈ S R := hspan ▸ mem_sup_left hv
    have hvQ : v ∈ Q R L := by
      rw [Baumann.localCore_eq_inter h]
      refine ⟨mem_sup_right hvS, ?_⟩
      exact mem_map_of_mem H.subtype
        (hs (show (⟨v, (Baumann.block_baumann_join_le_H h) (mem_sup_right hvS)⟩ : H) ∈
          (S R).subgroupOf H from hvS))
    exact (hb.core_eq ▸ hvQ).2
end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.PairGeneration
end
