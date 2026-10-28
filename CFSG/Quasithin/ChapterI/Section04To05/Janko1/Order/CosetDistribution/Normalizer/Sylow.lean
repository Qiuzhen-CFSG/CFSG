module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Setup
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups

/-!
# The Sylow normalizer in the J₁ local configuration

A Sylow subgroup of `A₅ × C₂` is the product of a Sylow four-group with
`C₂`. Its normalizer has order 24, since the normalizer in `A₅` is an
actual point stabilizer. Transport to the marked involution centralizer
forces a factor of three in the ambient Sylow normalizer. Fusion supplies
the factor of seven. The faithful odd automizer inside `GL₃(2)` therefore
has order 21, giving normalizer order 168.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), §4, printed p.225, the paragraph preceding (4.1).
-/

open Subgroup

private abbrev A5 := alternatingGroup (Fin 5)
private abbrev C2 := Multiplicative (ZMod 2)
private abbrev M := A5 × C2

private theorem a5_stabilizer_card (i : Fin 5) :
    Nat.card (MulAction.stabilizer A5 i) = 12 := by
  have hc : ∀ j : Fin 5, Fintype.card {a : A5 // a.val j = j} = 12 := by
    decide +kernel
  exact (Nat.card_eq_fintype_card).trans (hc i)

private theorem model_normalizer_card (P : Sylow 2 M) :
    Nat.card (normalizer (P : Set M)) = 24 := by
  let P1 : Sylow 2 A5 := P.mapSurjective (f := MonoidHom.fst A5 C2)
    (fun x => ⟨(x, 1), rfl⟩)
  have hPcard : Nat.card P = 8 := by
    rw [P.card_eq_multiplicity, Nat.card_prod, nat_card_alternatingGroup]
    norm_num [Nat.factorial, Nat.card_eq_fintype_card]
    decide +kernel
  have hP1card : Nat.card P1 = 4 := by
    rw [P1.card_eq_multiplicity, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
    decide +kernel
  have hPeq : (P : Subgroup M) = (P1 : Subgroup A5).prod ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge
    · intro x hx
      exact ⟨mem_map_of_mem (MonoidHom.fst A5 C2) hx, mem_top _⟩
    · rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
        hP1card, card_top, hPcard]
      norm_num [Nat.card_eq_fintype_card]
  have hNeq : normalizer (P : Set M) =
      (normalizer (P1 : Set A5)).prod (⊤ : Subgroup C2) := by
    change normalizer ((P : Subgroup M) : Set M) = _
    rw [hPeq]
    ext g
    constructor
    · intro hg
      refine ⟨?_, mem_top _⟩
      intro a
      exact ⟨fun ha => ((hg (a, 1)).mp ⟨ha, mem_top _⟩).1,
        fun ha => ((hg (a, 1)).mpr ⟨ha, mem_top _⟩).1⟩
    · intro hg x
      exact ⟨fun hx => ⟨(hg.1 x.1).mp hx.1, mem_top _⟩,
        fun hx => ⟨(hg.1 x.1).mpr hx.1, mem_top _⟩⟩
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer P1
  rw [hNeq, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    hi, a5_stabilizer_card, card_top]
  norm_num [Nat.card_eq_fintype_card]

namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] (h : Janko1CentralizerData G)

/-- The normalizer of the marked Sylow subgroup inside the involution
centralizer has order 24. -/
public theorem sylow_normalizer_in_centralizer_card :
    Nat.card (normalizer (h.sylow : Set G) ⊓ centralizer ({h.z} : Set G) : Subgroup G) = 24 := by
  let C := centralizer ({h.z} : Set G)
  let P := h.sylow.subtype h.sylow_le_centralizer
  let e := h.alternatingCentralizerEquiv
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have he : Nat.card (normalizer (P : Set C)) = 24 := by
    change Nat.card (normalizer ((P : Subgroup C) : Set C)) = 24
    rw [← card_map_of_injective (K := normalizer ((P : Subgroup C) : Set C))
      (f := e.toMonoidHom) e.injective, map_equiv_normalizer_eq]
    exact model_normalizer_card P'
  change Nat.card (normalizer ((h.sylow : Subgroup G).subgroupOf C : Set C)) = 24 at he
  rw [← subgroupOf_normalizer_eq h.sylow_le_centralizer] at he
  exact (Nat.card_congr (subgroupOfEquivOfLe (H := normalizer (h.sylow : Set G) ⊓ C)
    (show normalizer (h.sylow : Set G) ⊓ C ≤ C from inf_le_right)).toEquiv).symm.trans
    (by simpa only [inf_subgroupOf_right, Sylow.coe_coe, C] using he)

/-- The beginning of Bender §4: the Sylow normalizer has order 168. -/
public theorem sylow_normalizer_card [IsSimpleGroup G] :
    Nat.card (normalizer (h.sylow : Set G)) = 168 := by
  let S := (h.sylow : Subgroup G)
  let f := S.normalizerMonoidHom
  have hk : f.ker = S.subgroupOf (normalizer (S : Set G)) := by
    rw [normalizerMonoidHom_ker]
    change (centralizer (h.sylow : Set G)).subgroupOf _ = _
    rw [h.sylow_centralizer_eq]
  have hcard := f.ker.card_mul_index
  rw [index_ker, hk, Nat.card_congr (subgroupOfEquivOfLe S.le_normalizer).toEquiv,
    h.sylow_card] at hcard
  have h3 : 3 ∣ 8 * Nat.card f.range := by
    rw [hcard]
    exact (show 3 ∣ 24 by decide).trans
      (h.sylow_normalizer_in_centralizer_card ▸ card_dvd_of_le
        (show normalizer (h.sylow : Set G) ⊓ centralizer ({h.z} : Set G) ≤
          normalizer (h.sylow : Set G) from inf_le_left))
  have h7 := h.sylow_automizer_seven_dvd
  have ho := h.sylow_automizer_odd
  let _ := h.sylow_elementaryAbelian
  have hd : Nat.card f.range ∣ 168 :=
    (card_mulAut_of_elementary_eight h.sylow h.sylow_card) ▸ f.range.card_subgroup_dvd_card
  have hm := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  have hs : (168 : ℕ).divisors =
      {1, 2, 3, 4, 6, 7, 8, 12, 14, 21, 24, 28, 42, 56, 84, 168} := by decide
  rw [hs] at hm
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  have hn2 := ho.not_two_dvd_nat
  change ¬ 2 ∣ Nat.card f.range at hn2
  change 7 ∣ Nat.card f.range at h7
  have hf : Nat.card f.range = 21 := by omega
  rw [hf] at hcard
  exact hcard.symm
end CFSG.Quasithin.Janko1CentralizerData
