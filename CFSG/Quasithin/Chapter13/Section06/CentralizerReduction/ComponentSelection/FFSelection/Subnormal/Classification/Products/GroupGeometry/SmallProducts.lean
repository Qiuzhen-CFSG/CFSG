module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Products.Contracts
public import Theory.GroupTheory.PCoreProduct
public import Theory.SpecificGroups.SymmetricThreeProduct.NormalThreeSubgroups
/-!
# Cubic axes selected by an actual Sylow subgroup

A subnormal cubic lies in the three-core. If just one factor has a
three-core of order three, the cubic is that core axis. For S₃ × S₃,
the abelian three-core has index four and centralizes the cubic. The
normalizer index therefore divides four; containment of a Sylow
2-subgroup makes that index odd, hence one. The checked normal-cubic
axis argument then excludes both diagonals.

Source: the product deductions from Aschbacher–Smith, B.5.6(3),(5),
printed p.105, in 13.6.10, p.928.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification.Products.GroupGeometry
open SymmetricThreeProduct

private theorem core_le {X : Type*} [Group X] [Finite X] (B : Subgroup X) (hs : B.IsSubnormal)
    (hc : Nat.card B = 3) : B ≤ pCore 3 X := by
  have hp : IsPGroup 3 B := IsPGroup.of_card (n := 1) (by simpa using hc)
  have ht : pCore 3 B = ⊤ := top_unique (le_sSup ⟨inferInstance, hp.to_subgroup ⊤⟩)
  have hh := pCoreIn_le_of_subnormal 3 hs
  change (pCore 3 B).map B.subtype ≤ _ at hh
  simpa only [ht, ← MonoidHom.range_eq_map, range_subtype] using hh

private theorem s3_core : pCore 3 S3 = threeCore := by
  apply le_antisymm
  · intro x hx
    by_contra hn
    have hx2 : x ^ 2 = 1 :=
      (show ∀ x : S3, x ∉ threeCore → x ^ 2 = 1 by decide +kernel) x hn
    have he : (⟨x, hx⟩ : pCore 3 S3) = 1 :=
      ((pCore_isPGroup (p := 3) (G := S3)).powEquiv
        (n := 2) (by decide)).injective (by
          change (⟨x, hx⟩ : pCore 3 S3) ^ 2 = (1 : pCore 3 S3) ^ 2
          apply Subtype.ext
          exact hx2)
    have hx1 : x = 1 := congrArg Subtype.val he
    exact hn (hx1.symm ▸ threeCore.one_mem)
  · apply le_sSup
    exact ⟨inferInstance, IsPGroup.of_card (n := 1) (by
      rw [Nat.card_eq_fintype_card]; decide)⟩

private theorem s3_core_card : Nat.card (pCore 3 S3) = 3 := by
  rw [s3_core, Nat.card_eq_fintype_card]; decide

private theorem square_normal (B : Subgroup SymmetricThreeProduct.G)
    (R : Sylow 2 SymmetricThreeProduct.G) (hs : B.IsSubnormal)
    (hc : Nat.card B = 3) (hR : (R : Subgroup SymmetricThreeProduct.G) ≤ normalizer (B : Set SymmetricThreeProduct.G)) : B.Normal := by
  have hB : B ≤ threeCore.prod threeCore := by
    simpa only [pCore_prod, s3_core] using core_le B hs hc
  have hN : threeCore.prod threeCore ≤ normalizer (B : Set SymmetricThreeProduct.G) := by
    apply le_trans (show threeCore.prod threeCore ≤ centralizer (B : Set SymmetricThreeProduct.G) from ?_)
      (centralizer_le_normalizer (B : Set SymmetricThreeProduct.G))
    intro x hx
    rw [mem_centralizer_iff]
    intro b hb
    exact (show ∀ x b : SymmetricThreeProduct.G,
      x ∈ threeCore.prod threeCore → b ∈ threeCore.prod threeCore → b * x = x * b
      by decide +kernel) x b hx (hB hb)
  have hi : (threeCore.prod threeCore).index = 4 := by
    have hh := (threeCore.prod threeCore).card_mul_index
    have hc9 : Nat.card (threeCore.prod threeCore) = 9 := by
      rw [Nat.card_eq_fintype_card]; decide
    rw [hc9, card_group] at hh
    omega
  have hd : (normalizer (B : Set SymmetricThreeProduct.G)).index ∣ 4 := hi ▸ index_dvd_of_le hN
  have hn : ¬ 2 ∣ (normalizer (B : Set SymmetricThreeProduct.G)).index :=
    fun h => R.not_dvd_index (h.trans (index_dvd_of_le hR))
  apply normalizer_eq_top_iff.mp
  apply index_eq_one.mp
  exact Nat.eq_one_of_dvd_coprimes
    ((Nat.prime_two.coprime_pow_of_not_dvd hn).symm)
    (show (normalizer (B : Set SymmetricThreeProduct.G)).index ∣ 2 ^ 2 from hd) dvd_rfl

private theorem square_axes (B : Subgroup SymmetricThreeProduct.G) [B.Normal]
    (hc : Nat.card B = 3) : B = leftThree ∨ B = rightThree := by
  apply normal_twoPerfect_threePart B
  · intro N hn hp
    let := hn
    rcases hp.card_eq_or_dvd with h | h
    · exact index_eq_one.mp h
    · have hd := h.trans N.index_dvd_card
      rw [hc] at hd
      norm_num at hd
  · norm_num [hc]

variable {D E : Type*} [Group D] [Group E]

/-- An actual S₃ equivalence identifies a three-core of order three. -/
theorem symmetricThree_threeCore_card (e : D ≃* S3) : Nat.card (pCore 3 D) = 3 := by
  calc
    _ = Nat.card ((pCore 3 D).map e.toMonoidHom) :=
      (card_map_of_injective e.injective).symm
    _ = Nat.card (pCore 3 S3) := by rw [pCore_map_iso]
    _ = 3 := s3_core_card

private theorem card_left (e : D ≃* S3) :
    Nat.card ((pCore 3 D).prod (⊥ : Subgroup E)) = 3 := by
  rw [Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod, symmetricThree_threeCore_card e, card_bot, mul_one]

private theorem card_right (e : E ≃* S3) :
    Nat.card ((⊥ : Subgroup D).prod (pCore 3 E)) = 3 := by
  rw [Nat.card_congr (prodEquiv _ _).toEquiv, Nat.card_prod, symmetricThree_threeCore_card e, card_bot, one_mul]

variable [Finite D] [Finite E]

/-- Sylow normalization selects an actual cubic axis in a product whose
factors have either trivial three-core or an S₃ equivalence. -/
theorem product_cubic_position
    (hD : Nonempty (D ≃* S3) ∨ pCore 3 D = ⊥)
    (hE : Nonempty (E ≃* S3) ∨ pCore 3 E = ⊥)
    (B : Subgroup (D × E)) (R : Sylow 2 (D × E)) (hs : B.IsSubnormal)
    (hc : Nat.card B = 3) (hR : (R : Subgroup (D × E)) ≤ normalizer (B : Set (D × E))) :
    B.Normal ∧
      ((B = (pCore 3 D).prod ⊥ ∧ Nonempty (D ≃* S3)) ∨
       (B = (⊥ : Subgroup D).prod (pCore 3 E) ∧ Nonempty (E ≃* S3))) := by
  have hB : B ≤ (pCore 3 D).prod (pCore 3 E) := by
    simpa only [pCore_prod] using core_le B hs hc
  rcases hD with hD | hD
  · obtain ⟨d⟩ := hD
    rcases hE with hE | hE
    · obtain ⟨e⟩ := hE
      let f := d.prodCongr e
      let B' := B.map f.toMonoidHom
      let R' := R.mapSurjective (f := f.toMonoidHom) f.surjective
      have hc' : Nat.card B' = 3 := (card_map_of_injective f.injective).trans hc
      have hR' : (R' : Subgroup SymmetricThreeProduct.G) ≤ normalizer (B' : Set SymmetricThreeProduct.G) := by
        change (R.map f.toMonoidHom : Subgroup _) ≤ _
        rw [← B.map_equiv_normalizer_eq f]
        exact map_mono hR
      have hn' : B'.Normal := square_normal B' R' (hs.map f.surjective) hc' hR'
      have hn : B.Normal := by
        simpa only [B', comap_map_eq_self_of_injective (f := f.toMonoidHom) f.injective] using hn'.comap f.toMonoidHom
      let := hn'
      refine ⟨hn, ?_⟩
      rcases square_axes B' hc' with hl | hr
      · left
        refine ⟨eq_of_le_of_card_ge ?_ (by rw [card_left d, hc]), ⟨d⟩⟩
        intro b hb
        have hx : f b ∈ leftThree := hl ▸ mem_map_of_mem f.toMonoidHom hb
        refine ⟨(hB hb).1, ?_⟩
        apply e.injective
        exact (show e b.2 = 1 from hx.2).trans e.map_one.symm
      · right
        refine ⟨eq_of_le_of_card_ge ?_ (by rw [card_right e, hc]), ⟨e⟩⟩
        intro b hb
        have hx : f b ∈ rightThree := hr ▸ mem_map_of_mem f.toMonoidHom hb
        refine ⟨?_, (hB hb).2⟩
        apply d.injective
        exact (show d b.1 = 1 from hx.1).trans d.map_one.symm
    · have hb : B = (pCore 3 D).prod ⊥ :=
        eq_of_le_of_card_ge (by simpa only [hE] using hB) (by rw [card_left d, hc])
      refine ⟨?_, Or.inl ⟨hb, ⟨d⟩⟩⟩
      rw [hb]
      infer_instance
  · rcases hE with hE | hE
    · obtain ⟨e⟩ := hE
      have hb : B = (⊥ : Subgroup D).prod (pCore 3 E) :=
        eq_of_le_of_card_ge (by simpa only [hD] using hB) (by rw [card_right e, hc])
      refine ⟨?_, Or.inr ⟨hb, ⟨e⟩⟩⟩
      rw [hb]
      infer_instance
    · have hb : B = ⊥ := le_bot_iff.mp (by simpa only [hD, hE, bot_prod_bot] using hB)
      rw [hb, card_bot] at hc
      omega

/-- The two core axes catalogue all normal cubics, whether or not they exist. -/
theorem product_normal_catalogue
    (hD : Nonempty (D ≃* S3) ∨ pCore 3 D = ⊥)
    (hE : Nonempty (E ≃* S3) ∨ pCore 3 E = ⊥) :
    ∀ B : Subgroup (D × E), B.Normal → Nat.card B = 3 →
      B = (pCore 3 D).prod ⊥ ∨ B = (⊥ : Subgroup D).prod (pCore 3 E) := by
  intro B hn hc
  let := hn
  let R : Sylow 2 (D × E) := Classical.arbitrary _
  have hR : (R : Subgroup (D × E)) ≤ normalizer (B : Set (D × E)) := by
    rw [normalizer_eq_top]; exact le_top
  have hh := (product_cubic_position hD hE B R hn.isSubnormal hc hR).2
  exact hh.imp And.left And.left
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification.Products.GroupGeometry
