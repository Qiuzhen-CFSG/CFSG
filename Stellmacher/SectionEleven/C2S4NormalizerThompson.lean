module

public import Stellmacher.SectionFiveToSeven.Defs
public import Stellmacher.LaterDefs
public import Mathlib.GroupTheory.Nilpotent
public import Stellmacher.SectionEleven.C2S4SylowPairGeometry
public import Theory.GroupTheory.SymmetricFourModelCoreData
public import Theory.GroupTheory.ElementarySwappedPair

/-!
# The case (II) normalizer and elementary Thompson subgroup

For the Section 11 case (II) setup, a Sylow subgroup of `P1 ≃ C2 × S4`
has order sixteen. Sylow maximality gives `S0 ⊓ P1 = S`, so the stabilizer
in `N = N_{S0}(S)` of the two-core is exactly `S`, provided its ambient
normalizer is `P1`. If the two-core is elementary abelian of order eight
and belongs to a pair containing all such subgroups of `S`, conjugation
and the strict normalizer condition show that `[N : S] = 2` and `|N| = 32`.

The second theorem assembles the elementary Thompson equality from explicit
pair generation, a covering property for elementary subgroups of `S`, and
exclusion of elementary subgroups of order at least eight outside `S`.
It proves the required maximal-order bounds directly; it does not assume
Thompson monotonicity.

The principal theorem `c2s4_normalizer_thompson` supplies these inputs from
the concrete two-core computation and the `C2 × D8` Sylow pair geometry.
Every element of `N` outside `S` swaps the pair: fixing the core would put
it in `P1`, hence in `S`. The pair intersection has order four and contains
the ambient center of `P1`. The explicit hypothesis `C_H(Z(P1)) = P1`
therefore bounds its centralizer in `N` by `S`. The imported pair-swapping
exclusion theorem shows that every elementary subgroup of `N` of order at
least eight lies in `S`, completing `|N| = 32` and `J(N) = S`.

Source: `refs/latex/stellmacher-n-group.tex`, Section 11, lines 2089–2095.
-/

namespace Stellmacher.SectionEleven

open SectionsFiveToSeven

private theorem sylow_intersection
    {H : Type*} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P : Subgroup H)
    (hS0 : S ≤ (S0 : Subgroup H)) (hSylow : IsSylowTwoIn S P) :
    (S0 : Subgroup H) ⊓ P = S := by
  obtain ⟨hSP, T, hT⟩ := hSylow
  have hle : (T : Subgroup P) ≤ (S0 : Subgroup H).subgroupOf P := by
    intro element helement
    apply hS0
    rw [← hT]
    exact ⟨element, helement, rfl⟩
  have heq := T.is_maximal' S0.isPGroup'.comap_subtype hle
  apply le_antisymm
  · intro element helement
    rw [← hT]
    exact ⟨⟨element, helement.2⟩, heq ▸ helement.1, rfl⟩
  · exact le_inf hS0 hSP

private theorem sylow_card
    {H : Type*} [Group H] [Finite H]
    (S P : Subgroup H) (hSylow : IsSylowTwoIn S P)
    (hModel : Later.IsModel P (Later.C2 × Later.S4)) : Nat.card S = 16 := by
  obtain ⟨_, T, hT⟩ := hSylow
  obtain ⟨model⟩ := hModel
  have hP : Nat.card P = 48 := by
    rw [Nat.card_congr model.toEquiv, Nat.card_prod]
    norm_num [Later.C2, Later.S4, Nat.card_eq_fintype_card, Fintype.card_perm]
  rw [← hT, Subgroup.card_map_of_injective P.subtype_injective,
    T.card_eq_multiplicity, hP]
  rw [show 48 = 2 ^ 4 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num)]
  rw [Nat.factorization_pow]
  norm_num [Nat.factorization_pow, Nat.prime_two.factorization, Nat.prime_three.factorization]

private theorem outside_normalizer
    {H : Type*} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S : Subgroup H)
    (hS0 : S ≤ (S0 : Subgroup H)) (hne : S ≠ (S0 : Subgroup H)) :
    ∃ element ∈ (S0 : Subgroup H) ⊓ Subgroup.normalizer (S : Set H), element ∉ S := by
  let A := S.subgroupOf (S0 : Subgroup H)
  have hproper : A < ⊤ := by
    rw [lt_top_iff_ne_top]
    exact fun heq => hne (le_antisymm hS0 (Subgroup.subgroupOf_eq_top.mp heq))
  let : Group.IsNilpotent S0 := S0.isPGroup'.isNilpotent
  obtain ⟨element, hnorm, hout⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent A hproper)
  refine ⟨element, ⟨element.property, ?_⟩, hout⟩
  change element ∈ (Subgroup.normalizer (S : Set H)).subgroupOf (S0 : Subgroup H)
  rw [Subgroup.subgroupOf_normalizer_eq hS0]
  exact hnorm

private theorem conjugate_mul
    {H : Type*} [Group H] (A : Subgroup H) (left right : H) :
    A.map (MulAut.conj (left * right)).toMonoidHom =
      (A.map (MulAut.conj right).toMonoidHom).map (MulAut.conj left).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext element
  simp [MulAut.conj_apply, mul_assoc]

/-- The pair action has stabilizer `S`, yielding index two and order thirty-two. -/
public theorem c2s4_normalizer_card_of_elementary_pair
    {H : Type*} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2) (hne : S ≠ (S0 : Subgroup H))
    (hModel : Later.IsModel P1 (Later.C2 × Later.S4))
    (hNormalizer : Subgroup.normalizer (twoCoreIn P1 : Set H) = P1)
    (hCore_le : twoCoreIn P1 ≤ S)
    (hCore_elem : IsElementaryAbelian 2 (twoCoreIn P1))
    (hCore_card : Nat.card (twoCoreIn P1) = 8)
    (hPair : ∃ B : Subgroup H, ∀ E : Subgroup H,
      E ≤ S → IsElementaryAbelian 2 E → Nat.card E = 8 → E = twoCoreIn P1 ∨ E = B) :
    S.relIndex ((S0 : Subgroup H) ⊓ Subgroup.normalizer (S : Set H)) = 2 ∧
      Nat.card ((S0 : Subgroup H) ⊓ Subgroup.normalizer (S : Set H) : Subgroup H) = 2 ^ 5 := by
  let N := (S0 : Subgroup H) ⊓ Subgroup.normalizer (S : Set H)
  let A := twoCoreIn P1
  have hSP : IsSylowTwoIn S P1 := h.fiveOne.P1_mem.1.2.1
  have hInter := sylow_intersection S0 S P1 h.fiveOne.S_le_S0 hSP
  have hSN : S ≤ N := le_inf h.fiveOne.S_le_S0 Subgroup.le_normalizer
  have hStab (element : H) (helement : element ∈ N) :
      A.map (MulAut.conj element).toMonoidHom = A ↔ element ∈ S := by
    change A.map (↑(MulAut.conj element)) = A ↔ element ∈ S
    rw [← Subgroup.mem_normalizer_iff_map_conj_eq]
    change element ∈ Subgroup.normalizer (twoCoreIn P1 : Set H) ↔ element ∈ S
    rw [hNormalizer, ← hInter]
    exact ⟨fun hP => ⟨helement.1, hP⟩, fun hS => hS.2⟩
  obtain ⟨B, hB⟩ := hPair
  have hImages (element : H) (helement : element ∈ N) :
      A.map (MulAut.conj element).toMonoidHom = A ∨
      A.map (MulAut.conj element).toMonoidHom = B := by
    apply hB
    · have hmap := Subgroup.map_mono (f := (MulAut.conj element).toMonoidHom) hCore_le
      have heq := Subgroup.mem_normalizer_iff_map_conj_eq.mp helement.2
      exact heq ▸ hmap
    · exact hCore_elem.map _
    · exact (Subgroup.card_map_of_injective (MulAut.conj element).injective).trans hCore_card
  obtain ⟨outside, houtN, houtS⟩ := outside_normalizer S0 S h.fiveOne.S_le_S0 hne
  have hinvN := N.inv_mem houtN
  have hinvS : outside⁻¹ ∉ S := fun hinv => houtS (S.inv_mem_iff.mp hinv)
  have hinvImage := (hImages outside⁻¹ hinvN).resolve_left
    (fun heq => hinvS ((hStab outside⁻¹ hinvN).mp heq))
  have hswap : B.map (MulAut.conj outside).toMonoidHom = A := by
    rw [← hinvImage, ← conjugate_mul]
    simp only [mul_inv_cancel, map_one]
    exact Subgroup.map_id A
  have hindex : S.relIndex N = 2 := by
    apply Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mpr
    refine ⟨outside, houtN, houtS, ?_⟩
    intro element helement
    rcases hImages element helement with hfix | hmove
    · exact Or.inr ((hStab element helement).mp hfix)
    · apply Or.inl
      apply (hStab (outside * element) (N.mul_mem houtN helement)).mp
      rw [conjugate_mul, hmove, hswap]
  refine ⟨hindex, ?_⟩
  have hcard := (S.subgroupOf N).card_mul_index
  have hcardS : Nat.card (S.subgroupOf N) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv]
    exact sylow_card S P1 hSP hModel
  change Nat.card (S.subgroupOf N) * S.relIndex N = Nat.card N at hcard
  rw [hcardS, hindex] at hcard
  exact hcard.symm

/-- Pair generation and exclusion establish the elementary Thompson equality. -/
public theorem c2s4_normalizer_thompson_of_elementary_pair
    {H : Type*} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 B : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2) (hne : S ≠ (S0 : Subgroup H))
    (hModel : Later.IsModel P1 (Later.C2 × Later.S4))
    (hNormalizer : Subgroup.normalizer (twoCoreIn P1 : Set H) = P1)
    (hCore_le : twoCoreIn P1 ≤ S)
    (hCore_elem : IsElementaryAbelian 2 (twoCoreIn P1))
    (hCore_card : Nat.card (twoCoreIn P1) = 8)
    (hB_le : B ≤ S) (hB_elem : IsElementaryAbelian 2 B) (hB_card : Nat.card B = 8)
    (hJoin : twoCoreIn P1 ⊔ B = S)
    (hCover : ∀ E : Subgroup H, E ≤ S → IsElementaryAbelian 2 E →
      E ≤ twoCoreIn P1 ∨ E ≤ B)
    (hExclude : ∀ E : Subgroup H,
      E ≤ (S0 : Subgroup H) ⊓ Subgroup.normalizer (S : Set H) →
      IsElementaryAbelian 2 E → 8 ≤ Nat.card E → E ≤ S) :
    Nat.card ((S0 : Subgroup H) ⊓ Subgroup.normalizer (S : Set H) : Subgroup H) = 2 ^ 5 ∧
      elementaryAbelianMaxJ ((S0 : Subgroup H) ⊓ Subgroup.normalizer (S : Set H)) = S := by
  let N := (S0 : Subgroup H) ⊓ Subgroup.normalizer (S : Set H)
  have hSN : S ≤ N := le_inf h.fiveOne.S_le_S0 Subgroup.le_normalizer
  have hPair : ∃ B : Subgroup H, ∀ E : Subgroup H,
      E ≤ S → IsElementaryAbelian 2 E → Nat.card E = 8 → E = twoCoreIn P1 ∨ E = B := by
    refine ⟨B, ?_⟩
    intro E hES hEelem hEcard
    rcases hCover E hES hEelem with hEA | hEB
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge hEA (by omega))
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge hEB (by omega))
  have hcard := (c2s4_normalizer_card_of_elementary_pair S0 S P1 P2 h hne hModel
    hNormalizer hCore_le hCore_elem hCore_card hPair).2
  have hBound (E : Subgroup H) (hEN : E ≤ N) (hEelem : IsElementaryAbelian 2 E) :
      Nat.card E ≤ 8 := by
    by_cases hEcard : 8 ≤ Nat.card E
    · rcases hCover E (hExclude E hEN hEelem hEcard) hEelem with hEA | hEB
      · exact (Subgroup.card_le_of_le hEA).trans_eq hCore_card
      · exact (Subgroup.card_le_of_le hEB).trans_eq hB_card
    · omega
  have hCoreMax : twoCoreIn P1 ∈ elementaryAbelianMaxSubgroups N := by
    refine ⟨hCore_le.trans hSN, hCore_elem, ?_⟩
    intro E hEN hEelem
    rw [hCore_card]
    exact hBound E hEN hEelem
  have hBMax : B ∈ elementaryAbelianMaxSubgroups N := by
    refine ⟨hB_le.trans hSN, hB_elem, ?_⟩
    intro E hEN hEelem
    rw [hB_card]
    exact hBound E hEN hEelem
  refine ⟨hcard, le_antisymm ?_ ?_⟩
  · apply sSup_le
    intro E hE
    have hEcard : 8 ≤ Nat.card E := by
      rw [← hCore_card]
      exact hE.2.2 (twoCoreIn P1) (hCore_le.trans hSN) hCore_elem
    exact hExclude E hE.1 hE.2.1 hEcard
  · calc
      S = twoCoreIn P1 ⊔ B := hJoin.symm
      _ ≤ elementaryAbelianMaxJ N := sup_le (le_sSup hCoreMax) (le_sSup hBMax)

/-- In case (II), the Sylow normalizer of `S` has order thirty-two and
elementary Thompson subgroup `S`, assuming the stated centralizer equality. -/
public theorem c2s4_normalizer_thompson
    {H : Type*} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2) (hne : S ≠ (S0 : Subgroup H))
    (hModel : Later.IsModel P1 (Later.C2 × Later.S4))
    (hNormalizer : Subgroup.normalizer (twoCoreIn P1 : Set H) = P1)
    (hCentralizer : Subgroup.centralizer
      (((Subgroup.center P1).map P1.subtype) : Set H) = P1) :
    Nat.card ((S0 : Subgroup H) ⊓ Subgroup.normalizer (S : Set H) : Subgroup H) = 2 ^ 5 ∧
      elementaryAbelianMaxJ ((S0 : Subgroup H) ⊓ Subgroup.normalizer (S : Set H)) = S := by
  have hSylow : IsSylowTwoIn S P1 := h.fiveOne.P1_mem.1.2.1
  have hInter := sylow_intersection S0 S P1 h.fiveOne.S_le_S0 hSylow
  obtain ⟨hCore, hCards⟩ := symmetric_four_model_twoCore_data (Or.inr hModel)
  have hPcard : Nat.card P1 = 48 := by
    obtain ⟨model⟩ := hModel
    rw [Nat.card_congr model.toEquiv, Nat.card_prod]
    norm_num [Later.C2, Later.S4, Nat.card_eq_fintype_card, Fintype.card_perm]
  have hCoreCard : Nat.card (pCore 2 P1) = 8 := by
    rcases hCards with hSmall | hLarge
    · omega
    · exact hLarge.1
  have hCoreElem : IsElementaryAbelian 2 (twoCoreIn P1) := hCore.map P1.subtype
  have hCoreEight : Nat.card (twoCoreIn P1) = 8 :=
    (Subgroup.card_map_of_injective P1.subtype_injective).trans hCoreCard
  obtain ⟨_, B, hAS, hBS, _, hB, hBcard, hJoin, hFour, hCover, hCenter⟩ :=
    c2s4_sylow_elementary_pair S P1 hSylow hModel hCoreElem hCoreEight
  let A := twoCoreIn P1
  let N := (S0 : Subgroup H) ⊓ Subgroup.normalizer (S : Set H)
  have hSN : S ≤ N := le_inf h.fiveOne.S_le_S0 Subgroup.le_normalizer
  have hPair (E : Subgroup H) (hES : E ≤ S)
      (hE : IsElementaryAbelian 2 E) (hEcard : Nat.card E = 8) : E = A ∨ E = B := by
    rcases hCover E hES hE with hEA | hEB
    · exact Or.inl (Subgroup.eq_of_le_of_card_ge hEA (by
        change Nat.card (twoCoreIn P1) ≤ Nat.card E
        omega))
    · exact Or.inr (Subgroup.eq_of_le_of_card_ge hEB (by omega))
  have hindex := (c2s4_normalizer_card_of_elementary_pair S0 S P1 P2 h hne hModel
    hNormalizer hAS hCoreElem hCoreEight ⟨B, hPair⟩).1
  have hMove (element : H) (helement : element ∈ N) (hout : element ∉ S) :
      A.map (MulAut.conj element).toMonoidHom = B := by
    have hmapS : S.map (MulAut.conj element).toMonoidHom = S :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp helement.2
    have hmapAS : A.map (MulAut.conj element).toMonoidHom ≤ S :=
      (Subgroup.map_mono hAS).trans_eq hmapS
    have hmapCard : Nat.card (A.map (MulAut.conj element).toMonoidHom) = 8 :=
      (Subgroup.card_map_of_injective (MulAut.conj element).injective).trans hCoreEight
    rcases hPair _ hmapAS (hCoreElem.map _) hmapCard with hfix | hmove
    · have hnorm : element ∈ Subgroup.normalizer (A : Set H) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfix
      have hP : element ∈ P1 := hNormalizer ▸ hnorm
      exact (hout (hInter ▸ (show element ∈ (S0 : Subgroup H) ⊓ P1 from
        ⟨helement.1, hP⟩))).elim
    · exact hmove
  have hSwap (element : H) (helement : element ∈ N) (hout : element ∉ S) :
      A.map (MulAut.conj element).toMonoidHom = B ∧
      B.map (MulAut.conj element).toMonoidHom = A := by
    refine ⟨hMove element helement hout, ?_⟩
    have hinv := hMove element⁻¹ (N.inv_mem helement)
      (fun hinv => hout (S.inv_mem_iff.mp hinv))
    rw [← hinv, ← conjugate_mul]
    simp only [mul_inv_cancel, map_one]
    exact Subgroup.map_id A
  have hCent : N ⊓ Subgroup.centralizer ((A ⊓ B : Subgroup H) : Set H) ≤ S := by
    intro element helement
    have hcenterMem : element ∈ Subgroup.centralizer
        (((Subgroup.center P1).map P1.subtype) : Set H) :=
      Subgroup.centralizer_le hCenter helement.2
    have hP : element ∈ P1 := hCentralizer ▸ hcenterMem
    exact hInter ▸ (show element ∈ (S0 : Subgroup H) ⊓ P1 from ⟨helement.1.1, hP⟩)
  have hExclude := Subgroup.elementary_le_of_swapped_pair S N A B hSN inf_le_right
    hindex hAS hBS hFour hCover hSwap hCent
  exact c2s4_normalizer_thompson_of_elementary_pair S0 S P1 P2 B h hne hModel
    hNormalizer hAS hCoreElem hCoreEight hBS hB hBcard hJoin hCover hExclude

end Stellmacher.SectionEleven
