module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.CosetKernel
public import Theory.Frattini.SquareImage

/-!
# The opposite-core kernel and its orbit in a faithful Goldschmidt pair

Let A and B be the original vertices and let K be the normal core in A
of the embedded O₂(B). Every square in O₂(A) lies in K: conjugation by A
preserves O₂(A), while the original O₂(B) has index two in the common
Sylow subgroup. Thus the literal image of O₂(A) in A/K is elementary
abelian, has order dividing eight, and the original Frattini subgroup lies
in K. If B has characteristic two and O₂(G)=1, the index of K in A is
12, 24, or 48. Faithfulness also gives N_B(K)=A∩B for nontrivial K, so
there are exactly three opposite-vertex conjugates.

These facts isolate, rather than assume, the remaining kernel-size step.
The order bound 384 is equivalent to the correctly weighted alternatives
(index 12, kernel at most 32), (24, at most 16), or (48, at most 8).
The final consumers allow either orientation and preserve the literal
images in G/O₂(G). No universal kernel-size bound is asserted here.

Source: Aschbacher–Smith, F.1.12 and the both-characteristic-two branch
of F.6.5, printed pp.262–264 and 305. The elementary refinement uses only
the original local quotient, Sylow, generation, and faithfulness data.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {A B : Subgroup G}

/-- Every original core square is killed by the opposite-core coset action. -/
theorem IsGoldschmidtTriple.twoCore_square_mem_opposite_kernel (h : IsGoldschmidtTriple A B) (x : A) (hx : x ∈ pCore 2 A) :
    x ^ 2 ∈ (((pCore 2 B).map B.subtype).subgroupOf A).normalCore := by
  intro g
  let y : A := g * x * g⁻¹
  have hy : y ∈ pCore 2 A := (inferInstance : (pCore 2 A).Normal).conj_mem x hx g
  have hyT : (y : G) ∈ B ⊓ A := by
    have hi := h.local_twoCore_le_intersection (mem_map_of_mem A.subtype hy)
    exact ⟨hi.2,hi.1⟩
  have hh := (((pCore 2 B).map B.subtype).subgroupOf (B ⊓ A)).sq_mem_of_index_two
    h.symm.left_core_index ⟨y,hyT⟩
  change ((y : G) ^ 2) ∈ (pCore 2 B).map B.subtype at hh
  change ((g * x ^ 2 * g⁻¹ : A) : G) ∈ (pCore 2 B).map B.subtype
  simpa only [y, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, conj_pow] using hh


/-- The image of the original core in the actual degree-six quotient is elementary. -/
theorem IsGoldschmidtTriple.opposite_kernel_image_elementary
    (h : IsGoldschmidtTriple A B) :
    IsElementaryAbelian 2 ((pCore 2 A).map (QuotientGroup.mk'
      (((pCore 2 B).map B.subtype).subgroupOf A).normalCore)) := by
  let K := (((pCore 2 B).map B.subtype).subgroupOf A).normalCore
  let q := QuotientGroup.mk' K
  let E := (pCore 2 A).map q
  have hs (e : E) : e ^ 2 = 1 := by
    obtain ⟨x, hx, he⟩ := e.property
    apply Subtype.ext
    change e.val ^ 2 = 1
    rw [← he,← map_pow]
    exact (QuotientGroup.eq_one_iff (x ^ 2)).mpr
      (h.twoCore_square_mem_opposite_kernel x hx)
  have hi (e : E) : e⁻¹ = e := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hs e)
  exact {
    toIsMulCommutative := IsMulCommutative.of_comm (fun a b => by
      calc
        a * b = (a * b)⁻¹ := (hi _).symm
        _ = b * a := by rw [mul_inv_rev,hi,hi])
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

/-- The original core Frattini subgroup is contained in the literal kernel. -/
theorem IsGoldschmidtTriple.twoCore_frattini_le_opposite_kernel
    (h : IsGoldschmidtTriple A B) :
    (frattini (pCore 2 A)).map (pCore 2 A).subtype ≤
      (((pCore 2 B).map B.subtype).subgroupOf A).normalCore := by
  let K := (((pCore 2 B).map B.subtype).subgroupOf A).normalCore
  let f := (QuotientGroup.mk' K).comp (pCore 2 A).subtype
  have hphi := frattini_le_ker_of_square_image f (fun x => by
    change (QuotientGroup.mk' K x.val) ^ 2 = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (x.val ^ 2)).mpr
      (h.twoCore_square_mem_opposite_kernel x.val x.property))
  rintro x ⟨y, hy, rfl⟩
  exact (QuotientGroup.eq_one_iff y.val).mp (hphi hy)

/-- The quotient order is six times its original core image order. -/
theorem IsGoldschmidtTriple.opposite_kernel_index_eq_six_mul_image_card
    (h : IsGoldschmidtTriple A B) :
    let K := (((pCore 2 B).map B.subtype).subgroupOf A).normalCore
    K.index = 6 * Nat.card ((pCore 2 A).map (QuotientGroup.mk' K)) := by
  let K := (((pCore 2 B).map B.subtype).subgroupOf A).normalCore
  let E := (pCore 2 A).map (QuotientGroup.mk' K)
  have he : E.index = 6 := by
    rw [index_map_eq (pCore 2 A) (QuotientGroup.mk'_surjective K)
      (by rw [QuotientGroup.ker_mk']; exact h.opposite_core_normalCore_le_twoCore)]
    change Nat.card (A ⧸ pCore 2 A) = 6
    rw [Nat.card_congr h.quotient_left.some.toEquiv]
    simp [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]
  have hh := E.index_mul_card
  rw [he] at hh
  change K.index = 6 * Nat.card E
  rw [index_eq_card]
  exact hh.symm

/-- The elementary core image has order dividing eight. -/
theorem IsGoldschmidtTriple.opposite_kernel_image_card_dvd_eight
    (h : IsGoldschmidtTriple A B) :
    Nat.card ((pCore 2 A).map (QuotientGroup.mk'
      (((pCore 2 B).map B.subtype).subgroupOf A).normalCore)) ∣ 8 := by
  have hi := h.opposite_core_normalCore_index_dvd_forty_eight
  rw [h.opposite_kernel_index_eq_six_mul_image_card] at hi
  exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 6)).mp hi

private theorem core_ne_bot (h : IsGoldschmidtTriple A B)
    (hgood : generalizedFitting A = pCore 2 A) : pCore 2 A ≠ ⊥ := by
  intro hc
  have hcent := h.local_core_selfCentralizing hgood
  rw [hc] at hcent
  have ht : (⊤ : Subgroup A) = ⊥ := le_bot_iff.mp (by
    intro x _
    apply hcent
    intro y hy
    have hyone : y = 1 := hy
    simp [hyone])
  have hcard := congrArg (fun K : Subgroup A => Nat.card K) ht
  rw [card_top,card_bot] at hcard
  have horder := SymmetricThreeTwoCore.card_eq h.quotient_left.some
  rw [hc,card_bot,hcard] at horder
  norm_num at horder

/-- Index six would make the whole opposite core normal in both original vertices. -/
theorem IsGoldschmidtTriple.opposite_kernel_index_ne_six
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hgood : generalizedFitting B = pCore 2 B) :
    (((pCore 2 B).map B.subtype).subgroupOf A).normalCore.index ≠ 6 := by
  intro hi
  let N := (pCore 2 B).map B.subtype
  let R := N.subgroupOf A
  have heq : R.normalCore = R := by
    rcases lt_or_eq_of_le R.normalCore_le with hl | he
    · have hh := index_strictAnti hl
      rw [h.opposite_core_index_six,hi] at hh
      omega
    · exact he
  have hRA : R.Normal := by rw [← heq]; infer_instance
  let _ := hRA
  have hNA : N ≤ A := h.symm.local_twoCore_le_intersection.trans inf_le_right
  have hnormA : A ≤ normalizer (N : Set G) := by
    have hh := R.le_normalizer_map A.subtype
    rw [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] at hh
    rwa [map_subgroupOf_eq_of_le hNA] at hh
  have hnormB : B ≤ normalizer (N : Set G) := by
    have hh := (pCore 2 B).le_normalizer_map B.subtype
    simpa only [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] using hh
  have hn : N = ⊥ := h.common_normal_eq_bot hcore N
    (by simpa only [inf_comm B A] using h.symm.local_twoCore_le_intersection)
    (normal_subgroupOf_of_le_normalizer hnormA)
    (normal_subgroupOf_of_le_normalizer hnormB)
  exact core_ne_bot h.symm hgood
    ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp hn)

/-- The three possible nondegenerate quotient orders in the faithful good branch. -/
theorem IsGoldschmidtTriple.opposite_kernel_index_cases
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hgood : generalizedFitting B = pCore 2 B) :
    let K := (((pCore 2 B).map B.subtype).subgroupOf A).normalCore
    K.index = 12 ∨ K.index = 24 ∨ K.index = 48 := by
  have hd := h.opposite_core_normalCore_index_dvd_forty_eight
  have h6 : 6 ∣ (((pCore 2 B).map B.subtype).subgroupOf A).normalCore.index := by
    rw [h.opposite_kernel_index_eq_six_mul_image_card]
    exact dvd_mul_right _ _
  have hn := h.opposite_kernel_index_ne_six hcore hgood
  rcases (show ∀ n : ℕ, n ∣ 48 → 6 ∣ n → n ≠ 6 → n = 12 ∨ n = 24 ∨ n = 48 by
    intro n hd h6 hn
    have hb := Nat.le_of_dvd (by decide : 0 < 48) hd
    interval_cases n <;> norm_num at *) _ hd h6 hn with h12 | h24 | h48
  · exact Or.inl h12
  · exact Or.inr (Or.inl h24)
  · exact Or.inr (Or.inr h48)


/-- A nontrivial kernel is normalized in the opposite vertex exactly by the original overlap. -/
theorem IsGoldschmidtTriple.opposite_kernel_normalizer_intersection
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hne : (((pCore 2 B).map B.subtype).subgroupOf A).normalCore ≠ ⊥) :
    B ⊓ normalizer
      ((((pCore 2 B).map B.subtype).subgroupOf A).normalCore.map A.subtype : Set G) =
      A ⊓ B := by
  let R := ((pCore 2 B).map B.subtype).subgroupOf A
  let K := R.normalCore
  let N := K.map A.subtype
  have hNA : A ≤ normalizer (N : Set G) := by
    have hh := K.le_normalizer_map A.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hNT : N ≤ A ⊓ B := by
    rintro x ⟨y, hy, rfl⟩
    refine ⟨y.property, ?_⟩
    exact (h.symm.local_twoCore_le_intersection (R.normalCore_le hy)).1
  have hTN : A ⊓ B ≤ normalizer (N : Set G) := inf_le_left.trans hNA
  have hiT : (A ⊓ B).relIndex B = 3 := by
    have hh := ((A ⊓ B).subgroupOf B).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (show A ⊓ B ≤ B from inf_le_right)).toEquiv,
      h.symm.local_card_eq_three_mul_intersection, inf_comm B A] at hh
    have hp := Nat.card_pos (α := (A ⊓ B : Subgroup G))
    change ((A ⊓ B).subgroupOf B).index = 3
    nlinarith
  have hd : (normalizer (N : Set G)).relIndex B ∣ 3 := by
    rw [← hiT]
    exact relIndex_dvd_of_le_left B hTN
  have hiN : (normalizer (N : Set G)).relIndex B = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · have hBN := relIndex_eq_one.mp h1
      have hn : N = ⊥ := h.common_normal_eq_bot hcore N hNT
        (normal_subgroupOf_of_le_normalizer hNA)
        (normal_subgroupOf_of_le_normalizer hBN)
      exact (hne ((map_eq_bot_iff_of_injective _ A.subtype_injective).mp hn)).elim
    · exact h3
  have hle : (A ⊓ B).subgroupOf B ≤ (normalizer (N : Set G)).subgroupOf B :=
    subgroupOf_mono B hTN
  have he : (A ⊓ B).subgroupOf B = (normalizer (N : Set G)).subgroupOf B := by
    rcases lt_or_eq_of_le hle with hl | he
    · have hh := index_strictAnti hl
      change (normalizer (N : Set G)).relIndex B < (A ⊓ B).relIndex B at hh
      omega
    · exact he
  have hh := congrArg (fun H : Subgroup B => H.map B.subtype) he
  rw [map_subgroupOf_eq_of_le (show A ⊓ B ≤ B from inf_le_right), subgroupOf_map_subtype] at hh
  exact (inf_comm _ _).trans hh.symm

/-- The original opposite vertex has exactly three conjugates of every
nontrivial degree-six kernel. -/
theorem IsGoldschmidtTriple.opposite_kernel_normalizer_relIndex
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hne : (((pCore 2 B).map B.subtype).subgroupOf A).normalCore ≠ ⊥) :
    (normalizer
      ((((pCore 2 B).map B.subtype).subgroupOf A).normalCore.map A.subtype : Set G)).relIndex B = 3 := by
  let N := (((pCore 2 B).map B.subtype).subgroupOf A).normalCore.map A.subtype
  have he : (normalizer (N : Set G)).subgroupOf B = (A ⊓ B).subgroupOf B := by
    ext x
    change (x : G) ∈ normalizer (N : Set G) ↔ (x : G) ∈ A ⊓ B
    constructor
    · intro hx
      exact h.opposite_kernel_normalizer_intersection hcore hne ▸
        (show (x : G) ∈ B ⊓ normalizer (N : Set G) from ⟨x.property,hx⟩)
    · intro hx
      have hh : (x : G) ∈ B ⊓ normalizer (N : Set G) :=
        (h.opposite_kernel_normalizer_intersection hcore hne).symm ▸ hx
      exact hh.2
  change ((normalizer (N : Set G)).subgroupOf B).index = 3
  rw [he]
  have hh := ((A ⊓ B).subgroupOf B).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe (show A ⊓ B ≤ B from inf_le_right)).toEquiv,
    h.symm.local_card_eq_three_mul_intersection, inf_comm B A] at hh
  have hp := Nat.card_pos (α := (A ⊓ B : Subgroup G))
  nlinarith

/-- The exact weighted kernel-size obligation for the original vertex order bound. -/
theorem IsGoldschmidtTriple.local_card_le_384_iff_opposite_kernel_bounds
    (h : IsGoldschmidtTriple A B) (hcore : pCore 2 G = ⊥)
    (hgood : generalizedFitting B = pCore 2 B) :
    let K := (((pCore 2 B).map B.subtype).subgroupOf A).normalCore
    Nat.card A ≤ 384 ↔
      (K.index = 12 ∧ Nat.card K ≤ 32) ∨
      (K.index = 24 ∧ Nat.card K ≤ 16) ∨
      (K.index = 48 ∧ Nat.card K ≤ 8) := by
  let K := (((pCore 2 B).map B.subtype).subgroupOf A).normalCore
  change Nat.card A ≤ 384 ↔
      (K.index = 12 ∧ Nat.card K ≤ 32) ∨
      (K.index = 24 ∧ Nat.card K ≤ 16) ∨
      (K.index = 48 ∧ Nat.card K ≤ 8)
  have hc := K.index_mul_card
  rcases h.opposite_kernel_index_cases hcore hgood with hi | hi | hi
  all_goals change K.index = _ at hi
  all_goals rw [hi] at hc ⊢
  all_goals omega

/-- Either orientation of the correctly weighted kernel alternatives bounds
both original vertices and the original common Sylow subgroup. -/
theorem IsGoldschmidtTriple.local_cards_le_384_of_oriented_kernel_bounds
    (h : IsGoldschmidtTriple A B)
    (hbound :
      let K := (((pCore 2 B).map B.subtype).subgroupOf A).normalCore
      let L := (((pCore 2 A).map A.subtype).subgroupOf B).normalCore
      ((K.index ≤ 12 ∧ Nat.card K ≤ 32) ∨
        (K.index ≤ 24 ∧ Nat.card K ≤ 16) ∨ Nat.card K ≤ 8) ∨
      ((L.index ≤ 12 ∧ Nat.card L ≤ 32) ∨
        (L.index ≤ 24 ∧ Nat.card L ≤ 16) ∨ Nat.card L ≤ 8)) :
    Nat.card A ≤ 384 ∧ Nat.card B ≤ 384 ∧ Nat.card (A ⊓ B : Subgroup G) ≤ 128 := by
  have he : Nat.card A = Nat.card B := by
    rw [h.local_card_eq_three_mul_intersection, h.symm.local_card_eq_three_mul_intersection,
      inf_comm B A]
  have hb : Nat.card A ≤ 384 := by
    have step (X Y : Subgroup G) (hh : IsGoldschmidtTriple X Y)
        (hb : let K := (((pCore 2 Y).map Y.subtype).subgroupOf X).normalCore
          (K.index ≤ 12 ∧ Nat.card K ≤ 32) ∨
          (K.index ≤ 24 ∧ Nat.card K ≤ 16) ∨ Nat.card K ≤ 8) :
        Nat.card X ≤ 384 := by
      let K := (((pCore 2 Y).map Y.subtype).subgroupOf X).normalCore
      rw [← K.index_mul_card]
      rcases hb with ⟨hi, hc⟩ | ⟨hi, hc⟩ | hc
      · exact (Nat.mul_le_mul hi hc).trans (by norm_num)
      · exact (Nat.mul_le_mul hi hc).trans (by norm_num)
      · exact (Nat.mul_le_mul
          (Nat.le_of_dvd (by decide) hh.opposite_core_normalCore_index_dvd_forty_eight) hc).trans
          (by norm_num)
    rcases hbound with ha | hb
    · exact step A B h ha
    · rw [he]; exact step B A h.symm hb
  refine ⟨hb, he ▸ hb, ?_⟩
  rw [h.local_card_eq_three_mul_intersection] at hb
  omega


/-- The weighted bound on the literal quotient vertices controls the literal
image of the original common Sylow subgroup, with the original quotient map. -/
theorem IsGoldschmidtTriple.quotient_local_cards_le_384_of_oriented_kernel_bounds
    (h : IsGoldschmidtTriple A B)
    (hbound :
      let q := QuotientGroup.mk' (pCore 2 G)
      let A' := A.map q
      let B' := B.map q
      let K := (((pCore 2 B').map B'.subtype).subgroupOf A').normalCore
      let L := (((pCore 2 A').map A'.subtype).subgroupOf B').normalCore
      ((K.index ≤ 12 ∧ Nat.card K ≤ 32) ∨
        (K.index ≤ 24 ∧ Nat.card K ≤ 16) ∨ Nat.card K ≤ 8) ∨
      ((L.index ≤ 12 ∧ Nat.card L ≤ 32) ∨
        (L.index ≤ 24 ∧ Nat.card L ≤ 16) ∨ Nat.card L ≤ 8)) :
    let q := QuotientGroup.mk' (pCore 2 G)
    Nat.card (A.map q) ≤ 384 ∧ Nat.card (B.map q) ≤ 384 ∧
      Nat.card ((A ⊓ B).map q) ≤ 128 := by
  have hh := h.quotient_twoCore.local_cards_le_384_of_oriented_kernel_bounds hbound
  rw [← h.quotient_twoCore_intersection] at hh
  exact hh

end CFSG.Quasithin.ChapterF
