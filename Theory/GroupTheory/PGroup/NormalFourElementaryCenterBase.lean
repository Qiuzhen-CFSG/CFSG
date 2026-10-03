module

public import Theory.GroupTheory.PGroup.NormalFourAbelianBase
public import Theory.GroupTheory.AbelianSixteenSmallCenter
public import Theory.GroupTheory.AbelianExponentFourRecognition

/-!
# A normal C₄ × C₄ base from an elementary centralizer center

Let W be a normal four in a finite two-group with no normal elementary
eight. Suppose C(W) has center W, class at most two, and exponent dividing
four, and contains an elementary sixteen over W. A normal self-centralizing
abelian overgroup D of W has omega subgroup W. Its square map bounds its
order by sixteen. Order four contradicts self-centrality; order eight bounds
|C(W)| by 32, making the elementary sixteen characteristic in C(W) and
normal in the ambient group. Thus D has order sixteen and is C₄ × C₄.

Source: the structural base step of Janko–Thompson, Math. Z. 113 (1970),
1.4, p.386, and the final paragraph of p.395. No classification of two-groups
or transfer of the no-normal-eight hypothesis to the centralizer is used.
-/

open Subgroup
open scoped IsMulCommutative

public theorem IsPGroup.exists_c4_square_base_of_elementary_centralizer_center
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) (hWB : W ≤ B)
    (hcenter : (center (centralizer (W : Set P))).map (centralizer (W : Set P)).subtype = W)
    (hclass : commutator (centralizer (W : Set P)) ≤ center (centralizer (W : Set P)))
    (hexp : ∀ x : centralizer (W : Set P), x ^ 4 = 1) :
    ∃ D : Subgroup P, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
      centralizer (D : Set P) ≤ D ∧
      Nonempty (D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, hWD, hDn, hDa, -, hself⟩ :=
    exists_normal_abelian_selfCentralizing_containing hP W inferInstance inferInstance
  let : D.Normal := hDn
  let : IsMulCommutative D := hDa
  let : CommGroup D := IsMulCommutative.instCommGroup
  have hO := omega_one_eq_normal_four_of_no_normal_eight hno W D hW hWD
  let C := centralizer (W : Set P)
  have hDC : D ≤ C := D.le_centralizer.trans (centralizer_le hWD)
  have hBC : B ≤ C := B.le_centralizer.trans (centralizer_le hWB)
  have hDf (d : D) : d ^ 4 = 1 := by
    apply Subtype.ext
    exact congrArg (fun c : C => (c : P)) (hexp ⟨d, hDC d.property⟩)
  have hfour : Nat.card (omega₁ D (p := 2)) = 4 := by
    have hh := congrArg (fun H : Subgroup P => Nat.card H) hO
    simpa only [card_map_of_injective D.subtype_injective, hW] using hh
  let sq : D →* D := powMonoidHom 2
  have hker : Nat.card sq.ker = 4 := by
    rwa [IsPGroup.square_ker_eq_omega_one]
  have hrk : sq.range ≤ sq.ker := by
    rintro _ ⟨d, rfl⟩
    change (d ^ 2) ^ 2 = 1
    simpa only [← pow_mul] using hDf d
  have hcard : Nat.card D ≤ 16 := by
    have hh := sq.ker.card_mul_index
    rw [hker, index_ker] at hh
    have hh' := card_le_of_le hrk
    rw [hker] at hh'
    omega
  have hsmall : ¬ Nat.card D ≤ 4 := by
    intro h
    have heq : W = D := eq_of_le_of_card_ge hWD (by omega)
    have hBD : B ≤ D := by
      apply le_trans ?_ hself
      rw [← heq]
      exact hBC
    have hh := card_le_of_le hBD
    omega
  have hne8 : Nat.card D ≠ 8 := by
    intro h8
    let A := D.subgroupOf C
    let T := B.subgroupOf C
    let : IsMulCommutative A := inferInstance
    let : IsElementaryAbelian 2 T := IsElementaryAbelian.subgroupOf hBC
    have hAcard : Nat.card A = 8 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv, h8]
    have hTcard : Nat.card T = 16 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hBC).toEquiv, hB]
    have hZcard : Nat.card (center C) = 4 := by
      have hh := congrArg (fun H : Subgroup P => Nat.card H) hcenter
      simpa only [card_map_of_injective (centralizer (W : Set P)).subtype_injective, hW] using hh
    have hAself : centralizer (A : Set C) ≤ A := by
      intro c hc
      apply hself
      intro d hd
      exact congrArg (fun x : C => (x : P)) (hc ⟨d, hDC hd⟩ hd)
    have hCcard := card_le_thirtytwo_of_center_four_selfCentralizing_eight
      hZcard hclass A hAcard hAself
    let : T.Characteristic := characteristic_of_card_sixteen_of_center_card_four
      hCcard hZcard T hTcard
    have hmap : T.map C.subtype = B := map_subgroupOf_eq_of_le hBC
    have hBn : B.Normal := hmap ▸ (inferInstance : (T.map C.subtype).Normal)
    exact hno ⟨B, hBn, inferInstance, by omega⟩
  have hDcard : Nat.card D = 16 := by
    obtain ⟨n, hn⟩ := (hP.to_subgroup D).exists_card_eq
    have hn4 : n ≤ 4 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by
      simpa only [← hn] using hcard)
    have hn16 : n = 4 := by
      interval_cases n <;> norm_num only [Nat.reducePow] at hn <;> omega
    simpa [hn16] using hn
  refine ⟨D, hWD, hDn, hDa, hself, ?_⟩
  apply nonempty_mulEquiv_c4_square_of_card_involutions hDcard hDf
  exact hker
