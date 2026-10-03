module

public import Theory.GroupAction.C4SquareFixedKernel
public import Theory.GroupTheory.PGroup.C4SquareSelfCentralizing
public import Theory.GroupTheory.PGroup.NormalFourInvariantAbelianBase
public import Theory.GroupTheory.PGroup.NormalEightCentralizerCharacteristic
public import Theory.Frattini.BinarySquares
public import Theory.GroupTheory.PGroup.RankTwoNormalFour
public import Theory.GroupTheory.PGroup.Order128SpecialCharacteristicEight

/-!
# Frattini identification for a self-centralizing C₄-square

Let D be a normal self-centralizing C₄-square with omega W, and put C = C(W).
The action of C on D fixes its involutions, so every square in C centralizes
D and lies in D. Conversely, the squares of a basis of D generate W.
Consequently W ≤ Φ(C) ≤ D.

When ambient normal elementary eights are absent and automorphisms of C
are transitive on the involutions of W, characteristic abelian subgroups
between W and D are homocyclic. This leaves only Φ(C) = W or Φ(C) = D.
The center of C equals W whenever |C| > 16. At ambient order 256 with
central omega of order two, the small-Frattini branch therefore has |C| = 128
and Z(C) = Φ(C) elementary of order four. Transitivity on its central
involutions then gives a characteristic elementary eight by the binary
alternating-pencil theorem. This subgroup is normal in the ambient group,
contradicting the hypothesis and proving D = Φ(C).

Source: the C₄-square case of Janko–Thompson, Math. Z. 113 (1970), 1.4(c),
p.386, citing MacWilliams, Trans. AMS 150 (1970), §4. The normal-eight
hypothesis is used only for ambiently normal subgroups; no inheritance by
arbitrary normal subgroups of C is asserted.
-/

open Subgroup
open scoped IsMulCommutative
namespace C4SquareExtension

/-- The Frattini subgroup of the omega centralizer lies in the self-centralizing base. -/
public theorem frattini_centralizer_le_base {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (W D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* Model)) :
    (frattini (centralizer (W : Set P))).map (centralizer (W : Set P)).subtype ≤ D := by
  obtain ⟨e⟩ := hmodel
  let C := centralizer (W : Set P)
  let f : C →* MulAut D := (MulAut.conjNormal : P →* MulAut D).comp C.subtype
  let g : C →* MulAut Model := (MulAut.congr e).toMonoidHom.comp f
  have hfix (c : C) (d : D) (hd : d ^ 2 = 1) : f c d = d := by
    have hdW : (d : P) ∈ W := by
      rw [← hO]
      exact ⟨d, subset_closure (by simpa using hd), rfl⟩
    apply Subtype.ext
    change (c : P) * (d : P) * (c : P)⁻¹ = d
    rw [← c.property _ hdW, mul_inv_cancel_right]
  have hgfix (c : C) (x : Model) (hx : x ^ 2 = 1) : g c x = x := by
    change e (f c (e.symm x)) = x
    rw [hfix c (e.symm x) (by rw [← map_pow, hx, map_one]), e.apply_symm_apply]
  have hsq (c : C) : c ^ 2 ∈ D.comap C.subtype := by
    have hg : g (c ^ 2) = 1 := by
      rw [map_pow]
      exact square_eq_one_of_fix_square_one _ (hgfix c)
    have hf : f (c ^ 2) = 1 := (MulAut.congr e).injective (by
      change g (c ^ 2) = (MulAut.congr e).toMonoidHom 1
      rwa [map_one])
    have hk : ((c ^ 2 : C) : P) ∈ (MulAut.conjNormal : P →* MulAut D).ker := hf
    rwa [conjNormal_ker_eq_of_selfCentralizing_abelian D hDC] at hk
  rw [map_le_iff_le_comap, (hP.to_subgroup C).frattini_eq_closure_squares]
  exact (closure_le _).mpr (by rintro _ ⟨x, rfl⟩; exact hsq x)

/-- The omega four of a C₄-square lies in the Frattini subgroup of its centralizer. -/
public theorem omega_le_frattini_centralizer {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (W D : Subgroup P) [IsMulCommutative D] (hWD : W ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* Model)) :
    W ≤ (frattini (centralizer (W : Set P))).map (centralizer (W : Set P)).subtype := by
  let C := centralizer (W : Set P)
  have hDC : D ≤ C := (le_centralizer D).trans (centralizer_le hWD)
  obtain ⟨e⟩ := hmodel
  obtain ⟨a, b, -, -, -, hD, hW⟩ := exists_basis D W e hO
  have ha : a ∈ D := hD ▸ subset_closure (by simp)
  have hb : b ∈ D := hD ▸ subset_closure (by simp)
  let : Fact (IsPGroup 2 C) := ⟨hP.to_subgroup C⟩
  change W ≤ (frattini C).map C.subtype
  rw [hW]
  apply (closure_le _).mpr
  intro x hx
  rcases (by simpa using hx : x = a ^ 2 ∨ x = b ^ 2) with rfl | rfl
  · exact ⟨(⟨a, hDC ha⟩ : C) ^ 2, pth_power_mem_frattini_of_isPGroup _, rfl⟩
  · exact ⟨(⟨b, hDC hb⟩ : C) ^ 2, pth_power_mem_frattini_of_isPGroup _, rfl⟩

/-- A characteristic abelian subgroup between the four and an order-sixteen base equals one endpoint. -/
public theorem characteristic_abelian_eq_four_or_base {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (htrans : ∀ x y : centralizer (W : Set P), (x : P) ∈ W → (y : P) ∈ W →
      orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (centralizer (W : Set P)), a x = y)
    (D : Subgroup P) (hD : Nat.card D = 16)
    (A : Subgroup (centralizer (W : Set P))) [A.Characteristic] [IsMulCommutative A]
    (hWA : W ≤ A.map (centralizer (W : Set P)).subtype)
    (hAD : A.map (centralizer (W : Set P)).subtype ≤ D) :
    A.map (centralizer (W : Set P)).subtype = W ∨
      A.map (centralizer (W : Set P)).subtype = D := by
  let H := A.map (centralizer (W : Set P)).subtype
  obtain ⟨n, hn, ⟨e⟩⟩ :=
    homocyclic_of_characteristic_abelian_over_four hP hno W hW htrans A hWA
  have hH : Nat.card H = 2 ^ (n+n) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, pow_add]
    simp
  have hle : Nat.card H ≤ 16 := (card_le_of_le hAD).trans_eq hD
  have hnle : n ≤ 2 := by
    by_contra! hh
    have hh' : 64 ≤ Nat.card H := by
      rw [hH]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ n+n)
    omega
  have hncase : n = 1 ∨ n = 2 := by omega
  rcases hncase with rfl | rfl
  · exact Or.inl (eq_of_le_of_card_ge hWA (by
      change Nat.card H ≤ Nat.card W
      norm_num [hH, hW])).symm
  · exact Or.inr (eq_of_le_of_card_ge hAD (by
      change Nat.card D ≤ Nat.card H
      norm_num [hH, hD]))

/-- The Frattini subgroup has only the four and the C₄-square as possible ambient images. -/
public theorem frattini_centralizer_eq_four_or_base
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (htrans : ∀ x y : centralizer (W : Set P), (x : P) ∈ W → (y : P) ∈ W →
      orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (centralizer (W : Set P)), a x = y)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hWD : W ≤ D) (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* Model)) :
    (frattini (centralizer (W : Set P))).map (centralizer (W : Set P)).subtype = W ∨
    (frattini (centralizer (W : Set P))).map (centralizer (W : Set P)).subtype = D := by
  let C := centralizer (W : Set P)
  have hle := frattini_centralizer_le_base hP W D hDC hO hmodel
  have hge := omega_le_frattini_centralizer hP W D hWD hO hmodel
  have hD : Nat.card D = 16 := by
    obtain ⟨e⟩ := hmodel
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  let : IsMulCommutative (frattini C) := ⟨⟨fun a b => Subtype.ext (Subtype.ext (by
    exact congrArg (fun d : D => (d : P))
      (mul_comm (⟨((a : C) : P), hle (mem_map_of_mem C.subtype a.property)⟩ : D)
        ⟨((b : C) : P), hle (mem_map_of_mem C.subtype b.property)⟩)))⟩⟩
  exact characteristic_abelian_eq_four_or_base hP hno W hW htrans D hD
    (frattini C) hge hle

/-- Excluding the four as Frattini image identifies the base with the Frattini subgroup. -/
public theorem base_eq_frattini_centralizer_of_ne_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (htrans : ∀ x y : centralizer (W : Set P), (x : P) ∈ W → (y : P) ∈ W →
      orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (centralizer (W : Set P)), a x = y)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hWD : W ≤ D) (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* Model))
    (hne : (frattini (centralizer (W : Set P))).map
      (centralizer (W : Set P)).subtype ≠ W) :
    D = (frattini (centralizer (W : Set P))).map (centralizer (W : Set P)).subtype := by
  exact ((frattini_centralizer_eq_four_or_base hP hno W hW htrans D
    hWD hDC hO hmodel).resolve_left hne).symm

/-- If the centralizer is larger than the base, its center is exactly the four. -/
public theorem center_centralizer_eq_four_of_base_lt_card
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (htrans : ∀ x y : centralizer (W : Set P), (x : P) ∈ W → (y : P) ∈ W →
      orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (centralizer (W : Set P)), a x = y)
    (D : Subgroup P) [IsMulCommutative D] (hD : Nat.card D = 16)
    (hWD : W ≤ D) (hDC : centralizer (D : Set P) ≤ D)
    (hlt : 16 < Nat.card (centralizer (W : Set P))) :
    (center (centralizer (W : Set P))).map (centralizer (W : Set P)).subtype = W := by
  let C := centralizer (W : Set P)
  have hDC' : D ≤ C := (le_centralizer D).trans (centralizer_le hWD)
  have hWZ : W ≤ (center C).map C.subtype := by
    intro w hw
    refine ⟨⟨w, hDC' (hWD hw)⟩, mem_center_iff.mpr ?_, rfl⟩
    intro c
    exact Subtype.ext (c.property w hw).symm
  have hZD : (center C).map C.subtype ≤ D := by
    rintro _ ⟨c, hc, rfl⟩
    apply hDC
    intro d hd
    exact congrArg Subtype.val (mem_center_iff.mp hc (⟨d, hDC' hd⟩ : C))
  rcases characteristic_abelian_eq_four_or_base hP hno W hW htrans D hD
    (center C) hWZ hZD with heq | heq
  · exact heq
  · have hCD : C ≤ D := by
      intro c hc
      apply hDC
      intro d hd
      obtain ⟨z, hz, he⟩ := heq.symm ▸ hd
      change (z : P) = d at he
      rw [← he]
      exact (congrArg Subtype.val (mem_center_iff.mp hz (⟨c, hc⟩ : C))).symm
    have hh := card_le_of_le hCD
    change Nat.card C ≤ Nat.card D at hh
    change 16 < Nat.card C at hlt
    omega

/-- At ambient order 256, the small-Frattini branch gives an order-128 group with elementary center equal to Frattini, transitive central involutions, and no characteristic elementary eight. -/
public theorem small_frattini_branch
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcard : Nat.card P = 256)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (htrans : ∀ x y : centralizer (W : Set P), (x : P) ∈ W → (y : P) ∈ W →
      orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (centralizer (W : Set P)), a x = y)
    (D : Subgroup P) [IsMulCommutative D]
    (hWD : W ≤ D) (hDC : centralizer (D : Set P) ≤ D)
    (hmodel : Nonempty (D ≃* Model))
    (hsmall : (frattini (centralizer (W : Set P))).map
      (centralizer (W : Set P)).subtype = W) :
    let C := centralizer (W : Set P)
    Nat.card C = 128 ∧ Nat.card (center C) = 4 ∧
    IsElementaryAbelian 2 (center C) ∧ frattini C = center C ∧
    (∀ x y : C, x ∈ center C → y ∈ center C → orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut C, a x = y) ∧
    ¬ ∃ K : Subgroup C, K.Characteristic ∧ IsElementaryAbelian 2 K ∧ 8 ≤ Nat.card K := by
  let C := centralizer (W : Set P)
  have hC : Nat.card C = 128 := by
    have hh := C.card_mul_index
    rw [centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
      hP hZ W hW, hcard] at hh
    omega
  have hD : Nat.card D = 16 := by
    obtain ⟨e⟩ := hmodel
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have hCW : (center C).map C.subtype = W :=
    center_centralizer_eq_four_of_base_lt_card hP hno W hW htrans D hD hWD hDC
      (by change 16 < Nat.card C; omega)
  have hcc : Nat.card (center C) = 4 := by
    have hh := congrArg (fun H : Subgroup P => Nat.card H) hCW
    simpa only [card_map_of_injective C.subtype_injective, hW] using hh
  have hel : IsElementaryAbelian 2 (center C) := by
    refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
    intro x
    apply Subtype.ext
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian _
      (hCW.le (mem_map_of_mem C.subtype x.property))
  have hphi : frattini C = center C :=
    map_injective C.subtype_injective (hsmall.trans hCW.symm)
  refine ⟨hC, hcc, hel, hphi, ?_,
    no_characteristic_elementary_eight_of_normal hno C⟩
  intro x y hx hy hx2 hy2
  have hxW : (x : P) ∈ W := by
    exact hCW.le (mem_map_of_mem C.subtype hx)
  have hyW : (y : P) ∈ W := by
    exact hCW.le (mem_map_of_mem C.subtype hy)
  exact htrans x y hxW hyW hx2 hy2

/-- In the order-256 case, the self-centralizing C₄-square is the Frattini
subgroup of the centralizer of its omega four. -/
public theorem base_eq_frattini_centralizer
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcard : Nat.card P = 256)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (htrans : ∀ x y : centralizer (W : Set P), (x : P) ∈ W → (y : P) ∈ W →
      orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (centralizer (W : Set P)), a x = y)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hWD : W ≤ D) (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (hmodel : Nonempty (D ≃* Model)) :
    D = (frattini (centralizer (W : Set P))).map (centralizer (W : Set P)).subtype := by
  apply base_eq_frattini_centralizer_of_ne_four hP hno W hW htrans D hWD hDC hO hmodel
  intro hsmall
  obtain ⟨hC, hcenter, hel, hphi, hcentralTrans, hnoChar⟩ :=
    small_frattini_branch hP hcard hZ hno W hW htrans D hWD hDC hmodel hsmall
  let := hel
  exact hnoChar (Order128SpecialCharacteristicEight.exists_characteristic_elementary_eight
    (hP.to_subgroup (centralizer (W : Set P))) hC hcenter hphi hcentralTrans)

end C4SquareExtension
