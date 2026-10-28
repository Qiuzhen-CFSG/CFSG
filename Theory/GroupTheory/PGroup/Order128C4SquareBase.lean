module

public import Theory.GroupTheory.PGroup.Order128AbelianBase
public import Theory.GroupTheory.PGroup.NormalFourInvariantAbelianBase
public import Theory.GroupTheory.PGroup.C4SquareSelfCentralizing
public import Theory.GroupTheory.PGroup.CentralInvolutionRoots
public import Theory.GroupTheory.PGroup.RankTwoNormalFour
public import Theory.GroupTheory.SpecificGroups.AbelianCyclicTwoFixedAut
public import Theory.GroupTheory.SpecificGroups.C4TimesC2Automorphism

/-!
# A C₄-square base in a group of order 128

Suppose a two-group of order 128 has a normal four W, no normal elementary
eight, an elementary sixteen, and a unique central involution. If
Aut(C_P(W)) is transitive on the involutions of W, then the group has a
self-centralizing normal abelian C₄-square containing W, with omega W.

The small-base theorem leaves six ordered pairs of cyclic factors. The
four-group and C₄ × C₂ cases have insufficient automorphisms. For a base
D of type C₈ × C₂, put C = C_P(W). The action of C on D is abelian, so
C' lies in D, as does Z(C). Thus C'Z(C) is characteristic abelian in C.
Transitivity makes its image homocyclic; containment in C₈ × C₂ forces
it to equal W. Consequently C has class at most two and elementary center,
so it has exponent at most four, contradicting the element of order eight
in D. The remaining base has type C₄ × C₄.

This gives a direct proof of the base step in the order-128 alternative
of Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(a), printed p.386,
which cites MacWilliams, DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup
open scoped commutatorElement IsMulCommutative

namespace Order128C4SquareBase
private abbrev C8C2 := Multiplicative (ZMod 8) × Multiplicative (ZMod 2)

private theorem c8_has_large : ∃ x : C8C2, x ^ 4 ≠ 1 := by
  exact ⟨(Multiplicative.ofAdd 1, 1), by decide⟩
private theorem c4_pow (x : Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) :
    x ^ 4 = 1 := by
  apply Prod.ext
  · simpa using pow_card_eq_one' (x := x.1)
  · simpa using pow_card_eq_one' (x := x.2)

private theorem characteristic_eq_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (htrans : ∀ x y : centralizer (W : Set P), (x : P) ∈ W → (y : P) ∈ W →
      orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (centralizer (W : Set P)), a x = y)
    (D : Subgroup P) (e : D ≃* C8C2)
    (A : Subgroup (centralizer (W : Set P))) [A.Characteristic] [IsMulCommutative A]
    (hWA : W ≤ A.map (centralizer (W : Set P)).subtype)
    (hAD : A.map (centralizer (W : Set P)).subtype ≤ D) :
    A.map (centralizer (W : Set P)).subtype = W := by
  let H := A.map (centralizer (W : Set P)).subtype
  obtain ⟨n, hn, ⟨f⟩⟩ :=
    homocyclic_of_characteristic_abelian_over_four hP hno W hW htrans A hWA
  have hDcard : Nat.card D = 16 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have hHcard : Nat.card H = 2 ^ (n+n) := by
    rw [Nat.card_congr f.toEquiv, Nat.card_prod, pow_add]
    simp
  have hle : Nat.card H ≤ 16 := (card_le_of_le hAD).trans_eq hDcard
  have hnle : n ≤ 2 := by
    by_contra! hh
    have hh' : 64 ≤ Nat.card H := by
      rw [hHcard]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ n+n)
    omega
  have hn1 : n = 1 := by
    by_contra hh
    have hn2 : n = 2 := by omega
    subst n
    have hHD : H = D := eq_of_le_of_card_ge hAD (by norm_num [hHcard, hDcard])
    obtain ⟨x,hx⟩ := c8_has_large
    let g := (MulEquiv.subgroupCongr hHD).symm.trans f
    have hp : (e.symm x) ^ 4 = 1 := g.injective (by
      rw [map_pow, map_one]
      exact c4_pow _)
    apply hx
    simpa only [map_pow, e.apply_symm_apply, map_one] using congrArg e hp
  exact (eq_of_le_of_card_ge hWA (by change Nat.card H ≤ Nat.card W; rw [hHcard, hn1, hW]; decide)).symm

private theorem not_c8_times_c2
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (htrans : ∀ x y : centralizer (W : Set P), (x : P) ∈ W → (y : P) ∈ W →
      orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (centralizer (W : Set P)), a x = y)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hWD : W ≤ D) (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (e : D ≃* C8C2) : False := by
  let C := centralizer (W : Set P)
  have hWC : W ≤ C := le_centralizer W
  have hDC' : D ≤ C := (le_centralizer D).trans (centralizer_le hWD)
  let f : C →* MulAut D := (MulAut.conjNormal : P →* MulAut D).comp C.subtype
  have hfix (c : C) (d : D) (hd : d ^ 2 = 1) : f c d = d := by
    have hdW : (d : P) ∈ W := by
      rw [← hO]
      exact ⟨d, subset_closure (by simpa using hd), rfl⟩
    apply Subtype.ext
    change (c : P) * (d : P) * (c : P)⁻¹ = d
    rw [← c.property _ hdW, mul_inv_cancel_right]
  have hfcomm := abelian_cyclic_two_fixed_aut_commute_of_equiv (n := 3) (by decide)
    e f hfix
  have hder : commutator C ≤ D.comap C.subtype := by
    have hker : commutator C ≤ f.ker := by
      apply Subgroup.commutator_le.mpr
      intro x _ y _
      apply MonoidHom.mem_ker.mpr
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hfcomm x y).eq
    intro x hx
    have hxker : (x : P) ∈ (MulAut.conjNormal : P →* MulAut D).ker := hker hx
    rwa [conjNormal_ker_eq_of_selfCentralizing_abelian D hDC] at hxker
  have hcenter : center C ≤ D.comap C.subtype := by
    intro c hc
    apply hDC
    intro d hd
    exact congrArg Subtype.val (mem_center_iff.mp hc (⟨d, hDC' hd⟩ : C))
  let A : Subgroup C := commutator C ⊔ center C
  have hAD' : A ≤ D.comap C.subtype := sup_le hder hcenter
  let : A.Characteristic := inferInstanceAs ((commutator C ⊔ center C).Characteristic)
  let : IsMulCommutative A := ⟨⟨fun a b => Subtype.ext (Subtype.ext (by
    exact congrArg (fun d : D => (d : P)) (mul_comm (⟨((a : C) : P), hAD' a.property⟩ : D) ⟨((b : C) : P), hAD' b.property⟩)))⟩⟩
  have hWA : W ≤ A.map C.subtype := by
    intro w hw
    refine ⟨⟨w, hWC hw⟩, (show center C ≤ A from le_sup_right) ?_, rfl⟩
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (c.property w hw).symm
  have hAD : A.map C.subtype ≤ D := by
    rintro _ ⟨a,ha,rfl⟩
    exact hAD' ha
  have hA := characteristic_eq_four hP hno W hW htrans D e A hWA hAD
  have hAW : A ≤ W.comap C.subtype := by
    intro a ha
    rw [← hA]
    exact mem_map_of_mem C.subtype ha
  have hWcenter : W.comap C.subtype ≤ center C := by
    intro w hw
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (c.property w hw).symm
  have hclass : commutator C ≤ center C := le_sup_left.trans (hAW.trans hWcenter)
  have hz (z : C) (hz : z ∈ center C) : z ^ 2 = 1 := by
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (z : P) (hAW ((show center C ≤ A from le_sup_right) hz))
  obtain ⟨x,hx⟩ := c8_has_large
  let d := e.symm x
  let c : C := ⟨d,hDC' d.property⟩
  have hp := IsPGroup.exponent_four_of_class_two_of_center_exponent_two hclass hz c
  have hd : d ^ 4 = 1 := Subtype.ext (congrArg (fun t : C => (t : P)) hp)
  apply hx
  simpa only [map_pow, d, e.apply_symm_apply, map_one] using congrArg e hd


/-- A self-centralizing normal `C₄ × C₂` cannot lie in a group of order 128. -/
private theorem not_c4_times_c2
    {P : Type*} [Group P] [Finite P] (hcard : Nat.card P = 128)
    (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (e : D ≃* C4TimesC2Automorphism.Model) : False := by
  have hDcard : Nat.card D = 8 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have hAut : Nat.card (MulAut D) ≤ 8 := by
    rw [Nat.card_congr (MulAut.congr e).toEquiv]
    exact C4TimesC2Automorphism.card_mulAut_le_eight
  have hi : D.index ≤ 8 := by
    rw [← conjNormal_ker_eq_of_selfCentralizing_abelian D hDC, index_ker]
    exact (card_le_card_group _).trans hAut
  have hc := D.card_mul_index
  rw [hDcard, hcard] at hc
  omega

end Order128C4SquareBase

/-- Fusion-transitivity on the normal four's centralizer forces the small
self-centralizing abelian base in an order-128 group to be a `C₄`-square. -/
public theorem IsPGroup.exists_c4_square_base_of_card_eq_128
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hcard : Nat.card P = 128)
    (hZ : Nat.card (omega₁ (center P) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (htrans : ∀ x y : centralizer (W : Set P), (x : P) ∈ W → (y : P) ∈ W →
      orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (centralizer (W : Set P)), a x = y)
    (B : Subgroup P) [IsElementaryAbelian 2 B] (hB : Nat.card B = 16) :
    ∃ D : Subgroup P, W ≤ D ∧ D.Normal ∧ IsMulCommutative D ∧
      centralizer (D : Set P) ≤ D ∧ (omega₁ D (p := 2)).map D.subtype = W ∧
      Nonempty (D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))) := by
  obtain ⟨D, hWD, hDn, hDa, hDC, hO, -, -, n, m, hn, hm, hnm, ⟨e⟩⟩ :=
    hP.exists_small_normal_abelian_base_of_card_eq_128 hcard hZ hno W hW B hB
  let : D.Normal := hDn
  let : IsMulCommutative D := hDa
  have hcases : (n = 1 ∧ m = 1) ∨ (n = 2 ∧ m = 1) ∨ (n = 1 ∧ m = 2) ∨
      (n = 3 ∧ m = 1) ∨ (n = 1 ∧ m = 3) ∨ (n = 2 ∧ m = 2) := by omega
  rcases hcases with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ |
    ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have hDcard : Nat.card D = 4 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod]
      norm_num
    have heq : D = W := (eq_of_le_of_card_ge hWD (by omega)).symm
    have hC : centralizer (W : Set P) = W :=
      le_antisymm (heq ▸ hDC) (le_centralizer W)
    have hi := centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
      hP hZ W hW
    have hc := (centralizer (W : Set P)).card_mul_index
    rw [hi, hC, hW, hcard] at hc
    omega
  · exact (Order128C4SquareBase.not_c4_times_c2 hcard D hDC e).elim
  · exact (Order128C4SquareBase.not_c4_times_c2 hcard D hDC
      (e.trans MulEquiv.prodComm)).elim
  · exact (Order128C4SquareBase.not_c8_times_c2 hP hno W hW htrans D hWD hDC hO e).elim
  · exact (Order128C4SquareBase.not_c8_times_c2 hP hno W hW htrans D hWD hDC hO
      (e.trans MulEquiv.prodComm)).elim
  · exact ⟨D, hWD, hDn, hDa, hDC, hO, ⟨e⟩⟩
