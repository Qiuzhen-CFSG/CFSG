module

public import Theory.SpecificGroups.MacWilliams.HallJankoBaseActions
public import Theory.GroupTheory.PGroup.C4SquareSelfCentralizing
import Mathlib.Tactic

/-!
# Generation from the Hall–Janko base actions

The prescribed actions on a self-centralizing C₄-square force the chosen
base and lifts to generate an extension of order 128. The squares of the
basis elements are distinct nonidentity involutions because they generate
an order-four subgroup. Conjugation by `u` and `v` therefore gives distinct
nonidentity actions fixing `a²`, and these yield at least four elements in
its stabilizer. Conjugation by `t` moves `a²`, so the action image has more
than four elements. Its kernel is the sixteen-element base, giving more
than 64 elements in the generated subgroup; its index must consequently be
one. No relations on `t²`, `tu`, or `tv` are needed.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(a), printed p.386,
citing MacWilliams, Trans. AMS 150 (1970), DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup
open scoped IsMulCommutative
namespace MacWilliamsSylow.HallJankoBaseActions

private theorem four_le_card {G : Type*} [Group G] [Finite G]
    (x y : G) (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y) (hx2 : x * x = 1) :
    4 ≤ Nat.card G := by
  classical
  let := Fintype.ofFinite G
  have hxy1 : x * y ≠ 1 := by
    intro h
    apply hxy
    calc
      x = x * (x * y) := by rw [h, mul_one]
      _ = y := by rw [← mul_assoc, hx2, one_mul]
  have hxyx : x * y ≠ x := by simpa using hy
  have hxyy : x * y ≠ y := by simpa using hx
  have hc : ({1, x, y, x * y} : Finset G).card = 4 := by
    simp [hxy, Ne.symm hx, Ne.symm hy,
      Ne.symm hxy1, Ne.symm hxyx, Ne.symm hxyy]
  have hh := Finset.card_le_univ ({1, x, y, x * y} : Finset G)
  simpa [hc, Nat.card_eq_fintype_card] using hh

private theorem independent_squares {P : Type*} [Group P] [Finite P]
    {D W B : Subgroup P} (f : HallJankoBaseActions D W B) (hW : Nat.card W = 4) :
    f.a ^ 2 ≠ 1 ∧ f.b ^ 2 ≠ 1 ∧ f.a ^ 2 ≠ f.b ^ 2 := by
  have hsmall (x : P) (hx : x ^ 2 = 1) (ha : f.a ^ 2 ∈ zpowers x)
      (hb : f.b ^ 2 ∈ zpowers x) : False := by
    have hle : W ≤ zpowers x := by
      rw [f.four]
      exact (closure_le _).mpr (by
        simpa only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe]
          using And.intro ha hb)
    have hc := card_le_of_le hle
    rw [hW, Nat.card_zpowers] at hc
    have ho := orderOf_le_of_pow_eq_one (by decide : 0 < 2) hx
    omega
  have ha4 : (f.a ^ 2) ^ 2 = 1 := by simpa [← pow_mul] using f.a_four
  have hb4 : (f.b ^ 2) ^ 2 = 1 := by simpa [← pow_mul] using f.b_four
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact hsmall _ hb4 (h ▸ one_mem _) (mem_zpowers _)
  · intro h
    exact hsmall _ ha4 (mem_zpowers _) (h ▸ one_mem _)
  · intro h
    exact hsmall _ hb4 (h ▸ mem_zpowers _) (mem_zpowers _)

/-- In an extension of order 128 with a self-centralizing C₄-square base,
the supplied Hall–Janko base actions force the five marked elements to generate. -/
public theorem generate {P : Type*} [Group P] [Finite P]
    (hcard : Nat.card P = 128) {D W B : Subgroup P}
    [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (hW : Nat.card W = 4) (hDC : centralizer (D : Set P) ≤ D)
    (hmodel : Nonempty (D ≃* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4))))
    (f : HallJankoBaseActions D W B) :
    closure ({f.a, f.b, f.u, f.v, f.t} : Set P) = ⊤ := by
  classical
  have haD : f.a ∈ D := f.base.ge (subset_closure (by simp))
  have hbD : f.b ∈ D := f.base.ge (subset_closure (by simp))
  let a : D := ⟨f.a, haD⟩
  let b : D := ⟨f.b, hbD⟩
  let c : P →* MulAut D := MulAut.conjNormal
  have ha4 : a ^ 4 = 1 := Subtype.ext f.a_four
  have hb4 : b ^ 4 = 1 := Subtype.ext f.b_four
  obtain ⟨ha, hb, hab⟩ := independent_squares f hW
  have ha2 : a ^ 2 ≠ 1 := fun h => ha (congrArg Subtype.val h)
  have hb2 : b ^ 2 ≠ 1 := fun h => hb (congrArg Subtype.val h)
  have hab2 : a ^ 2 ≠ b ^ 2 := fun h => hab (congrArg Subtype.val h)
  have hua : c f.u a = a⁻¹ * b ^ 2 := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr f.ua
  have hub : c f.u b = b⁻¹ := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr f.ub
  have hva : c f.v a = a * b ^ 2 := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr f.va
  have hvb : c f.v b = a ^ 2 * b := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr f.vb
  have hta : c f.t a = a * b := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr f.ta
  have ha22 : (a ^ 2) ^ 2 = 1 := by simpa [← pow_mul] using ha4
  have hb22 : (b ^ 2) ^ 2 = 1 := by simpa [← pow_mul] using hb4
  have ha2inv : (a ^ 2)⁻¹ = a ^ 2 :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha22)
  have hu_fix : c f.u (a ^ 2) = a ^ 2 := by
    rw [map_pow, hua, mul_pow, hb22, mul_one, inv_pow, ha2inv]
  have hv_fix : c f.v (a ^ 2) = a ^ 2 := by
    rw [map_pow, hva, mul_pow, hb22, mul_one]
  have ht_move : c f.t (a ^ 2) ≠ a ^ 2 := by
    rw [map_pow, hta, mul_pow]
    simpa using hb2
  have hu_ne : c f.u ≠ 1 := by
    intro h
    have h' : b⁻¹ = b := by simpa [h] using hub.symm
    apply hb2
    simpa only [h', ← pow_two] using inv_mul_cancel b
  have hv_ne : c f.v ≠ 1 := by
    intro h
    have h' : a ^ 2 * b = b := by simpa [h] using hvb.symm
    exact ha2 (mul_right_cancel (h'.trans (one_mul b).symm))
  have huv_ne : c f.u ≠ c f.v := by
    intro h
    have h' : b⁻¹ = a ^ 2 * b := by rw [← hub, h, hvb]
    have h'' : a ^ 2 = (b ^ 2)⁻¹ := by
      calc
        a ^ 2 = b⁻¹ * b⁻¹ := by
          calc
            a ^ 2 = (a ^ 2 * b) * b⁻¹ := (mul_inv_cancel_right _ _).symm
            _ = b⁻¹ * b⁻¹ := congrArg (fun x : D => x * b⁻¹) h'.symm
        _ = (b ^ 2)⁻¹ := by group
    apply hab2
    exact h''.trans (inv_eq_of_mul_eq_one_right (show b ^ 2 * b ^ 2 = 1 by
      simpa only [pow_two] using hb22))
  let K := closure ({f.a, f.b, f.u, f.v, f.t} : Set P)
  have huK : f.u ∈ K := subset_closure (by simp)
  have hvK : f.v ∈ K := subset_closure (by simp)
  have htK : f.t ∈ K := subset_closure (by simp)
  have hDK : D ≤ K := by
    rw [f.base]
    apply Subgroup.closure_mono
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  let r : K →* MulAut D := c.comp K.subtype
  let E := r.range
  let H := E ⊓ MulAction.stabilizer (MulAut D) (a ^ 2)
  have huH : c f.u ∈ H := ⟨⟨⟨f.u, huK⟩, rfl⟩, hu_fix⟩
  have hvH : c f.v ∈ H := ⟨⟨⟨f.v, hvK⟩, rfl⟩, hv_fix⟩
  have htE : c f.t ∈ E := ⟨⟨f.t, htK⟩, rfl⟩
  have hu2 : c f.u * c f.u = 1 := by
    rw [← map_mul]
    have h := elemPow_eq_one_of_isElementaryAbelian (p := 2) f.u f.u_mem
    rw [← pow_two, h, map_one]
  have hH : 4 ≤ Nat.card H :=
    four_le_card (⟨c f.u, huH⟩ : H) ⟨c f.v, hvH⟩
      (fun h => hu_ne (congrArg Subtype.val h))
      (fun h => hv_ne (congrArg Subtype.val h))
      (fun h => huv_ne (congrArg Subtype.val h)) (Subtype.ext hu2)
  have hE : 4 < Nat.card E := by
    by_contra! h
    have heq : H = E := eq_of_le_of_card_ge inf_le_left (by omega)
    exact ht_move ((heq ▸ htE : c f.t ∈ H).2)
  have hk : r.ker = D.subgroupOf K := by
    ext x
    change c (x : P) = 1 ↔ (x : P) ∈ D
    rw [← MonoidHom.mem_ker, Subgroup.conjNormal_ker_eq_of_selfCentralizing_abelian D hDC]
  have hD : Nat.card D = 16 := by
    obtain ⟨e⟩ := hmodel
    rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num
  have hker : Nat.card r.ker = 16 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe hDK).toEquiv, hD]
  have hc := r.ker.card_mul_index
  rw [hker, index_ker] at hc
  have hK : 64 < Nat.card K := by
    change 4 < Nat.card r.range at hE
    omega
  change K = ⊤
  by_contra hnot
  have hi := K.one_lt_index_of_ne_top hnot
  have hcK := K.card_mul_index
  rw [hcard] at hcK
  nlinarith
end MacWilliamsSylow.HallJankoBaseActions
