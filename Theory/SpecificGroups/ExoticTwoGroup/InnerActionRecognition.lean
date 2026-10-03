module

public import Theory.SpecificGroups.ExoticTwoGroup.ActionModel

/-!
# Recognition of the inner four on a C₄-square

A four-group of automorphisms fixing the square-trivial elements is the
prescribed inner four if each nonidentity member fixes only square-trivial
elements and inverts some element of order four. Encode the congruence
automorphisms as the sixteen binary matrices `I + 2M`; a kernel-checked
finite calculation recognizes any two independent members and their product.

This is the coordinate step for the actions in Janko–Thompson, Math. Z. 113
(1970), 1.4(c), printed p.386. The two structural conditions are explicit
premises here, not consequences of the order of the action image.
-/

set_option maxRecDepth 2000
set_option synthInstance.maxSize 1024
open C4SquareExtension Subgroup
namespace ExoticTwoGroup.ActionModel.InnerRecognition
private abbrev Bits := Fin 2 × Fin 2 × Fin 2 × Fin 2
private def act (m : Bits) (x : Model) : Model :=
  (Multiplicative.ofAdd ((1 + 2 * (m.1.val : ZMod 4)) * x.1.toAdd +
    2 * (m.2.1.val : ZMod 4) * x.2.toAdd),
   Multiplicative.ofAdd (2 * (m.2.2.1.val : ZMod 4) * x.1.toAdd +
    (1 + 2 * (m.2.2.2.val : ZMod 4)) * x.2.toAdd))
private theorem act_invol : ∀ m : Bits, ∀ x : Model, act m (act m x) = x := by decide
private def aut (m : Bits) : MulAut Model where
  toFun := act m
  invFun := act m
  left_inv := act_invol m
  right_inv := act_invol m
  map_mul' x y := by
    ext <;> simp only [act, Prod.fst_mul, Prod.snd_mul,
      toAdd_mul, toAdd_ofAdd] <;> ring
private theorem encode (f : MulAut Model)
    (hf : ∀ x : Model, x ^ 2 = 1 → f x = x) : ∃ m : Bits, f = aut m := by
  have hu : f u ^ 2 = u ^ 2 := by
    rw [← map_pow]
    exact hf _ (by rw [← pow_mul]; exact u_four)
  have hv : f v ^ 2 = v ^ 2 := by
    rw [← map_pow]
    exact hf _ (by rw [← pow_mul]; exact v_four)
  have hc : ∀ a b : Model, a ^ 2 = u ^ 2 → b ^ 2 = v ^ 2 →
      ∃ m : Bits, a = act m u ∧ b = act m v := by
    rw [u_eq, v_eq]
    decide
  obtain ⟨m, hm, hn⟩ := hc (f u) (f v) hu hv
  exact ⟨m, aut_ext hm hn⟩
private def Good (f : Model → Model) : Prop :=
  (∀ x, f x = x → x ^ 2 = 1) ∧ ∃ x, f x = x⁻¹ ∧ x ^ 2 ≠ 1
private theorem table : ∀ m n : Bits,
    act m u ≠ u ∨ act m v ≠ v →
    act n u ≠ u ∨ act n v ≠ v →
    act m u ≠ act n u ∨ act m v ≠ act n v →
    Good (act m) → Good (act n) → Good (fun x => act m (act n x)) →
    ((act m u = u⁻¹ ∧ act m v = u ^ 2 * v⁻¹) ∨
      (act n u = u⁻¹ ∧ act n v = u ^ 2 * v⁻¹) ∨
      (act m (act n u) = u⁻¹ ∧ act m (act n v) = u ^ 2 * v⁻¹)) ∧
    ((act m u = u⁻¹ * v ^ 2 ∧ act m v = v⁻¹) ∨
      (act n u = u⁻¹ * v ^ 2 ∧ act n v = v⁻¹) ∨
      (act m (act n u) = u⁻¹ * v ^ 2 ∧ act m (act n v) = v⁻¹)) := by
  rw [u_eq, v_eq]
  unfold Good
  decide

/-- Fixed and inverted elements recognize the prescribed inner four. -/
public theorem inner_mem_of_fixed_and_inverted (H : Subgroup (MulAut Model)) (hc : Nat.card H = 4)
    (hfix : ∀ f ∈ H, ∀ x : Model, x ^ 2 = 1 → f x = x)
    (hfixed : ∀ f ∈ H, f ≠ 1 → ∀ x : Model, f x = x → x ^ 2 = 1)
    (hinverted : ∀ f ∈ H, f ≠ 1 → ∃ x : Model, f x = x⁻¹ ∧ x ^ 2 ≠ 1) :
    inner₁ ∈ H ∧ inner₂ ∈ H := by
  classical
  let : Fintype H := Fintype.ofFinite H
  have ht : 2 < Fintype.card H := by rw [← Nat.card_eq_fintype_card, hc]; decide
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp ht
  let f : MulAut Model := (a : MulAut Model)⁻¹ * b
  let g : MulAut Model := (a : MulAut Model)⁻¹ * c
  have hf : f ∈ H := H.mul_mem (H.inv_mem a.property) b.property
  have hg : g ∈ H := H.mul_mem (H.inv_mem a.property) c.property
  have hf1 : f ≠ 1 := by
    intro h
    exact hab (Subtype.ext (inv_mul_eq_one.mp h))
  have hg1 : g ≠ 1 := by
    intro h
    exact hac (Subtype.ext (inv_mul_eq_one.mp h))
  have hfg : f ≠ g := by
    intro h
    exact hbc (Subtype.ext (mul_left_cancel h))
  obtain ⟨m, hm⟩ := encode f (hfix f hf)
  obtain ⟨n, hn⟩ := encode g (hfix g hg)
  have hfg1 : f * g ≠ 1 := by
    intro h
    have he : f = g := by
      have hh : ∀ x : Model, f (g x) = x := fun x => congrArg (fun a : MulAut Model => a x) h
      apply MulEquiv.ext
      intro x
      have hi : g (g x) = x := by rw [hn]; exact act_invol n x
      simpa only [hi] using hh (g x)
    exact hfg he
  have hm1 : act m u ≠ u ∨ act m v ≠ v := by
    by_contra! h
    exact hf1 (aut_ext (hm ▸ h.1) (hm ▸ h.2))
  have hn1 : act n u ≠ u ∨ act n v ≠ v := by
    by_contra! h
    exact hg1 (aut_ext (hn ▸ h.1) (hn ▸ h.2))
  have hmn : act m u ≠ act n u ∨ act m v ≠ act n v := by
    by_contra! h
    apply hfg
    rw [hm, hn]
    exact aut_ext h.1 h.2
  have hmG : Good (act m) := by
    change Good (aut m)
    rw [← hm]
    exact ⟨hfixed f hf hf1, hinverted f hf hf1⟩
  have hnG : Good (act n) := by
    change Good (aut n)
    rw [← hn]
    exact ⟨hfixed g hg hg1, hinverted g hg hg1⟩
  have hmnG : Good (fun x => act m (act n x)) := by
    change Good ((aut m * aut n : MulAut Model) : Model → Model)
    rw [← hm, ← hn]
    exact ⟨hfixed _ (H.mul_mem hf hg) hfg1, hinverted _ (H.mul_mem hf hg) hfg1⟩
  obtain ⟨h₁, h₂⟩ := table m n hm1 hn1 hmn hmG hnG hmnG
  have hfm : aut m ∈ H := hm ▸ hf
  have hgn : aut n ∈ H := hn ▸ hg
  constructor
  · rcases h₁ with h | h | h
    · exact (aut_ext (α := aut m) (β := inner₁) (h.1.trans inner₁_u.symm) (h.2.trans inner₁_v.symm)) ▸ hfm
    · exact (aut_ext (α := aut n) (β := inner₁) (h.1.trans inner₁_u.symm) (h.2.trans inner₁_v.symm)) ▸ hgn
    · exact (aut_ext (α := aut m * aut n) (β := inner₁) (h.1.trans inner₁_u.symm) (h.2.trans inner₁_v.symm)) ▸ H.mul_mem hfm hgn
  · rcases h₂ with h | h | h
    · exact (aut_ext (α := aut m) (β := inner₂) (h.1.trans inner₂_u.symm) (h.2.trans inner₂_v.symm)) ▸ hfm
    · exact (aut_ext (α := aut n) (β := inner₂) (h.1.trans inner₂_u.symm) (h.2.trans inner₂_v.symm)) ▸ hgn
    · exact (aut_ext (α := aut m * aut n) (β := inner₂) (h.1.trans inner₂_u.symm) (h.2.trans inner₂_v.symm)) ▸ H.mul_mem hfm hgn
end ExoticTwoGroup.ActionModel.InnerRecognition
