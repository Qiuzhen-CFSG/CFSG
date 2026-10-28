module

public import Theory.Representation.BinaryPermutation.FiveAction
public import Theory.Representation.BinaryPermutation.FiveCentralizerGeometry

/-!
# Finite polar geometry used in nonsingular reconstruction

The polar pairing on the even-weight core is the coordinate dot product.
The three singular points in the distinguished nonsingular hyperplane span
it. Transitivity on nonsingular vectors and the displayed three-cycle give
transitivity on incident nonsingular–singular flags. The small vector
certificates also supply a common singular seed and show that the family
of hyperplanes covers the whole module.

Source: Aschbacher–Smith, combined manuscript, printed p.928, the geometric
reduction before 13.6.8, with the orthogonal module of §B.3.
-/

public section
open Subgroup BinaryPermutation BinaryPermutation.FiveCentralizerGeometry
open BinaryPermutation.FiveGeometry


namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Reconstruction.Model
private abbrev poly (x : Full (Fin 5)) : ZMod 2 :=
  ∑ i : Fin 5, ∑ j : Fin 5 with i < j, x i * x j

theorem polar_dot (x y : Space) : form.polarBilin x y = ∑ i, x.val i * y.val i := by
  have h : ∀ x y : Full (Fin 5), (∑ i, x i) = 0 → (∑ i, y i) = 0 →
      poly (x + y) - poly x - poly y = ∑ i, x i * y i := by decide
  exact h x.val y.val x.property y.property

theorem polar_act (g : alternatingGroup (Fin 5)) (x y : Space) :
    form.polarBilin (act g x) (act g y) = form.polarBilin x y := by
  rw [polar_dot, polar_dot]
  exact Equiv.sum_comp g.val.symm (fun i => x.val i * y.val i)

theorem span_certificate (x : Space) (hx : form.polarBilin v x = 0) :
    ∃ i j k : Bool, x = (if i then z else 0) +
      (if j then act cubic z else 0) + (if k then act (cubic ^ 2) z else 0) := by
  have h : ∀ x : Full (Fin 5), (∑ i, x i) = 0 →
      (∑ i, v.val i * x i) = 0 →
      ∃ i j k : Bool, x = (if i then z.val else 0) +
        (if j then (act cubic z).val else 0) +
        (if k then (act (cubic ^ 2) z).val else 0) := by decide
  rw [polar_dot] at hx
  obtain ⟨i,j,k,hx⟩ := h x.val x.property hx
  refine ⟨i,j,k, Subtype.ext ?_⟩
  cases i <;> cases j <;> cases k <;> exact hx


private theorem act_mul (g h : alternatingGroup (Fin 5)) (x : Space) :
    act (g * h) x = act g (act h x) := by
  change coreRepresentation (Fin 5) (g.val * h.val) x = _
  rw [map_mul]
  rfl

@[simp] private theorem act_one (x : Space) : act 1 x = x := by
  change coreRepresentation (Fin 5) 1 x = x
  rw [map_one]
  rfl

@[simp] private theorem act_inv_cancel (g : alternatingGroup (Fin 5)) (x : Space) :
    act g (act g⁻¹ x) = x := by rw [← act_mul]; simp

@[simp] private theorem act_inv_cancel' (g : alternatingGroup (Fin 5)) (x : Space) :
    act g⁻¹ (act g x) = x := by rw [← act_mul]; simp

private theorem form_act (g : alternatingGroup (Fin 5)) (x : Space) :
    form (act g x) = form x := by
  have hz : act g x = 0 ↔ x = 0 := by
    constructor
    · intro h
      have hh := congrArg (act g⁻¹) h
      simpa only [act_inv_cancel', map_zero] using hh
    · rintro rfl
      exact map_zero _
  have hc : (Finset.univ.filter fun i => (act g x).val i ≠ 0).card =
      (Finset.univ.filter fun i => x.val i ≠ 0).card := by
    simp only [Finset.card_filter]
    exact Equiv.sum_comp g.val.symm (fun i => if x.val i ≠ 0 then 1 else 0)
  have hi : form (act g x) = 0 ↔ form x = 0 := by
    rw [singular_iff, singular_iff, hz, hc]
  exact (by decide : ∀ a b : ZMod 2, (a = 0 ↔ b = 0) → a = b) _ _ hi

theorem flag_transport (u t : Space) (hu : form u ≠ 0) (ht : form t = 0)
    (ht0 : t ≠ 0) (hut : form.polarBilin u t = 0) :
    ∃ g : alternatingGroup (Fin 5), act g v = u ∧ act g z = t := by
  have hv : form v ≠ 0 := by decide
  have hq : form v = form u :=
    (by decide : ∀ a b : ZMod 2, a ≠ 0 → b ≠ 0 → a = b) _ _ hv hu
  obtain ⟨g, hg⟩ := exists_even_transport v u v_ne_zero
    (fun he => hu (he ▸ form.map_zero)) hq
  have hp : form.polarBilin v (act g⁻¹ t) = 0 := by
    rw [← polar_act g v (act g⁻¹ t), act_inv_cancel, hg]
    exact hut
  have hs : form (act g⁻¹ t) = 0 := (form_act _ _).trans ht
  have hn : act g⁻¹ t ≠ 0 := by
    intro he
    apply ht0
    have hh := congrArg (act g) he
    simpa only [act_inv_cancel, map_zero] using hh
  have h : ∀ t : Full (Fin 5), (∑ i, t i) = 0 → poly t = 0 →
      t ≠ 0 → (∑ i, v.val i * t i) = 0 →
      ∃ k : Fin 3, (act (cubic ^ k.val) z).val = t := by decide
  obtain ⟨k, hk⟩ := h (act g⁻¹ t).val (act g⁻¹ t).property hs
    (fun he => hn (Subtype.ext he)) ((polar_dot _ _).symm.trans hp)
  have hfix : ∀ k : Fin 3, act (cubic ^ k.val) v = v := by decide
  refine ⟨g * cubic ^ k.val, ?_, ?_⟩
  · rw [act_mul, hfix, hg]
  · rw [act_mul, Subtype.ext hk, act_inv_cancel]

theorem family_covers (x : Space) : ∃ u : Space,
    form u ≠ 0 ∧ form.polarBilin v u = 0 ∧ form.polarBilin u x = 0 := by
  have h : ∀ x : Full (Fin 5), (∑ i, x i) = 0 →
      ∃ u : Full (Fin 5), (∑ i, u i) = 0 ∧ poly u ≠ 0 ∧
        (∑ i, v.val i * u i) = 0 ∧ (∑ i, u i * x i) = 0 := by decide
  obtain ⟨u, hu, hq, hv, hx⟩ := h x.val x.property
  exact ⟨⟨u, hu⟩, hq, (polar_dot _ _).trans hv, (polar_dot _ _).trans hx⟩

theorem common_seed (u : Space) (hu : form u ≠ 0) (hvu : form.polarBilin v u = 0) :
    ∃ t : Space, t ≠ 0 ∧ form t = 0 ∧
      form.polarBilin v t = 0 ∧ form.polarBilin u t = 0 := by
  have h : ∀ u : Full (Fin 5), (∑ i, u i) = 0 → poly u ≠ 0 →
      (∑ i, v.val i * u i) = 0 →
      ∃ t : Full (Fin 5), (∑ i, t i) = 0 ∧ t ≠ 0 ∧ poly t = 0 ∧
        (∑ i, v.val i * t i) = 0 ∧ (∑ i, u i * t i) = 0 := by decide
  obtain ⟨t, ht, ht0, hq, hv, hx⟩ := h u.val u.property hu ((polar_dot _ _).symm.trans hvu)
  exact ⟨⟨t, ht⟩, (fun he => ht0 (congrArg Subtype.val he)), hq,
    (polar_dot _ _).trans hv, (polar_dot _ _).trans hx⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Reconstruction.Model
