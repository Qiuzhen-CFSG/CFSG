module
public import Theory.Representation.BinarySevenCode.WeightFourOrbit
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# Cubic movement in a weight-four stabilizer

The stabilizer of the standard weight-four word contains three explicit
three-cycles whose supports cover the seven coordinates. Their common fixed
words cannot have weight six. Conjugating the weight-four word transports
this calculation to every stabilizer. A surjection onto that stabilizer lifts
a cubic mover into the two-residual of the actual finite source group.

Source application: the repaired proper branch of Aschbacher--Smith,
Lemma 12.3.12, printed p.811. Only the natural seven-point action is used;
no assertion about an A₅ residual of this solvable stabilizer is needed.
-/

@[expose] public section
namespace BinarySevenCode
open Subgroup
private def c₀ : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 6, by change Equiv.Perm.sign _ = 1; decide⟩
private def c₁ : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 2 3 * Equiv.swap 3 4, by change Equiv.Perm.sign _ = 1; decide⟩
private def c₂ : alternatingGroup (Fin 7) :=
  ⟨Equiv.swap 3 4 * Equiv.swap 4 5, by change Equiv.Perm.sign _ = 1; decide⟩

set_option maxRecDepth 4096 in
private theorem standard_mover (f : EvenWord) (hf : weight f.val = 6) :
    ∃ a : alternatingGroup (Fin 7), a ^ 3 = 1 ∧
      evenRepresentation a.val e4 = e4 ∧ evenRepresentation a.val f ≠ f := by
  have h : ∀ v : Word, weight v = 6 →
      (∃ i, v (c₀.val.symm i) ≠ v i) ∨
      (∃ i, v (c₁.val.symm i) ≠ v i) ∨
      (∃ i, v (c₂.val.symm i) ≠ v i) := by decide
  rcases h f.val hf with h | h | h
  · refine ⟨c₀, ?_, ?_, ?_⟩
    · decide
    · apply Subtype.ext; decide
    · intro he; obtain ⟨i, hi⟩ := h; exact hi (congrArg (fun v : EvenWord => v.val i) he)
  · refine ⟨c₁, ?_, ?_, ?_⟩
    · decide
    · apply Subtype.ext; decide
    · intro he; obtain ⟨i, hi⟩ := h; exact hi (congrArg (fun v : EvenWord => v.val i) he)
  · refine ⟨c₂, ?_, ?_, ?_⟩
    · decide
    · apply Subtype.ext; decide
    · intro he; obtain ⟨i, hi⟩ := h; exact hi (congrArg (fun v : EvenWord => v.val i) he)

/-- A cubic element of any weight-four stabilizer moves a given weight-six word. -/
theorem exists_cubic_weight_four_mover (w f : EvenWord)
    (hw : weight w.val = 4) (hf : weight f.val = 6) :
    ∃ a : alternatingGroup (Fin 7), a ^ 3 = 1 ∧
      evenRepresentation a.val w = w ∧ evenRepresentation a.val f ≠ f := by
  obtain ⟨b, hb⟩ := weight_four_transitive w e4 hw representative_weights.2.1
  obtain ⟨c, hc, hcw, hcf⟩ := standard_mover (evenRepresentation b.val f)
    ((weight_evenRepresentation b.val f).trans hf)
  refine ⟨b⁻¹*c*b, ?_, ?_, ?_⟩
  · calc
      (b⁻¹*c*b)^3 = b⁻¹*c^3*b := by
        simpa only [inv_inv] using (conj_pow (a := b⁻¹) (b := c) (i := 3))
      _ = 1 := by rw [hc]; group
  · change evenRepresentation (b.val⁻¹*c.val*b.val) w = w
    rw [map_mul, Module.End.mul_apply, map_mul, Module.End.mul_apply, hb, hcw,
      ← hb, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]
  · intro he
    apply hcf
    have hh := congrArg (evenRepresentation b.val) he
    change evenRepresentation b.val (evenRepresentation (b.val⁻¹*c.val*b.val) f) = _ at hh
    rw [← Module.End.mul_apply, ← map_mul] at hh
    have hp : b.val * (b.val⁻¹*c.val*b.val) = c.val*b.val := by group
    rw [hp, map_mul, Module.End.mul_apply] at hh
    exact hh

/-- Surjectivity onto a weight-four stabilizer lifts movement to the actual
finite group's two-residual. -/
theorem exists_pResidual_weight_six_mover {H : Type*} [Group H] [Finite H]
    (q : H →* alternatingGroup (Fin 7)) (w f : EvenWord)
    (hw : weight w.val = 4) (hf : weight f.val = 6)
    (hq : ∀ a, evenRepresentation a.val w = w → ∃ x, q x = a) :
    ∃ x : H, x ∈ pResidual 2 H ∧ evenRepresentation (q x).val f ≠ f := by
  obtain ⟨a, ha, haw, haf⟩ := exists_cubic_weight_four_mover w f hw hf
  obtain ⟨x, hx⟩ := hq a haw
  let ar : q.range := ⟨a, ⟨x, hx⟩⟩
  have har : ar ^ 3 = 1 := Subtype.ext ha
  have hr : ar ∈ pResidual 2 q.range :=
    mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one har))
  rw [← map_pResidual_of_surjective 2 q.rangeRestrict q.rangeRestrict_surjective] at hr
  obtain ⟨y, hy, he⟩ := mem_map.mp hr
  refine ⟨y, hy, ?_⟩
  have he' : q y = a := congrArg Subtype.val he
  simpa only [he'] using haf
end BinarySevenCode
