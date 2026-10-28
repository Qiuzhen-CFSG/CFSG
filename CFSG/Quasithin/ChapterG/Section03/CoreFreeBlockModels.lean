module

public import CFSG.Quasithin.ChapterG.Section03.Recognition.Reduced.Blocks

/-!
# Marked block factors without a spanning hypothesis

The kernel of the action of a canonical block group on its own block lies in
the two-core of the original acting group. A trivial ambient two-core therefore
makes every full block action faithful, even when the center orbit does not
span the original module. The internal group decomposition then identifies
the generated group with the product of the full linear groups on the literal
blocks, preserving each original block inclusion.

Source application: Aschbacher--Smith 12.7.18, printed p.845.
-/

public noncomputable section
open Subgroup BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Triviality of the ambient two-core replaces the spanning hypothesis in the
marked product of the actual canonical block actions. -/
theorem core_free_block_models
    {H : Subgroup (BinaryLinear.GL V)} [Finite H] {Δ : Set V}
    (h : Hypotheses H Δ) (hcore : pCore 2 H = ⊥)
    (hf : FullAction H Δ) (hd : Decomposition H Δ) :
    ∃ e : ∀ i : OrbitBlock H Δ,
        blockGroup H Δ i ≃* BinaryLinear.GL (blockSpace H Δ i),
      (∀ i, (e i).toMonoidHom = spanAction H i.val) ∧
      ∃ E : (∀ i : OrbitBlock H Δ, BinaryLinear.GL (blockSpace H Δ i)) ≃*
          generated H Δ,
        ∀ i (g : blockGroup H Δ i),
          (E (by classical exact Pi.mulSingle i (e i g)) : BinaryLinear.GL V) =
          (g : BinaryLinear.GL V) := by
  classical
  let e (i : OrbitBlock H Δ) := MulEquiv.ofBijective (spanAction H i.val)
    ⟨Reduced.blockAction_injective h hcore i, hf.surjective i⟩
  obtain ⟨F, hF⟩ := hd.group_equiv
  let E := (MulEquiv.piCongrRight (fun i => (e i).symm)).trans F
  refine ⟨e, fun _ => rfl, E, ?_⟩
  intro i g
  have he : (MulEquiv.piCongrRight (fun j => (e j).symm))
      (Pi.mulSingle i (e i g)) = singleGroupElement i g := by
    funext j
    by_cases hij : i = j
    · subst j
      simp only [MulEquiv.piCongrRight_apply, singleGroupElement, Pi.mulSingle_eq_same]
      exact (e i).symm_apply_apply g
    · simp [singleGroupElement, Pi.mulSingle_eq_of_ne (Ne.symm hij)]
      rfl
  change (F ((MulEquiv.piCongrRight (fun j => (e j).symm))
    (Pi.mulSingle i (e i g))) : BinaryLinear.GL V) = _
  rw [he]
  exact hF i g

end CFSG.Quasithin.ChapterG.Section03
