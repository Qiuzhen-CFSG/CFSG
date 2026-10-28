module

public import CFSG.Quasithin.ChapterG.Section03.Source
import Mathlib.Algebra.Module.Submodule.EqLocus

/-!
# Marked linear factors for a spanning G.3 decomposition

Each block group fixes the other summands pointwise. When the center orbit
spans the original space, its restriction to its own block is therefore
faithful. The full-action conclusion identifies it with the full linear
group, and the internal group decomposition becomes a marked product of
these linear groups.

Source application: Aschbacher--Smith12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The factor isomorphisms and their product preserve the literal block
actions and every original block inclusion. -/
theorem spanning_block_models
    {H : Subgroup (BinaryLinear.GL V)} {Δ : Set V}
    (hf : FullAction H Δ) (hd : Decomposition H Δ)
    (hspan : Submodule.span (ZMod 2) Δ = ⊤) :
    ∃ e : ∀ i : OrbitBlock H Δ,
        blockGroup H Δ i ≃* BinaryLinear.GL (blockSpace H Δ i),
      (∀ i, (e i).toMonoidHom = spanAction H i.val) ∧
      ∃ E : (∀ i : OrbitBlock H Δ, BinaryLinear.GL (blockSpace H Δ i)) ≃*
          generated H Δ,
        ∀ i (g : blockGroup H Δ i),
          (E (by classical exact Pi.mulSingle i (e i g)) : BinaryLinear.GL V) =
          (g : BinaryLinear.GL V) := by
  classical
  have hi (i : OrbitBlock H Δ) : Function.Injective (spanAction H i.val) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro g hg
    have hfix (v : V) (hv : v ∈ blockSpace H Δ i) : g.val v = v := by
      exact congrArg (fun a : BinaryLinear.GL (blockSpace H Δ i) =>
        (a ⟨v,hv⟩ : V)) (show spanAction H i.val g = 1 from hg)
    have hall : (⨆ j : OrbitBlock H Δ, blockSpace H Δ j) ≤
        g.val.toLinearMap.eqLocus LinearMap.id := by
      apply iSup_le
      intro j v hv
      by_cases hij : i = j
      · subst j
        exact hfix v hv
      · exact hd.cross_fix i j hij g.val g.property v hv
    rw [hd.space_span,hspan] at hall
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    exact hall (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) V))
  let e (i : OrbitBlock H Δ) := MulEquiv.ofBijective (spanAction H i.val)
    ⟨hi i,hf.surjective i⟩
  obtain ⟨F,hF⟩ := hd.group_equiv
  let E := (MulEquiv.piCongrRight (fun i => (e i).symm)).trans F
  refine ⟨e,fun _ => rfl,E,?_⟩
  intro i g
  have he : (MulEquiv.piCongrRight (fun j => (e j).symm))
      (Pi.mulSingle i (e i g)) = singleGroupElement i g := by
    funext j
    by_cases hij : i = j
    · subst j
      simp only [MulEquiv.piCongrRight_apply,singleGroupElement,Pi.mulSingle_eq_same]
      exact (e i).symm_apply_apply g
    · simp [singleGroupElement,Pi.mulSingle_eq_of_ne (Ne.symm hij)]
      rfl
  change (F ((MulEquiv.piCongrRight (fun j => (e j).symm))
    (Pi.mulSingle i (e i g))) : BinaryLinear.GL V) = _
  rw [he]
  exact hF i g

end CFSG.Quasithin.ChapterG.Section03
