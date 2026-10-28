module

public import Theory.Representation.BinaryTransvectionGroups.Duality

/-!
# Faithfulness from a full radical image

Evaluation at a vector outside a proper axis maps its full radical onto the
axis. When the actor is equinumerous with the axis, this surjection is
injective, hence so is the action. This removes a redundant faithfulness
premise from the H.15.2-to-H.16.4 duality step (pp.399,403).
-/

@[expose] public section
noncomputable section
namespace MathieuCode.Hexad.ChiefFlag.Actions
variable {G X : Type*} [Group G] [Finite G] [AddCommGroup X] [Module (ZMod 2) X]

/-- Evaluation away from the axis proves faithfulness when the full radical
and the actor have the same carrier size, witnessed by an actual equivalence. -/
theorem faithful_of_full_radical (ρ : G →* BinaryLinear.GL X)
    (P : Submodule (ZMod 2) X) (hP : P ≠ ⊤) (e : G ≃ P)
    (hfull : ρ.range = BinaryLinear.radical P) : Function.Injective ρ := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : X, v ∉ P := by
    by_contra! hn
    exact hP (top_unique (fun x _ => hn x))
  have ha (g : G) : ρ g ∈ BinaryLinear.radical P := by
    rw [← hfull]
    exact ⟨g, rfl⟩
  let f : G → P := fun g => ⟨ρ g v - v, (ha g).2 v⟩
  have hs : Function.Surjective f := by
    intro w
    obtain ⟨l, hlv, hlP⟩ := P.exists_le_ker_of_notMem hv
    have hl1 : l v = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hlv
    have ht := BinaryLinear.transvection_mem w.property hlP
    rw [← hfull] at ht
    obtain ⟨g, hg⟩ := ht
    refine ⟨g, Subtype.ext ?_⟩
    change ρ g v - v = w.val
    rw [hg]
    change (v + l v • w.val) - v = w.val
    rw [hl1, one_smul, add_sub_cancel_left]
  have hf : Function.Injective f := (Finite.injective_iff_surjective_of_equiv e).mpr hs
  intro a b he
  apply hf
  apply Subtype.ext
  exact congrArg (fun t : BinaryLinear.GL X => t v - v) he

end MathieuCode.Hexad.ChiefFlag.Actions
