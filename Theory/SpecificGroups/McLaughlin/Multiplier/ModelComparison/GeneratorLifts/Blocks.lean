module
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.GeneratorLifts.Check
/-! Bounded certificates cover the degree-275 domain in eleven blocks of 25. -/
@[expose] public section
namespace Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison

def pointBlock (b : Fin 11) (j : Fin 25) : Fin 275 :=
  ⟨25 * b.val + j.val, by omega⟩

theorem allPointBlocks (P : Fin 275 → Prop)
    (h : ∀ b j, P (pointBlock b j)) (x : Fin 275) : P x := by
  have he : pointBlock ⟨x.val / 25, by omega⟩ ⟨x.val % 25, by omega⟩ = x := by
    apply Fin.ext
    change 25 * (x.val / 25) + x.val % 25 = x.val
    omega
  exact he ▸ h _ _
end Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison
