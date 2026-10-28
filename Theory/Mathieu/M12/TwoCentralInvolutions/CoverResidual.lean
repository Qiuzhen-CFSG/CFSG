module

public import Theory.GroupTheory.PerfectCentralCoverFixedResidual
public import Theory.Mathieu.M12.Properties.Simplicity
public import Theory.Mathieu.M12.GoldschmidtFullG2Obstruction

/-!
# Excluding small fixed residuals in central covers of M₁₂

A two-central involution centralizer in the actual M₁₂ carrier has
two-residual of order 96. Faithful automorphism descent and residual
surjectivity carry this lower bound to every perfect central two-cover.
An inner involution fixing a Sylow subgroup therefore cannot have
fixed-subgroup two-residual of order at most 48.

The actual component application is RecognitionFixedResidual in Chapter14.
Source: Aschbacher--Smith 14.3.22, printed p.999, model inspection.
-/

public section
open Subgroup
namespace Sporadic.Mathieu
open PerfectCentralCovering
variable {E : Type*} [Group E] [Finite E]
theorem no_mathieuTwelve_cover_of_small_fixedResidual (f : Cover E M12)
    (hk : f.toMonoidHom.ker = center E) (hp : IsPGroup 2 f.toMonoidHom.ker)
    (α : MulAut E) (hα : orderOf α = 2)
    (hi : ∃ x, α = MulAut.conj x) (P : Sylow 2 E)
    (hfix : ∀ x : P, α (x : E) = x)
    (hsmall : Nat.card (pResidual 2 α.fixedSubgroup) ≤ 48) : False := by
  let := m12_isSimpleGroup
  let := f.isPerfect
  let : Group.IsPerfect M12 := Group.IsPerfect.ofSurjective f.surjective
  obtain ⟨t,ht,hc,hd⟩ := f.exists_twoCentral_fixedResidual_dvd hk hp
    (center_eq_bot_of_simple_perfect) α hα hi P hfix
  rw [M12FullG2Obstruction.residual_card_centralizer_of_twoCentral t ht hc] at hd
  have := Nat.le_of_dvd (Nat.card_pos : 0 < Nat.card (pResidual 2 α.fixedSubgroup)) hd
  omega
end Sporadic.Mathieu
