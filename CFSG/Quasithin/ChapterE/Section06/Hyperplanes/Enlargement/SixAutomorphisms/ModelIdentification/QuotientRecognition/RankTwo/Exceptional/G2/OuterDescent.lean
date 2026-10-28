module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientRecognition.RankTwo.Exceptional.G2
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Outer
/-!
# The genuine G₂ row of E.6.23

Actual coefficient descent discharges the outer fixed-model premise. The
existing inner parabolic calculation and the ordinary component calculation
on the smaller G₂ model now exclude an A₆ fixed component for every marked
involution. The full G₂(2) endpoint is preserved. Source: Aschbacher--Smith
E.6.23, p.254, and 16.1.4(4), p.1171.
-/
public section
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Exceptional.G2
/-- Full outer descent supplies the literal fixed-model premise in E.6.23. -/
theorem outerFixedModels : OuterFixedModels := by
  intro F _ _ n hn hc a ha hout
  obtain ⟨σ,m,_,_,_,hcard,he⟩ :=
    Atlas.G2.EvenFieldFixedResidual.outer_involution_smaller_fixed_model hn hc a ha hout
  refine ⟨Atlas.G2.EvenFieldFixedResidual.fixedField σ,inferInstance,inferInstance,?_,he⟩
  have := Finite.one_lt_card (α := Atlas.G2.EvenFieldFixedResidual.fixedField σ)
  omega
/-- Every involution of the actual binary G₂ model excludes an A₆ fixed
component, using the proved inner geometry and full outer descent. -/
theorem excludesFixedSix (F : Type) [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hc : Nat.card F = 2 ^ n) : ExcludesFixedSix (Atlas.G2.Model F) :=
  excludesFixedSix_of_outerFixedModels outerFixedModels F hn hc
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen.RankTwo.Exceptional.G2
