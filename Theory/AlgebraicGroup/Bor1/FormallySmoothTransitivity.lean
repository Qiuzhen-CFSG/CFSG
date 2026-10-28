module

public import Mathlib.RingTheory.Kaehler.JacobiZariski
public import Mathlib.RingTheory.Smooth.Basic

universe u

namespace Theory.AlgebraicGroup.Bor1

open scoped TensorProduct

/-- Formal smoothness descends through a formally smooth intermediate algebra
when the base-change map on Kahler differentials is split injective. -/
public theorem formallySmooth_of_split_mapBaseChange
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallySmooth R S] [Algebra.FormallySmooth R T]
    (hsplit : ∃ l : Ω[T⁄R] →ₗ[T] T ⊗[S] Ω[S⁄R],
      l.comp (KaehlerDifferential.mapBaseChange R S T) = LinearMap.id) :
    Algebra.FormallySmooth S T := by
  let i := KaehlerDifferential.mapBaseChange R S T
  let q := KaehlerDifferential.map R S T T
  have hi : Function.Injective i := by
    obtain ⟨l, hl⟩ := hsplit
    exact Function.HasLeftInverse.injective ⟨l, LinearMap.congr_fun hl⟩
  have hq : Function.Surjective q :=
    KaehlerDifferential.map_surjective R S T
  have hexact : Function.Exact i q :=
    KaehlerDifferential.exact_mapBaseChange_map R S T
  obtain ⟨s, hs⟩ :=
    ((hexact.split_tfae hi hq).out 1 0).mp hsplit
  refine ⟨Module.Projective.of_split s q hs, ?_⟩
  constructor
  intro x y
  have hdeltaZero : Algebra.H1Cotangent.δ R S T = 0 := by
    rw [← LinearMap.range_eq_bot]
    rw [← (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T).linearMap_ker_eq]
    exact LinearMap.ker_eq_bot.mpr hi
  have hdeltaInjective : Function.Injective (Algebra.H1Cotangent.δ R S T) := by
    rw [← LinearMap.ker_eq_bot]
    rw [(Algebra.H1Cotangent.exact_map_δ R S T).linearMap_ker_eq]
    apply LinearMap.range_eq_bot.mpr
    apply LinearMap.ext
    intro z
    rw [Subsingleton.elim z 0]
    exact map_zero _
  apply hdeltaInjective
  rw [hdeltaZero]
  rfl

end Theory.AlgebraicGroup.Bor1
