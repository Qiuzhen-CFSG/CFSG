module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.FullAutomizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual

/-!
# The source prime residual on the full automizer

Restrict O^{p′} from M=N_G(L) to N_G(V), then map it through the
surjective literal action homomorphism. The exact 11.0.4 residual equality
places every p-power actor in the component image. This avoids the false
assumption that a quotient element of order p has an order-p lift.
LinearOdd uses the result to exclude the source diagonal actors.

Source: Aschbacher--Smith, 11.0.4 and 11.2.2(2), printed pp.760,768.
-/

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- The source prime residual survives passage from the original normalizer
to its literal action image, without lifting quotient actors to the same order. -/
theorem automizer_primeResidual_le_layer {p : ℕ} (hp : p.Prime)
    (hc : Preliminary.SourcePrime D S p) :
    primeToResidual p (Automizer V) ≤ inducedAutomizer V L := by
  let : Fact p.Prime := ⟨hp⟩
  let N := normalizer (V : Set G)
  let M := normalizer (L : Set G)
  let q := V.normalizerMonoidHom.rangeRestrict
  have hNM : N ≤ M := seed_normalizer_le D S
  rw [← map_primeToResidual_of_surjective p q V.normalizerMonoidHom.rangeRestrict_surjective]
  rintro a ⟨x,hx,rfl⟩
  have hMx : inclusion hNM x ∈ primeToResidual p M :=
    map_primeToResidual_le_of_hom p (inclusion hNM) (mem_map_of_mem _ hx)
  have hxL : (x : G) ∈ L := by
    rw [Preliminary.prime_residual D S hp hc]
    exact ⟨inclusion hNM x,hMx,rfl⟩
  exact ⟨x,hxL,rfl⟩

/-- Actual p-power actors in the full automizer are inner for the source
prime ranges. No assertion about arbitrary linear normalizers is used. -/
theorem automizer_primePower_mem_layer {p k : ℕ} (hp : p.Prime)
    (hc : Preliminary.SourcePrime D S p) {a : Automizer V}
    (ha : a ^ (p ^ k) = 1) : a ∈ inducedAutomizer V L :=
  automizer_primeResidual_le_layer D S hp hc (mem_primeToResidual_of_pow ha)

/-- The odd-prime fixed-space calculation may therefore use the actual
component model whenever the prime is in the range of 11.0.4. -/
theorem automizer_orderPrime_mem_layer {p : ℕ} (hp : p.Prime)
    (hc : Preliminary.SourcePrime D S p) {a : Automizer V}
    (ha : orderOf a = p) : a ∈ inducedAutomizer V L := by
  apply automizer_primePower_mem_layer D S hp hc (k := 1)
  simpa only [pow_one, ← ha] using pow_orderOf_eq_one a

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer
