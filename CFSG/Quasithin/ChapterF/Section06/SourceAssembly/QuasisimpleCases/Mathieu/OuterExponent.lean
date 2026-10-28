module
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.OverlapExtensions.Coverage.Arithmetic
/-!
# Exponent eight for the actual outer Mathieu common Sylow

The existing checked Cayley table already interprets all 128 elements and
their powers in the original overlap. Its numeric eighth powers are zero;
the marked first-times-third generator has nontrivial fourth power.
Source: Aschbacher–Smith, F.1.12(I)(13), printed pp.262–263, and 14.2.21.
-/
public noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M12ExceptionalExtension
open Sporadic.Mathieu.M12ExceptionalExtension.OverlapExtensions
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu
private theorem outer_index_eight : ∀ i : Fin 128, Coverage.power i 8 = 0 := by
  decide +kernel
/-- Eighth powers vanish on the literal order-128 common Sylow. -/
theorem aut_m12_sylow_pow_eight (x : overlap) : x ^ 8 = 1 := by
  obtain ⟨i,rfl⟩ := Overlap.element_surjective x
  rw [← Coverage.element_power, outer_index_eight, Overlap.element_zero]
/-- The actual marked overlap contains an element of order eight. -/
theorem aut_m12_sylow_order_eight :
    orderOf (Overlap.generator 0 * Overlap.generator 2) = 8 := by
  exact orderOf_eq_prime_pow (p := 2) (n := 2)
    Coverage.generators_admissible.2.2.2.2.1.2 (aut_m12_sylow_pow_eight _)
end CFSG.Quasithin.ChapterF.SourceAssembly.Mathieu
