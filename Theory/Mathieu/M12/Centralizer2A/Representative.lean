module

public import Theory.Mathieu.M12.Properties.InvolutionClasses
import all Theory.Mathieu.M12.Properties.InvolutionClasses

/-!
# Permutation specification of the marked M₁₂ 2A involution

This is an internal proof extension of `InvolutionClasses`: `import all` is
needed only to unfold its two unexposed generator elements in the proof below.
Clients receive the explicit permutation equation, without changing or exposing
those definition bodies and without rebuilding the shared involution module.
The word is the ATLAS representative used there for Aschbacher–Smith 16.1.5(4).
-/

public section
namespace Sporadic.Mathieu.M12Centralizer2A

private theorem first_generator_coe :
    (m12AInvolution : Equiv.Perm (Fin 12)) = m12GeneratorA := rfl

private theorem second_generator_coe :
    (m12BElement : Equiv.Perm (Fin 12)) = m12GeneratorB := rfl

/-- The literal permutation of the existing, marked 2A involution. -/
theorem representative_coe : (m12Involution2A : Equiv.Perm (Fin 12)) =
    (m12GeneratorA * m12GeneratorB * m12GeneratorA * m12GeneratorB *
      m12GeneratorA * m12GeneratorB * m12GeneratorB) ^ 3 := by
  simp only [m12Involution2A, Subgroup.coe_pow, Subgroup.coe_mul,
    first_generator_coe, second_generator_coe]

end Sporadic.Mathieu.M12Centralizer2A
