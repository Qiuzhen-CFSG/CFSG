module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# The even centralizer of the natural point residual

The point residual is the A₄ on the first four letters. A permutation
commuting with its two displayed cubic generators fixes those four letters;
if even, it fixes the remaining two as well. Conjugation transports the
trivial centralizer intersection without changing the chosen point marking.

Source: Aschbacher–Smith 13.5.15(9), printed pp.920–921, for the literal
C_T(L₁) intersection with the ordinary A₆ local subgroup.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags

private theorem even_commuting_cycles (g : S)
    (he : g ∈ alternatingGroup (Fin 6))
    (h1 : cycle012 * g = g * cycle012) (h2 : cycle013 * g = g * cycle013) : g = 1 := by
  have hc : ∀ g : S, Equiv.Perm.sign g = 1 →
      cycle012*g=g*cycle012 → cycle013*g=g*cycle013 → g=1 := by decide +kernel
  exact hc g he h1 h2

theorem even_inf_residual_centralizer :
    alternatingGroup (Fin 6) ⊓ centralizer (K : Set S) = ⊥ := by
  apply eq_bot_iff.mpr
  rintro g ⟨he,hc⟩
  apply even_commuting_cycles g he
  · exact hc _ (by rw [K_eq_closure];exact subset_closure (by simp))
  · exact hc _ (by rw [K_eq_closure];exact subset_closure (by simp))

theorem even_inf_conjugate_residual_centralizer (a : alternatingGroup (Fin 6)) :
    alternatingGroup (Fin 6) ⊓
      centralizer (K.map (MulAut.conj a.val).toMonoidHom : Set S) = ⊥ := by
  have hh := congrArg (map (MulAut.conj a.val).toMonoidHom) even_inf_residual_centralizer
  rw [map_inf _ _ _ (MulAut.conj a.val).injective,Subgroup.map_bot] at hh
  rw [Theory.GroupTheory.map_centralizer_equiv] at hh
  have ha : (alternatingGroup (Fin 6)).map (MulAut.conj a.val).toMonoidHom =
      alternatingGroup (Fin 6) := mem_normalizer_iff_map_conj_eq.mp
        ((alternatingGroup (Fin 6)).le_normalizer a.property)
  rw [ha] at hh
  exact hh

end Theory.SpecificGroups.SymmetricSix.BinaryFlags
