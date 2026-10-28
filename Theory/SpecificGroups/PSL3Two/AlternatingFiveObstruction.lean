module

public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.NormNum

/-!
# The alternating group of degree five does not embed in PSL₃(2)

The determinant kernel calculation gives `|SL₃(2)| = 168`. The order of its
projective quotient divides 168, whereas `|A₅| = 60` does not. Lagrange's
theorem therefore excludes an embedding of A₅ in the projective group.

This intrinsic obstruction supplies the distinction between the two concrete
group models in the final paragraph of Aschbacher–Smith, *The Classification
of Quasithin Groups*, combined manuscript (1 March 2004), §10.3, p. 757.
-/

namespace Matrix.PSL3Two

/-- The order of the concrete projective group divides 168. -/
public theorem card_PSL_dvd :
    Nat.card (ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∣ 168 := by
  rw [← card_SL]
  exact Subgroup.card_quotient_dvd_card _

/-- The alternating group of degree five cannot embed in PSL₃(2). -/
public theorem not_injective_alternatingFive
    (f : alternatingGroup (Fin 5) →* ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) :
    ¬ Function.Injective f := by
  intro hf
  have h := (Subgroup.card_dvd_of_injective f hf).trans card_PSL_dvd
  rw [nat_card_alternatingGroup] at h
  norm_num [Nat.factorial] at h

/-- In particular, the actual groups A₅ and PSL₃(2) are not isomorphic. -/
public theorem not_nonempty_alternatingFive_equiv :
    ¬ Nonempty (alternatingGroup (Fin 5) ≃*
      ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  rintro ⟨e⟩
  exact not_injective_alternatingFive e.toMonoidHom e.injective

end Matrix.PSL3Two
