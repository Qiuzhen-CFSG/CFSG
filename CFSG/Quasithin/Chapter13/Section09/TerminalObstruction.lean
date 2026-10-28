module

public import Theory.GroupTheory.SolvableCentralizerConjugacy
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.SpecificGroups.PSL3Two.NonSolvable
public import Mathlib.GroupTheory.Nilpotent

/-!
# The terminal centralizer obstruction in 13.9.1

The normal two-group and the actual `S₃ × C₂` quotient in 13.9.8 imply
that `C_G(z)` is solvable. The final paragraph of 13.9.1 constructs a copy
of `PSL₃(2)` centralized by `M₁` and a conjugate of `z` in `M₁`. These
facts contradict solvability of the conjugate centralizer.

The two theorems below prove these implications. They do not assert 13.9.8
or construct the terminal copy of `PSL₃(2)`; those source premises must be
discharged when assembling Theorem 13.9.1. Normality here is inside the
literal centralizer, never in the ambient simple group.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.9.8(1)
and the final paragraph of 13.9.1, printed pp.971–974 (PDF pp.988–991).
-/

public section

namespace CFSG.Quasithin.Chapter13.Section09

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The solvability consequence of the literal quotient in 13.9.8(1). -/
theorem centralizer_solvable_of_twoGroup_quotient (z : G)
    (Q : Subgroup (centralizer ({z} : Set G))) [Q.Normal]
    (hQ : IsPGroup 2 Q)
    (e : ((centralizer ({z} : Set G)) ⧸ Q) ≃*
      (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2))) :
    Group.IsSolvable (centralizer ({z} : Set G)) := by
  let : Group.IsNilpotent Q := hQ.isNilpotent
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
  let : Group.IsSolvable ((centralizer ({z} : Set G)) ⧸ Q) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact (Group.isSolvable_iff_subgroup_quotient Q).mpr ⟨inferInstance, inferInstance⟩

/-- The final contradiction on p.974, with the earlier source outputs explicit.
The recognized subgroup and conjugacy witness refer to the original ambient G. -/
theorem false_of_terminal_model (z : G)
    (Q : Subgroup (centralizer ({z} : Set G))) [Q.Normal]
    (hQ : IsPGroup 2 Q)
    (eQ : ((centralizer ({z} : Set G)) ⧸ Q) ≃*
      (Equiv.Perm (Fin 3) × Multiplicative (ZMod 2)))
    (M₁ H : Subgroup G)
    (eH : H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (hcomm : M₁ ≤ centralizer (H : Set G))
    (hfused : ∃ x ∈ M₁, IsConj z x) : False := by
  have hH : ¬ Group.IsSolvable H := by
    intro hs
    let := hs
    exact not_isSolvable_psl3_two
      (Group.isSolvable_of_surjective (f := eH.toMonoidHom) eH.surjective)
  obtain ⟨x, hx, hzx⟩ := hfused
  exact Theory.GroupTheory.not_isConj_of_nonsolvable_subgroup_centralized H
    (centralizer_solvable_of_twoGroup_quotient z Q hQ eQ) hH (hcomm hx) hzx

end CFSG.Quasithin.Chapter13.Section09
