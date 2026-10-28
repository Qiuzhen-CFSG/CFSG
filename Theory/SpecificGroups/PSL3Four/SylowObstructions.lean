module
public import Theory.SpecificGroups.PSL3Four.SylowModel.MatrixRealization
public import Theory.SpecificGroups.PSL3Four.SylowModel.QuaternionCoordinates
public import Theory.GroupTheory.SylowCyclicDerivedSections
public import Theory.GroupTheory.PGroup.CyclicInvolution
/-!
# Sylow obstructions for PSL₃(4)

The highest-root commutators with parameters one and omega are distinct
involutions, so the Sylow derived subgroup is not cyclic. Opposite simple
root involutions do not commute. The faithful unitriangular realization
and Sylow conjugacy carry both obstructions into every actual Sylow.

Source application: Aschbacher–Smith A.3.12, pp.47–48, and 13.6.27, p.934.
-/
public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace Matrix.PSL3Four
open SylowModel
private theorem root_comm (a : F) :
    ⁅(⟨a,0,0⟩ : U),(⟨0,1,0⟩ : U)⁆ = (⟨0,0,a⟩ : U) := by
  apply U.ext
  · change ((a+0)+ -a)+ -0=0
    ring
  · change ((0+1)+ -0)+ -1=0
    ring
  · change ((0+0+a*1)+(a*0-0)+(a+0)* -0)+(0*1-0)+((a+0)+ -a)* -1=a
    ring
private theorem central_square (a : F) : (⟨0,0,a⟩ : U)^2=1 := by
  rw [pow_two]
  apply U.ext <;> simp [CharTwo.add_self_eq_zero]
private theorem derived_not_cyclic : ¬IsCyclic (commutator U) := by
  intro hc
  let := hc
  let x : commutator U := ⟨⟨0,0,1⟩, root_comm 1 ▸ commutator_mem_commutator (mem_top _) (mem_top _)⟩
  let y : commutator U := ⟨⟨0,0,omega⟩, root_comm omega ▸ commutator_mem_commutator (mem_top _) (mem_top _)⟩
  have hx : orderOf x=2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      exact central_square 1
    · intro h
      have := congrArg (fun a : commutator U => a.val.c) h
      exact one_ne_zero this
  have hy : orderOf y=2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      exact central_square omega
    · intro h
      exact omega_ne_zero (congrArg (fun a : commutator U => a.val.c) h)
  exact omega_ne_one (congrArg (fun a : commutator U => a.val.c)
    (IsCyclic.eq_of_orderOf_eq_two hy hx))
private def P : Sylow 2 PSL := Sylow.ofCard MatrixRealization.projective.range (by
  rw [← Nat.card_congr (MonoidHom.ofInjective MatrixRealization.projective_injective).toEquiv,
    card_U,card_PSL]
  decide +kernel)
private def e : U ≃* P := MonoidHom.ofInjective MatrixRealization.projective_injective

theorem sylow_derived_not_cyclic (S : Sylow 2 PSL) : ¬IsCyclic (commutator S) := by
  intro h
  exact derived_not_cyclic (derived_cyclic_of_injective
    (e.trans (P.equiv S)).toMonoidHom (e.trans (P.equiv S)).injective h)

theorem exists_noncommuting_sylow_involutions (S : Sylow 2 PSL) :
    ∃ x y : S, x^2=1 ∧ y^2=1 ∧ x*y≠y*x := by
  let a : U := ⟨1,0,0⟩
  let b : U := ⟨0,1,0⟩
  have ha : a^2=1 := by rw [pow_two]; apply U.ext <;> simp [a,CharTwo.add_self_eq_zero]
  have hb : b^2=1 := by rw [pow_two]; apply U.ext <;> simp [b,CharTwo.add_self_eq_zero]
  have hab : a*b≠b*a := by
    intro h
    have := congrArg U.c h
    simp [a,b] at this
  let d := e.trans (P.equiv S)
  refine ⟨d a,d b,?_,?_,?_⟩
  · rw [← map_pow,ha,map_one]
  · rw [← map_pow,hb,map_one]
  · intro h
    exact hab (d.injective (by simpa only [map_mul] using h))
end Matrix.PSL3Four
