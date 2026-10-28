module
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Uniqueness of invariant quadratic refinements

Two invariant quadratic forms with the same polar form have additive
difference. Its zero set is an invariant field subspace containing every
moved vector. For a nontrivial irreducible action that subspace is the whole
space. Hence a linear normalizer preserving the polar form also preserves
the invariant quadratic refinement. This extends the component-product
quadratic form to the actual symplectic normalizer in Aschbacher--Smith
G.4.9, printed pp.341--342.
-/

public section
namespace Representation.QuadraticRefinement
variable {F G V : Type*} [Field F] [Group G] [AddCommGroup V] [Module F V]

/-- For a nontrivial irreducible action, an invariant quadratic refinement of
a given polar form is unique. No perfect-field hypothesis is needed. -/
theorem invariant_eq_of_polar_eq (ρ : Representation F G V) [ρ.IsIrreducible]
    (hnon : ∃g v,ρ g v≠v)
    (Q R : QuadraticForm F V)
    (hQ : ∀g v,Q (ρ g v)=Q v) (hR : ∀g v,R (ρ g v)=R v)
    (hpolar : Q.polarBilin=R.polarBilin) : Q=R := by
  let d : V →+ F := {
    toFun v := Q v-R v
    map_zero' := by simp
    map_add' v w := by
      have h := LinearMap.congr_fun (LinearMap.congr_fun hpolar v) w
      simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar] at h
      change Q (v+w)-R (v+w) = (Q v-R v)+(Q w-R w)
      linear_combination h }
  let W : Subrepresentation ρ := {
    toSubmodule := {
      carrier := {v | d v=0}
      zero_mem' := d.map_zero
      add_mem' := by intro v w hv hw; change d (v+w)=0; rw [map_add,hv,hw,add_zero]
      smul_mem' := by
        intro c v hv
        change Q (c•v)-R (c•v)=0
        rw [Q.map_smul,R.map_smul,smul_eq_mul,smul_eq_mul,←mul_sub]
        change (c*c)*d v=0
        rw [hv,mul_zero] }
    apply_mem_toSubmodule g v hv := by
      change Q (ρ g v)-R (ρ g v)=0
      rw [hQ,hR]
      exact hv }
  have hW : W≠⊥ := by
    obtain ⟨g,v,hgv⟩ := hnon
    intro he
    have hm : ρ g v-v∈W.toSubmodule := by
      change d (ρ g v-v)=0
      rw [map_sub]
      change (Q (ρ g v)-R (ρ g v))-(Q v-R v)=0
      rw [hQ,hR,sub_self]
    rw [he] at hm
    exact hgv (sub_eq_zero.mp hm)
  have htop : W=⊤ := (IsSimpleOrder.eq_bot_or_eq_top W).resolve_left hW
  apply QuadraticMap.ext
  intro v
  have hv : v∈W.toSubmodule := by rw [htop]; trivial
  exact sub_eq_zero.mp hv

/-- An intertwining normalizer preserving the polar form preserves its unique
invariant quadratic refinement. -/
theorem normalizer_preserves (ρ : Representation F G V) [ρ.IsIrreducible]
    (hnon : ∃g v,ρ g v≠v) (Q : QuadraticForm F V)
    (hQ : ∀g v,Q (ρ g v)=Q v)
    (a : G≃*G) (t : V≃ₗ[F]V)
    (ht : ∀g v,t (ρ g v)=ρ (a g) (t v))
    (hpolar : ∀v w,Q.polarBilin (t v) (t w)=Q.polarBilin v w) :
    ∀v,Q (t v)=Q v := by
  have he : Q.comp t.toLinearMap=Q := by
    apply invariant_eq_of_polar_eq ρ hnon _ Q
    · intro g v
      change Q (t (ρ g v))=Q (t v)
      rw [ht,hQ]
    · exact hQ
    · rw [QuadraticMap.polarBilin_comp]
      ext v w
      exact hpolar v w
  exact fun v => congrArg (fun R : QuadraticForm F V=>R v) he
end Representation.QuadraticRefinement
