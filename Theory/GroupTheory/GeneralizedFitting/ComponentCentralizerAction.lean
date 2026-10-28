module

public import Theory.GroupTheory.GeneralizedFitting.ComponentInvolutionAction

/-!
# The marked centralizer action on a component

Let an embedded component have trivial ambient centralizer. The centralizer
of any nonidentity element of that component normalizes the component:
otherwise two distinct conjugate components would commute, making the marked
element central. Restricting conjugation and transporting through the given
equivalence then gives a faithful action on the component's source group.

Source application: Aschbacher--Smith, 14.3.20, printed p.998. The component
need not be normal in the ambient group.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {H X : Type*} [Group H] [Group X] {K : Subgroup H}

/-- Conjugation by the marked centralizer, transported through an explicit
equivalence onto a component with trivial ambient centralizer. -/
theorem IsComponent.exists_faithful_centralizer_action
    (hK : IsComponent H K) (e : X ≃* K)
    (hC : centralizer (K : Set H) = ⊥)
    (x : X) (hx : (e x : H) ≠ 1) :
    ∃ ρ : centralizer ({(e x : H)} : Set H) →* MulAut X,
      Function.Injective ρ ∧ ∀ c y,
        (e (ρ c y) : H) = (c : H) * (e y : H) * (c : H)⁻¹ := by
  have hxC : (e x : H) ∉ centralizer (K : Set H) := by
    rw [hC, mem_bot]
    exact hx
  have hnorm : centralizer ({(e x : H)} : Set H) ≤ normalizer (K : Set H) := by
    intro c hc
    apply hK.normalizes_of_noncentral_element ⊥ bot_le c (e x) (e x).property hxC
    exact (show Commute c (e x : H) from mem_centralizer_singleton_iff.mp hc).map
      (QuotientGroup.mk' ⊥)
  let a : centralizer ({(e x : H)} : Set H) →* MulAut K :=
    K.normalizerMonoidHom.comp (inclusion hnorm)
  let ρ : centralizer ({(e x : H)} : Set H) →* MulAut X :=
    (MulAut.congr e.symm).toMonoidHom.comp a
  have hact (c) (y) : (e (ρ c y) : H) = (c : H) * (e y : H) * (c : H)⁻¹ := by
    change (e (e.symm (a c (e y))) : H) = _
    rw [e.apply_symm_apply]
    rfl
  refine ⟨ρ, ?_, hact⟩
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  apply (eq_bot_iff_forall _).mpr
  intro c hc
  have hcC : (c : H) ∈ centralizer (K : Set H) := by
    apply mem_centralizer_iff.mpr
    rintro y hy
    obtain ⟨z, hz⟩ := e.surjective ⟨y, hy⟩
    have hzy : (e z : H) = y := congrArg Subtype.val hz
    rw [← hzy]
    have he : ρ c z = z := by
      change ρ c = 1 at hc
      rw [hc]
      rfl
    have ha := hact c z
    rw [he] at ha
    exact (mul_inv_eq_iff_eq_mul.mp ha.symm).symm
  rw [hC, mem_bot] at hcC
  exact Subtype.ext hcC

end Theory.GroupTheory
