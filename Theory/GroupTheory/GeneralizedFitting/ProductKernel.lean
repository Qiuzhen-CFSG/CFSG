module
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Normal kernels in a product with a centerless component

Suppose F*(X) is quasisimple with trivial center. A normal subgroup of
X × A is trivial if it avoids F*(X) × 1 and meets 1 × A trivially.
Its intersection with X centralizes the component, hence vanishes by
self-centralization of F*. Commutators with X then put its first
coordinate in the same trivial centralizer, leaving only the second factor.

This isolates the group argument used for the actual quotient-action
kernel in Aschbacher–Smith 5.1.17, printed p.641 (refs/quasithin.pdf).
The finite-group input is the generalized Fitting centralizer theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement

namespace Theory.GroupTheory
variable {X A : Type*} [Group X] [Group A] [Finite X]

/-- Avoiding the centerless generalized Fitting subgroup and the other factor
forces a normal subgroup of the product to vanish. -/
theorem normal_product_eq_bot_of_fitting_and_right
    (K : Subgroup X) [K.Normal] [IsQuasisimple K]
    (hF : generalizedFitting X = K) (hZ : center K = ⊥)
    (N : Subgroup (X × A)) [N.Normal]
    (hK : ¬ K ≤ N.comap (MonoidHom.inl X A))
    (hA : ∀ a : A, (1,a) ∈ N → a = 1) : N = ⊥ := by
  let C := N.comap (MonoidHom.inl X A)
  have hcomp : IsComponent X K := ⟨(inferInstance : K.Normal).isSubnormal,inferInstance⟩
  have hCK : C ≤ centralizer (K : Set X) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      ((hcomp.normal_dichotomy C).resolve_left hK))
  have hcenter : centralizer (K : Set X) = ⊥ := by
    apply bot_unique
    intro x hx
    have hxK : x ∈ K := (hF ▸ centralizer_generalizedFitting_le X) hx
    have hz : (⟨x,hxK⟩ : K) ∈ center K :=
      mem_center_iff.mpr fun k => Subtype.ext (hx k k.property)
    simpa only [hZ,mem_bot,Subtype.ext_iff,Subgroup.coe_one] using hz
  have hC : C = ⊥ := bot_unique (hCK.trans hcenter.le)
  apply bot_unique
  rintro ⟨x,a⟩ hn
  have hx : x ∈ centralizer (K : Set X) := by
    apply mem_centralizer_iff_commutator_eq_one'.mpr
    intro k hk
    have hc : ⁅x,k⁆ ∈ C := by
      change (⁅x,k⁆,1) ∈ N
      have hh : ⁅(x,a),(k,1)⁆ ∈ N :=
        (commutator_le_left N (⊤ : Subgroup (X × A)))
          (commutator_mem_commutator hn (mem_top _))
      change (x*k*x⁻¹*k⁻¹,a*1*a⁻¹*1⁻¹) ∈ N at hh
      simpa only [commutatorElement_def,mul_one,inv_one,mul_inv_cancel] using hh
    simpa only [hC,mem_bot] using hc
  have hx1 : x = 1 := by simpa only [hcenter,mem_bot] using hx
  subst x
  exact mem_bot.mpr (Prod.ext rfl (hA a hn))
end Theory.GroupTheory
