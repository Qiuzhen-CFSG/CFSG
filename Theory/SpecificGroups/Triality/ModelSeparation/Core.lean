module

public import Theory.SpecificGroups.Triality.ElementaryCentralKernel
public import Theory.SpecificGroups.Triality.Model.QTKE
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore

/-!
# The two-core of a quasisimple genuine triality model

The elementary-to-carrier quotient is an isomorphism in characteristic two,
by the checked elementary-center theorem. Thus any group isomorphic to the
carrier is centerless. A finite quasisimple group's two-core is central, so
it is trivial here. Quasisimplicity is inherited from the input; no independent
simplicity certification of the triality model is needed, including at q = 2.

Source: the quasisimple normal-subgroup property in GLS2, Chapter 1, and the
central-quotient convention in GLS3 2.2.6. This justifies the quotient in
Aschbacher–Smith 1.2.1(3), printed p.504 (`refs/quasithin.pdf`).
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.ModelSeparation

private theorem center_eq_bot_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hB : center B = ⊥) : center A = ⊥ := by
  apply bot_unique
  intro a ha
  apply Subgroup.mem_bot.mpr
  apply e.injective
  rw [map_one]
  apply Subgroup.mem_bot.mp
  rw [← hB]
  rw [Subgroup.mem_center_iff]
  intro b
  obtain ⟨a', rfl⟩ := e.surjective b
  simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp ha a')

/-- Inherited quasisimplicity and the proved elementary central kernel give
a trivial two-core for every genuine binary triality model. -/
theorem twoCore_eq_bot {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    {n : ℕ} (hn : 0 < n) (ht : IsTrialityGroupAt (2^n) A) : pCore 2 A = ⊥ := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff A n hn).mp ht
  let P := binaryParameters n hn
  let et : ElementaryGroup P ≃* Carrier P := MulEquiv.ofBijective (toCarrier P)
    ⟨ElementaryCentralKernel.toCarrier_injective P rfl, toCarrier_surjective P⟩
  have hA := center_eq_bot_of_equiv (e.trans et.symm) (ElementaryCentralKernel.center_eq_bot P rfl)
  exact bot_unique ((IsQuasisimple.pCore_le_center 2).trans hA.le)

end Triality.Standard.ModelSeparation
