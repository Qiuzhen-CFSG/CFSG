module
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Characteristic kernels of the actual constituent models

The kernel of a center-free image of a quasisimple characteristic quotient
is the preimage of that quotient's center. It is therefore characteristic,
and remains so under both source and model coordinates. This lets the
chosen-seed sieve use automorphisms of the literal component image.

Source: Aschbacher--Smith A.3.3 and the B.4.2 sieve in D.3.5(5),
combined manuscript of 1 March 2004, printed pp.42 and195--196.
The actual consumer is `SeedAlternativesMovedSylowSieve`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {A B C E : Type*} [Group A] [Group B] [Group C] [Group E]

theorem center_eq_bot_of_model_equiv (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply bot_unique
  intro x hx
  apply mem_bot.mpr
  apply e.injective
  rw [map_one]
  apply mem_bot.mp (hz.le ?_)
  apply mem_center_iff.mpr
  intro y
  obtain ⟨y,rfl⟩ := e.surjective y
  simpa only [map_mul] using congrArg e (mem_center_iff.mp hx y)

/-- A center-free image of a quasisimple characteristic quotient has
characteristic kernel, with the original quotient map retained. -/
theorem kernel_characteristic_of_quasisimple_quotient
    (N : Subgroup A) [N.Characteristic] [IsQuasisimple (A ⧸ N)] [Nontrivial B]
    (f : A →* B) (q : (A ⧸ N) →* B) (hq : Function.Surjective q)
    (he : ∀ x, q (QuotientGroup.mk' N x) = f x) (hz : center B = ⊥) :
    f.ker.Characteristic := by
  have hk : q.ker = center (A ⧸ N) := by
    change (⊥ : Subgroup B).comap q = _
    rw [← hz]
    exact IsQuasisimple.comap_center_of_surjective q hq
  have hf : f.ker = (center (A ⧸ N)).comap (QuotientGroup.mk' N) := by
    rw [← hk]
    ext x
    change f x = 1 ↔ q (QuotientGroup.mk' N x) = 1
    rw [he]
  rw [hf]
  exact Characteristic.comap_quotient_mk inferInstance

/-- Relabeling the source and target preserves a characteristic kernel. -/
theorem characteristic_kernel_model_transport
    (f : A →* B) (hf : f.ker.Characteristic) (j : C ≃* A) (e : B ≃* E) :
    ((e.toMonoidHom.comp f).comp j.toMonoidHom).ker.Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  have hx' : j x ∈ f.ker := by
    change e (f (j x)) = 1 at hx
    exact e.injective (hx.trans (map_one e).symm)
  have ha := characteristic_iff_le_comap.mp hf (j.symm.trans (a.trans j)) hx'
  change f (j (a (j.symm (j x)))) = 1 at ha
  change e (f (j (a x))) = 1
  simpa only [j.symm_apply_apply,map_one] using congrArg e ha

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
