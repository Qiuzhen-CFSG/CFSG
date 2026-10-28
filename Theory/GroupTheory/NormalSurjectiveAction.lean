module
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Ambient conjugation on a characteristic-kernel image

A surjection from a normal subgroup with characteristic kernel identifies
its image with a characteristic quotient. Conjugation therefore descends
canonically, agrees with the given map on conjugates, and contains all inner
automorphisms of the image.

This is the action transport used in Aschbacher--Smith 14.2.12--13.
-/

public section
open Subgroup
namespace Subgroup
variable {X D : Type*} [Group X] [Group D]

@[expose] noncomputable def normalSurjectiveAction (L : Subgroup X) [L.Normal]
    (f : L →* D) (hf : Function.Surjective f) [f.ker.Characteristic] :
    X →* MulAut D :=
  (MulAut.congr (QuotientGroup.quotientKerEquivOfSurjective f hf)).toMonoidHom.comp
    (normalQuotientAction L f.ker)

theorem normalSurjectiveAction_apply (L : Subgroup X) [L.Normal]
    (f : L →* D) (hf : Function.Surjective f) [f.ker.Characteristic]
    (x : X) (l : L) :
    normalSurjectiveAction L f hf x (f l) = f (MulAut.conjNormal x l) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have he (l : L) : e (QuotientGroup.mk' f.ker l) = f l := rfl
  change e (normalQuotientAction L f.ker x (e.symm (f l))) = _
  rw [← he l, e.symm_apply_apply, normalQuotientAction_apply_mk]
  rfl

theorem normalSurjectiveAction_inner (L : Subgroup X) [L.Normal]
    (f : L →* D) (hf : Function.Surjective f) [f.ker.Characteristic] (l : L) :
    normalSurjectiveAction L f hf (l : X) = MulAut.conj (f l) := by
  ext d
  obtain ⟨a,rfl⟩ := hf d
  rw [normalSurjectiveAction_apply]
  change f (l * a * l⁻¹) = f l * f a * (f l)⁻¹
  simp only [map_mul,map_inv]

theorem inner_le_normalSurjectiveAction_range (L : Subgroup X) [L.Normal]
    (f : L →* D) (hf : Function.Surjective f) [f.ker.Characteristic] :
    MulAut.innerSubgroup D ≤ (normalSurjectiveAction L f hf).range := by
  rintro _ ⟨d,rfl⟩
  obtain ⟨l,rfl⟩ := hf d
  exact ⟨l,normalSurjectiveAction_inner L f hf l⟩
end Subgroup
