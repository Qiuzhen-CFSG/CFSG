module
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Stellmacher.OmegaOneCenterMap
public import Theory.Representation.BinaryOffender.Defs

/-!
# Bounding a central seed by a marked Sylow fixed space

If a Sylow two-subgroup normalizes a component, its intersection with the
component is Sylow there. An equivariant surjective component action
therefore sends every element of a contained omega-center into the fixed
space of a genuine Sylow image. The marked module isomorphism makes this
an injection, giving the cardinal bound without changing the action map.

Source application: Aschbacher--Smith 13.4.7(3), printed p.903, excluding
the natural A₆ module when the original central seed has order four.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender
namespace Representation
variable {G H M : Type*} [Group G] [Finite G] [Group H]
  [AddCommGroup M] [Module (ZMod 2) M] [Finite M]

/-- A contained omega-center injects into the fixed space of the actual
Sylow image on a marked component module. -/
theorem omega_card_le_fixed
    (T : Sylow 2 G) (C U : Subgroup G)
    (hTC : (T : Subgroup G) ≤ normalizer (C : Set G))
    (hCU : C ≤ normalizer (U : Set G))
    (hZU : omegaOneCenterAmbient (T : Subgroup G) ≤ U)
    (q : C →* H) (hq : Function.Surjective q)
    (ρ : Representation (ZMod 2) H M) (e : U ≃* Multiplicative M)
    (he : ∀ (c : C) (v : U),
      (e (U.normalizerMonoidHom ⟨c.val,hCU c.property⟩ v)).toAdd =
        ρ (q c) (e v).toAdd) :
    ∃ S : Sylow 2 H, (S : Subgroup H) = ((T : Subgroup G).subgroupOf C).map q ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) ≤
        Nat.card (fixedSpace ρ (S : Subgroup H)) := by
  obtain ⟨R,hR⟩ := Subgroup.NormalSylowQuotientAction.intersection_sylow T C hTC
  let S := R.mapSurjective hq
  have hS : (S : Subgroup H) = ((T : Subgroup G).subgroupOf C).map q := by
    change (R : Subgroup C).map q = _
    rw [hR]
  refine ⟨S,hS,?_⟩
  let f : omegaOneCenterAmbient (T : Subgroup G) → fixedSpace ρ (S : Subgroup H) :=
    fun z => ⟨(e ⟨z.val,hZU z.property⟩).toAdd,by
      intro a
      obtain ⟨c,hc,hca⟩ := hS.le a.property
      have hh := he c ⟨z.val,hZU z.property⟩
      have hzfix : U.normalizerMonoidHom ⟨c.val,hCU c.property⟩
          ⟨z.val,hZU z.property⟩ = ⟨z.val,hZU z.property⟩ := by
        apply Subtype.ext
        rw [normalizerMonoidHom_apply_apply_coe]
        exact mul_inv_eq_iff_eq_mul.mpr
          (((mem_omegaOneCenterAmbient_iff _ _).mp z.property).2.2 c.val hc)
      rw [hzfix,hca] at hh
      exact hh.symm⟩
  apply Nat.card_le_card_of_injective f
  intro x y hxy
  apply Subtype.ext
  have hh := congrArg (fun z : fixedSpace ρ (S : Subgroup H) => z.val) hxy
  exact congrArg (fun u : U => u.val) (e.injective hh)

end Representation
