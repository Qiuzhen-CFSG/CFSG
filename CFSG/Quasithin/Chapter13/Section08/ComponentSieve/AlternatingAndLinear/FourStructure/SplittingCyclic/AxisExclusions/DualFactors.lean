module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions.Duality

/-!
# Chief factors of the contragredient module

For an invariant interval `A ≤ B` in the dual module, evaluation identifies
`B/A` with the dual of `Aᗮ/Bᗮ` in the original module. Its kernel is exactly
`A`, by double annihilation. Every functional on the reversed section extends
to the ambient space, proving surjectivity. Evaluation also intertwines the
actual quotient actions, with the inverse in the contragredient convention.

The annihilator order isomorphism reverses chief intervals. Thus compatible
natural-or-dual chief-factor identifications pass to the dual, with the same
identification of the actor with GL₄(2). Centrality of a dual chief factor
would imply centrality of the reversed original factor, since functionals
separate vectors; hence the absence of central factors passes as well.

This supplies the chief-factor hypothesis for the dual use of B.4.9(1) in
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
of 1 March 2004, 13.8.25, printed p.961 (PDF p.978).
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions

variable {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) H U)

private def sectionFunctional (A B : Subrepresentation ρ.dual) :
    B.toSubmodule →ₗ[ZMod 2]
      Module.Dual (ZMod 2) ((coannihilator ρ A).toSubmodule ⧸
        (sectionLower ρ (coannihilator ρ B) (coannihilator ρ A)).toSubmodule) where
  toFun f := (sectionLower ρ (coannihilator ρ B) (coannihilator ρ A)).toSubmodule.liftQ
    (f.val.comp (coannihilator ρ A).toSubmodule.subtype) (by
      intro x hx
      exact ((Submodule.mem_dualCoannihilator _).mp hx) f f.property)
  map_add' f g := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x => rfl
  map_smul' c f := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x => rfl

private def sectionDualMap (A B : Subrepresentation ρ.dual) :=
  (sectionLower ρ.dual A B).toSubmodule.liftQ (sectionFunctional ρ A B) (by
    intro f hf
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x => exact ((Submodule.mem_dualCoannihilator _).mp x.property) f hf)

variable [FiniteDimensional (ZMod 2) U]

private theorem sectionDualMap_injective (A B : Subrepresentation ρ.dual) :
    Function.Injective (sectionDualMap ρ A B) := by
  apply (LinearMap.ker_eq_bot).mp
  apply bot_unique
  intro q hq
  change q = 0
  induction q using Submodule.Quotient.induction_on with
  | _ f =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    change (f : Module.Dual (ZMod 2) U) ∈ A
    rw [← annihilator_coannihilator ρ A]
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro x hx
    exact LinearMap.congr_fun hq
      ((sectionLower ρ (coannihilator ρ B) (coannihilator ρ A)).toSubmodule.mkQ ⟨x, hx⟩)

private theorem sectionDualMap_surjective (A B : Subrepresentation ρ.dual) (hAB : A ≤ B) :
    Function.Surjective (sectionDualMap ρ A B) := by
  intro φ
  let K := coannihilator ρ A
  let L := coannihilator ρ B
  let Q := (sectionLower ρ L K).toSubmodule
  obtain ⟨f, hf⟩ := (Subspace.dualRestrict_surjective (W := K.toSubmodule))
    (φ.comp Q.mkQ)
  have hfB : f ∈ B := by
    rw [← annihilator_coannihilator ρ B]
    apply (Submodule.mem_dualAnnihilator _).mpr
    intro x hx
    have hxK : x ∈ K := (Submodule.mem_dualCoannihilator _).mpr
      (fun a ha => ((Submodule.mem_dualCoannihilator _).mp hx) a (hAB ha))
    have he := LinearMap.congr_fun hf ⟨x, hxK⟩
    change f x = φ (Q.mkQ ⟨x, hxK⟩) at he
    rw [he, show Q.mkQ ⟨x, hxK⟩ = 0 from (Submodule.Quotient.mk_eq_zero Q).mpr hx,
      map_zero]
  refine ⟨Submodule.Quotient.mk ⟨f, hfB⟩, ?_⟩
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ x => exact LinearMap.congr_fun hf x

/-- Evaluation identifies `B/A` with the dual of `Aᗮ/Bᗮ`. The two sections
use the coannihilators in the original representation. -/
noncomputable def coannihilatorSectionEquiv
    (A B : Subrepresentation ρ.dual) (hAB : A ≤ B) :
    (sectionRepresentation ρ.dual A B).Equiv
      (sectionRepresentation ρ (coannihilator ρ B) (coannihilator ρ A)).dual :=
  Representation.Equiv.mk
    (LinearEquiv.ofBijective (sectionDualMap ρ A B)
      ⟨sectionDualMap_injective ρ A B, sectionDualMap_surjective ρ A B hAB⟩) (fun g => by
        apply LinearMap.ext
        intro q
        induction q using Submodule.Quotient.induction_on with
        | _ f =>
          apply LinearMap.ext
          intro s
          induction s using Submodule.Quotient.induction_on with
          | _ x => rfl)

/-- The section equivalence is the actual evaluation pairing on representatives. -/
@[simp] theorem coannihilatorSectionEquiv_apply_mk
    (A B : Subrepresentation ρ.dual) (hAB : A ≤ B)
    (f : B.toSubmodule) (x : (coannihilator ρ A).toSubmodule) :
    coannihilatorSectionEquiv ρ A B hAB
      (Submodule.Quotient.mk f) (Submodule.Quotient.mk x) =
      f.val x := by rfl

/-- Evaluation intertwines the quotient action with the contragredient action
on the reversed section, including the inverse in that action. -/
theorem coannihilatorSectionEquiv_equivariant
    (A B : Subrepresentation ρ.dual) (hAB : A ≤ B) (g : H) : ∀ q,
    coannihilatorSectionEquiv ρ A B hAB (sectionRepresentation ρ.dual A B g q) =
      (sectionRepresentation ρ (coannihilator ρ B) (coannihilator ρ A)).dual g
        (coannihilatorSectionEquiv ρ A B hAB q) := by
  intro q
  exact LinearMap.congr_fun ((coannihilatorSectionEquiv ρ A B hAB).isIntertwining' g) q

/-- The annihilator order isomorphism reverses every chief interval. -/
theorem coannihilator_covBy {A B : Subrepresentation ρ.dual} (hAB : A ⋖ B) :
    coannihilator ρ B ⋖ coannihilator ρ A := by
  exact (apply_covBy_apply_iff (annihilatorOrderIso ρ).symm).mpr hAB.toDual

/-- Duality preserves compatible natural-or-dual chief factors and the
absence of central chief factors. -/
theorem chiefFactorsNaturalOrDual_dual
    (eH : H ≃* BinaryLinear.GL NaturalSpace) (hchief : ChiefFactorsNaturalOrDual ρ eH) :
    ChiefFactorsNaturalOrDual ρ.dual eH := by
  intro A B hAB
  obtain ⟨hnatural, hnoncentral⟩ := hchief _ _ (coannihilator_covBy ρ hAB)
  refine ⟨naturalOrDual_of_equivariant _ _ (coannihilatorSectionEquiv ρ A B hAB.le).toLinearEquiv
    (coannihilatorSectionEquiv_equivariant ρ A B hAB.le) eH
    (naturalOrDual_dual _ eH hnatural), ?_⟩
  intro hcentral
  apply hnoncentral
  intro g v
  apply (Module.evalEquiv (ZMod 2) _).injective
  apply LinearMap.ext
  intro φ
  obtain ⟨q, rfl⟩ := (coannihilatorSectionEquiv ρ A B hAB.le).toLinearEquiv.surjective φ
  have he := coannihilatorSectionEquiv_equivariant ρ A B hAB.le g⁻¹ q
  rw [hcentral g⁻¹ q] at he
  have hev := LinearMap.congr_fun he v
  change coannihilatorSectionEquiv ρ A B hAB.le q v =
    coannihilatorSectionEquiv ρ A B hAB.le q
      (sectionRepresentation ρ (coannihilator ρ B) (coannihilator ρ A) (g⁻¹)⁻¹ v) at hev
  simpa only [inv_inv, Module.evalEquiv_apply, Module.Dual.eval_apply,
    Representation.Equiv.toLinearEquiv_apply, Representation.Equiv.coe_toIntertwiningMap]
    using hev.symm

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.AxisExclusions
