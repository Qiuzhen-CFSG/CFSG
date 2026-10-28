module

public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.Models
public import Theory.GroupTheory.ReducedNormal.SubspaceGroupConsequences

/-!
# Distinct module types in the moved chosen-seed orbit

A multiplicative equivalence of the literal subgroup conjugation modules
is binary linear in their reduced-module coordinates. It identifies their
fixed spaces, so it descends to the original fixed-space images. Homogeneous
selection then makes isomorphic conjugates equal as actual subgroups. Thus
moving the seed forces nonisomorphism for the unchanged actor.

The quotient transport adapts the private `same_central_images` proof in
`Theory/Representation/BinaryOffender/Homogeneous/NaturalFive.lean`.
The actual chosen-module application is `SeedAlternativesMovedGeometry`.
This proves the nonisomorphism clause used in D.3.10; it does not classify
the constituent or assert that its Sylow orbit has exactly two summands.

Source: Aschbacher--Smith A.1.40--42 and D.3.10--11, combined manuscript
of 1 March 2004, printed pp.31--32 and201.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325

variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

private theorem same_central_images (ρ : Representation (ZMod 2) G W)
    (X : Subgroup G) (I J : Submodule (ZMod 2) W)
    (hI : X ≤ subspaceStabilizer ρ I) (hJ : X ≤ subspaceStabilizer ρ J)
    (e : I ≃ₗ[ZMod 2] J)
    (he : ∀ (x : X) v, e ((invariantSubspace ρ X I hI).toRepresentation x v) =
      (invariantSubspace ρ X J hJ).toRepresentation x (e v)) :
    SameModule (quotientImage ρ X I hI) (quotientImage ρ X J hJ) := by
  let CI := (fixedSpace ρ X).comap I.subtype
  let CJ := (fixedSpace ρ X).comap J.subtype
  have hf : CI.map e.toLinearMap = CJ := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩ x
      have hv' : (invariantSubspace ρ X I hI).toRepresentation x v = v :=
        Subtype.ext (hv x)
      exact congrArg Subtype.val ((he x v).symm.trans (congrArg e hv'))
    · intro hw
      refine ⟨e.symm w, ?_, e.apply_symm_apply w⟩
      intro x
      have hh : (invariantSubspace ρ X I hI).toRepresentation x (e.symm w) = e.symm w := by
        apply e.injective
        exact (he x (e.symm w)).trans (by
          rw [e.apply_symm_apply]
          exact Subtype.ext (hw x))
      exact congrArg (fun u : I => (u : W)) hh
  let qE := Submodule.Quotient.equiv CI CJ e hf
  have hq (x : X) (v : centralQuotient ρ X I) :
      qE (centralQuotientRepresentation ρ X I hI x v) =
        centralQuotientRepresentation ρ X J hJ x (qE v) := by
    induction v using Submodule.Quotient.induction_on with
    | _ v =>
      change Submodule.Quotient.mk (e ((invariantSubspace ρ X I hI).toRepresentation x v)) =
        Submodule.Quotient.mk ((invariantSubspace ρ X J hJ).toRepresentation x (e v))
      exact congrArg (fun u : J => (Submodule.Quotient.mk u : J ⧸ CJ)) (he x v)
  let ei := centralQuotientImageEquiv ρ X I
  let ej := centralQuotientImageEquiv ρ X J
  refine ⟨ei.symm.trans (qE.trans ej), ?_⟩
  intro x v
  obtain ⟨w, rfl⟩ := ei.surjective v
  change ej (qE (ei.symm ((quotientImage ρ X I hI).toRepresentation x (ei w)))) =
    (quotientImage ρ X J hJ).toRepresentation x (ej (qE (ei.symm (ei w))))
  rw [← centralQuotientImageEquiv_equivariant, ei.symm_apply_apply,
    ei.symm_apply_apply, hq, centralQuotientImageEquiv_equivariant]

open Theory.GroupTheory.ReducedNormal

set_option backward.isDefEq.respectTransparency false in
/-- The literal subgroup module equivalence induces equivalence of the
original fixed-space images, retaining the original actor X. -/
theorem same_central_images_of_sameConjugationModule
    (H X : Subgroup G) (_hXH : X ≤ H)
    (I J : Submodule (ZMod 2) (Additive (ModuleGroup H)))
    (hI : X.subgroupOf H ≤ subspaceStabilizer (representation H) I)
    (hJ : X.subgroupOf H ≤ subspaceStabilizer (representation H) J)
    (he : SameConjugationModule X (subspaceImage H I) (subspaceImage H J)) :
    SameModule (quotientImage (representation H) (X.subgroupOf H) I hI)
      (quotientImage (representation H) (X.subgroupOf H) J hJ) := by
  obtain ⟨f,hf⟩ := he
  let a : Additive (subspaceImage H I) ≃ₗ[ZMod 2] Additive (subspaceImage H J) :=
    { f.toAdditive with map_smul' := ZMod.map_smul f.toAdditive }
  let e := (subspaceEquiv H I).trans (a.trans (subspaceEquiv H J).symm)
  apply same_central_images (representation H) (X.subgroupOf H) I J hI hJ e
  intro x v
  apply (subspaceEquiv H J).injective
  have hm (w : I) : subspaceEquiv H J (e w) = a (subspaceEquiv H I w) :=
    (subspaceEquiv H J).apply_symm_apply _
  apply Additive.toMul.injective
  apply Subtype.ext
  have hequiv := hf ⟨x.val.val, x.property⟩
    (subspaceEquiv H I v).toMul
    (subspaceEquiv H I ((invariantSubspace (representation H)
      (X.subgroupOf H) I hI).toRepresentation x v)).toMul rfl
  rw [hm]
  change (f (subspaceEquiv H I _).toMul : G) =
    x.val.val * (e v).val.toMul.val.val * x.val.val⁻¹
  rw [hequiv]
  have hm' := congrArg (fun w : Additive (subspaceImage H J) => w.toMul.val) (hm v)
  exact congrArg (fun z : G => x.val.val * z * x.val.val⁻¹) hm'.symm

/-- Homogeneity forces isomorphic conjugates to coincide as actual
subgroups. In particular every moved conjugate has a different X-module
isomorphism type, without twisting X by the conjugator. -/
theorem homogeneous_conjugate_eq_of_sameConjugationModule
    (H X : Subgroup G) (hXH : X ≤ H) (R : Subgroup H)
    (I : Submodule (ZMod 2) (Additive (ModuleGroup H)))
    (hI : IsIrrPlusWith (representation H) (X.subgroupOf H) R I) (t : R)
    (he : SameConjugationModule X (subspaceImage H I)
      ((subspaceImage H I).map (MulAut.conj (t.val.val)).toMonoidHom)) :
    (subspaceImage H I).map (MulAut.conj (t.val.val)).toMonoidHom = subspaceImage H I := by
  have hJ := hI.isIrrPlus.map_normalizer (representation H) (hI.normalizes t.property)
  have he' : SameConjugationModule X (subspaceImage H I)
      (subspaceImage H (I.map (representation H t.val))) := by
    rwa [subspaceImage_map]
  have hs := hI.eq_of_isomorphic_conjugate (representation H) t
    (same_central_images_of_sameConjugationModule H X hXH I _ hI.invariant hJ.choose he')
  have hm := congrArg (subspaceImage H) hs
  rwa [subspaceImage_map] at hm

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
