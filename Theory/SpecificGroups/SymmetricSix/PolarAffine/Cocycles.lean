module

public import Theory.SpecificGroups.SymmetricSix.PolarAffine
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.Representation.FirstCohomologySymplecticFour.BinaryField

/-!
# The exact cocycle ambiguity of the alternating-six polar action

The six-letter quotient marking is retained. Its natural cocycles consist of
one principal vector and one binary multiple of the nonprincipal quadratic
defect. In particular the available nonprincipal adjustment has only one
binary parameter; this does not assert extension of arbitrary endpoint
cocycles.
-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.SymmetricSix.PolarAffine
open Representation Representation.OneCohomology
open scoped Matrix
open Representation.OneCohomology.SymplecticFour

private abbrev Derived := commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))

private def derivedEquiv : Derived ≃* A6 := by
  refine (SymplecticFour.Binary.symmetricSixEquiv.symm.subgroupMap _).trans
    (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr
    SymplecticFour.Binary.symmetricSixEquiv.symm.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

private theorem derived_action (g : Derived) (v : NaturalModule) :
    polarAction (derivedEquiv g).val v = g.val.val *ᵥ v := by
  rw [← polarRepresentation_apply]
  have hg : polarRepresentation (derivedEquiv g).val = g.val := by
    change polarRepresentation (SymplecticFour.Binary.symmetricSixEquiv.symm g.val) = _
    rw [← SymplecticFour.Binary.symmetricSixEquiv_apply]
    exact SymplecticFour.Binary.symmetricSixEquiv.apply_symm_apply _
  rw [hg]

/-- The explicit quadratic defect for the literal six-letter quotient. -/
def quadratic (g : A6) : NaturalModule :=
  quadraticCocycle.val (polarRepresentation g.val)

private theorem quadratic_derived (g : Derived) :
    quadratic (derivedEquiv g) = derivedQuadraticCocycle.val g := by
  unfold quadratic
  have hg : polarRepresentation (derivedEquiv g).val = g.val := by
    change polarRepresentation (SymplecticFour.Binary.symmetricSixEquiv.symm g.val) = _
    rw [← SymplecticFour.Binary.symmetricSixEquiv_apply]
    exact SymplecticFour.Binary.symmetricSixEquiv.apply_symm_apply _
  rw [hg]
  rfl

@[simp] theorem quadratic_one : quadratic 1 = 0 := by
  have h := quadraticCocycle.property (1 : Matrix.symplecticGroup (Fin 2) (ZMod 2)) 1
  have h0 : quadraticCocycle.val (1 : Matrix.symplecticGroup (Fin 2) (ZMod 2)) = 0 := by
    simpa using h.symm
  simpa only [quadratic, Subgroup.coe_one, map_one] using h0

/-- The quadratic defect is a crossed homomorphism for the same polar action. -/
theorem quadratic_mul (g h : A6) :
    quadratic (g*h) = polarAction g.val (quadratic h) + quadratic g := by
  have hh := quadraticCocycle.property (polarRepresentation g.val) (polarRepresentation h.val)
  simpa only [quadratic, Subgroup.coe_mul, map_mul,
    symplecticNatural_apply, polarRepresentation_apply] using hh

/-- The quadratic adjustment cannot be replaced by conjugation in the kernel. -/
theorem quadratic_not_principal :
    ¬ ∃ v : NaturalModule, ∀ g : A6, quadratic g = polarAction g.val v - v := by
  rintro ⟨v,hv⟩
  apply derivedQuadraticCocycle_not_principal (K := ZMod 2)
  refine ⟨v,Subtype.ext (funext fun g => ?_)⟩
  have hh := hv (derivedEquiv g)
  rw [quadratic_derived,derived_action] at hh
  exact hh.symm

/-- Every crossed homomorphism on the original six-letter A₆ action has exactly
one binary quadratic parameter, modulo a principal displacement. -/
theorem cocycle_normal_form (δ : A6 → NaturalModule)
    (hδ : ∀ g h, δ (g*h) = polarAction g.val (δ h) + δ g) :
    ∃ (b : ZMod 2) (v : NaturalModule),
      ∀ g, δ g = b • quadratic g + (polarAction g.val v - v) := by
  let f : cocycles (symplecticDerivedNatural (k := ZMod 2) 2) :=
    ⟨fun g => δ (derivedEquiv g),by
      intro g h
      change δ (derivedEquiv (g*h)) = g.val.val *ᵥ δ (derivedEquiv h) + δ (derivedEquiv g)
      simpa only [map_mul,derived_action] using hδ (derivedEquiv g) (derivedEquiv h)⟩
  obtain ⟨b,v,hv⟩ := BinaryField.exists_normal_form_zmod_two f
  refine ⟨b,v,fun g => ?_⟩
  obtain ⟨x,rfl⟩ := derivedEquiv.surjective g
  have hh := congrArg (fun z : cocycles (symplecticDerivedNatural (k := ZMod 2) 2) => z.val x) hv
  change δ (derivedEquiv x) = b • derivedQuadraticCocycle.val x + (x.val.val *ᵥ v - v) at hh
  simpa only [quadratic_derived,derived_action] using hh

end Theory.SpecificGroups.SymmetricSix.PolarAffine
