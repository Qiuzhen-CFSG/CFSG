module
public import Theory.Representation.IrreducibleSectionGenerators
public import Theory.Representation.IrreducibleSectionPullback
public import Theory.Representation.NormalSemisimpleSpan
public import CFSG.Quasithin.ChapterD.Section02.LinearThreeSimpleTypes
public import Theory.Representation.PSL3Two.IrreducibleCatalogue

/-!
# Natural types from a normal component's seed orbit

Conjugation transports a marked natural seed through an actual automorphism
of the normal component. Its ambient conjugates are therefore simple natural
modules with potentially different group markings. If their sum contains all
component displacements, the simple-section generator theorem identifies every
noncentral simple section. Pulling back the original ambient subquotients then
gives their complete family of natural component types.

The Chapter14 NormalTypes consumer constructs the seed and orbit exhaustion
from the original terminal setup, retaining its central quotient and both
component inclusions. Source: Aschbacher--Smith14.6.22, printed p.1038.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD
open ChapterB.QuasisimpleSource
universe u
variable {D V : Type u} [Group D] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

omit [Finite V] in
private theorem natural_conjugate_marking
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal]
    (S : Subrepresentation (ρ.comp K.subtype))
    (b : K ≃* BinaryLinearThree.Group)
    (e : S.toRepresentation.Equiv (BinaryLinearThree.W.comp b.toMonoidHom)) (g : D) :
    ∃ j : K ≃* BinaryLinearThree.Group,
      Nonempty ((conjugateSubrepresentationOrderIso ρ K g S).toRepresentation.Equiv
        (BinaryLinearThree.W.comp j.toMonoidHom)) := by
  let a : MulAut K := K.normalizerMonoidHom ⟨g⁻¹,by rw [normalizer_eq_top]; trivial⟩
  let c := conjugateSubrepresentationEquiv ρ K S g⁻¹
  refine ⟨a.trans b,⟨.mk (c.toLinearEquiv.trans e.toLinearEquiv) ?_⟩⟩
  intro k
  apply LinearMap.ext
  intro v
  have hc := LinearMap.congr_fun (c.isIntertwining' k) v
  exact (congrArg e.toLinearEquiv hc).trans (LinearMap.congr_fun (e.isIntertwining' (a k)) (c v))

omit [Finite V] in
/-- A normal natural seed whose ambient orbit contains all component
displacements recognizes every nontrivial simple component section. -/
theorem natural_section_of_normal_seed_orbit
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal]
    (S : Subrepresentation (ρ.comp K.subtype))
    (b : K ≃* BinaryLinearThree.Group)
    (e : S.toRepresentation.Equiv (BinaryLinearThree.W.comp b.toMonoidHom))
    (hgen : Coinvariants.ker (ρ.comp K.subtype) ≤ ⨆ g : D, S.toSubmodule.map (ρ g))
    {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    (τ : Representation (ZMod 2) K W)
    (hs : QuadraticFourGroup.IsIrreducibleSection (ρ.comp K.subtype) τ) (hnt : τ ≠ 1) :
    ∃ j : K ≃* BinaryLinearThree.Group,
      Nonempty (τ.Equiv (BinaryLinearThree.W.comp j.toMonoidHom)) := by
  let C := fun g : D => conjugateSubrepresentationOrderIso ρ K g S
  have hC (g : D) : IsIrreducible (C g).toRepresentation := by
    obtain ⟨j,⟨f⟩⟩ := natural_conjugate_marking ρ K S b e g
    have hi : IsIrreducible (BinaryLinearThree.W.comp j.toMonoidHom) :=
      (irreducible_comp_surjective_iff j.toMonoidHom j.surjective _).mpr
        BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
    exact (RepEquiv.ofRepresentationEquiv f).irreducible_of_euqiv hi
  have hgen' : Coinvariants.ker (ρ.comp K.subtype) ≤ (⨆ g, C g).toSubmodule := by
    rw [toSubmodule_iSup]
    simpa only [C,conjugateSubrepresentationOrderIso_toSubmodule] using hgen
  obtain ⟨g,⟨f⟩⟩ := QuadraticFourGroup.equiv_generator_of_moved_le (ρ.comp K.subtype) C hC hgen' τ hs hnt
  obtain ⟨j,⟨c⟩⟩ := natural_conjugate_marking ρ K S b e g
  exact ⟨j,⟨f.symm.trans c⟩⟩

/-- Recognition from a normal seed applies to every original ambient
irreducible subquotient, including those reached through nonsplit extensions. -/
theorem subquotient_natural_types_of_normal_seed_orbit
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal] [Group.IsPerfect K]
    (S : Subrepresentation (ρ.comp K.subtype))
    (b : K ≃* BinaryLinearThree.Group)
    (e : S.toRepresentation.Equiv (BinaryLinearThree.W.comp b.toMonoidHom))
    (hgen : Coinvariants.ker (ρ.comp K.subtype) ≤ ⨆ g : D, S.toSubmodule.map (ρ g))
    (U : Subrepresentation ρ) (N : Subrepresentation U.toRepresentation)
    (hi : IsIrreducible N.quotientRepresentation) :
    NaturalLinearThreeTypes N.quotientRepresentation K := by
  let σ := N.quotientRepresentation
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let : IsIrreducible σ := hi
  let : IsSemisimpleRepresentation (σ.comp K.subtype) :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
      (subnormal_restriction_semisimple σ K (inferInstance : K.Normal).isSubnormal)
  intro I hI
  let J := invariantSubspace σ K I hI.choose
  let τ := J.toRepresentation
  have ht : IsIrreducible τ := hI.irreducible_of_semisimple σ
  have hn : τ ≠ 1 := by
    intro he
    apply hI.not_le_fixedSpace σ
    intro v hv k
    have hh := congrArg (fun r : Representation (ZMod 2) K I => r k ⟨v,hv⟩) he
    exact congrArg Subtype.val hh
  have hs : QuadraticFourGroup.IsIrreducibleSection (σ.comp K.subtype) τ :=
    QuadraticFourGroup.IsIrreducibleSection.of_submodule_surjection J
      (IntertwiningMap.id _) Function.surjective_id ht
  let q : Representation.IntertwiningMap (U.toRepresentation.comp K.subtype) (σ.comp K.subtype) := {
    toLinearMap := N.toSubmodule.mkQ
    isIntertwining' _ := rfl }
  have hs' := hs.of_surjective_intertwining q N.toSubmodule.mkQ_surjective
  let l : Representation.IntertwiningMap (U.toRepresentation.comp K.subtype) (ρ.comp K.subtype) := {
    toLinearMap := U.toSubmodule.subtype
    isIntertwining' _ := rfl }
  obtain ⟨j,⟨f⟩⟩ := natural_section_of_normal_seed_orbit ρ K S b e hgen τ
    (hs'.of_injective_intertwining l U.toSubmodule.subtype_injective) hn
  exact ⟨BinaryField.two,rfl,⟨⟨j,f.toLinearEquiv,fun k v => LinearMap.congr_fun (f.isIntertwining' k) v⟩⟩⟩
end CFSG.Quasithin.ChapterD
