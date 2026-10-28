module
public import Theory.Representation.IrreducibleSectionSemisimple
public import Theory.Representation.BinaryOffender.Homogeneous.Selection.Action
public import Mathlib.RepresentationTheory.Coinvariants
public import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Simple sections detected by semisimple displacement generators

If a family of simple submodules contains every displacement, every
nontrivial simple section has the type of one of those generators. Intersect
its numerator with the generated semisimple submodule; the intersection
surjects because the complementary quotient action is trivial. Semisimplicity
then identifies the section with a generator. This permits nonsplit extensions
in the original representation.

The normal terminal component application uses the ambient conjugates of a
natural seed, retaining the original quotient. Source: Aschbacher--Smith
A.1.41--42 and 14.6.22, printed pp. 31--32, 1038.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation.BinaryOffender.Homogeneous
open scoped MonoidAlgebra
open Representation
namespace Representation.QuadraticFourGroup
variable {D V W : Type*} [Group D]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

/-- A nontrivial simple section of a representation occurs in any semisimple
sum of simple submodules containing all displacements. -/
theorem equiv_generator_of_moved_le
    (ρ : Representation (ZMod 2) D V) {ι : Type*} (S : ι → Subrepresentation ρ)
    (hS : ∀ i, IsIrreducible (S i).toRepresentation)
    (hmoved : Coinvariants.ker ρ ≤ (⨆ i, S i).toSubmodule)
    (τ : Representation (ZMod 2) D W) (hs : IsIrreducibleSection ρ τ) (hnt : τ ≠ 1) :
    ∃ i, Nonempty ((S i).toRepresentation.Equiv τ) := by
  classical
  obtain ⟨hi,U,N,⟨e⟩⟩ := hs
  let := hi
  let P : Subrepresentation ρ := ⨆ i, S i
  let Q : Subrepresentation U.toRepresentation := {
    toSubmodule := P.toSubmodule.comap U.toSubmodule.subtype
    apply_mem_toSubmodule g v hv := P.apply_mem_toSubmodule g hv }
  let f : Q.toRepresentation.IntertwiningMap τ := {
    toLinearMap := e.toLinearEquiv.toLinearMap.comp
      (N.toSubmodule.mkQ.comp Q.toSubmodule.subtype)
    isIntertwining' g := by
      ext v
      exact LinearMap.congr_fun (e.isIntertwining' g) (N.toSubmodule.mkQ v.val) }
  have hf : f ≠ 0 := by
    intro hz
    apply hnt
    ext g w
    obtain ⟨v,rfl⟩ := e.toLinearEquiv.surjective w
    obtain ⟨v,rfl⟩ := N.toSubmodule.mkQ_surjective v
    have hv : ρ g v.val - v.val ∈ P.toSubmodule :=
      hmoved (Submodule.subset_span ⟨⟨g,v.val⟩,rfl⟩)
    let z : Q := ⟨U.toRepresentation g v - v,hv⟩
    have hz' := congrArg (fun a : Q.toRepresentation.IntertwiningMap τ => a z) hz
    have he : τ g (e (N.toSubmodule.mkQ v)) - e (N.toSubmodule.mkQ v) = 0 := by
      change e (N.toSubmodule.mkQ (U.toRepresentation g v - v)) = 0 at hz'
      rw [map_sub,map_sub] at hz'
      have hh := LinearMap.congr_fun (e.isIntertwining' g) (N.toSubmodule.mkQ v)
      change e (N.toSubmodule.mkQ (U.toRepresentation g v)) = τ g (e (N.toSubmodule.mkQ v)) at hh
      rwa [hh] at hz'
    exact sub_eq_zero.mp he
  let l : Q.toRepresentation.IntertwiningMap P.toRepresentation := {
    toLinearMap := (U.toSubmodule.subtype.comp Q.toSubmodule.subtype).codRestrict
      P.toSubmodule (fun v => v.property)
    isIntertwining' _ := rfl }
  have hli : Function.Injective l := by
    intro v w he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : P => (x : V)) he
  let a := IntertwiningMap.equivLinearMapAsModule Q.toRepresentation P.toRepresentation l
  let b := IntertwiningMap.equivLinearMapAsModule Q.toRepresentation τ f
  let os := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  let : IsSemisimpleModule (ZMod 2)[D] P.asSubmodule := by
    have hp : P.asSubmodule = ⨆ i, (S i).asSubmodule := os.map_iSup S
    rw [hp]
    have hh : (⨆ i ∈ Set.univ, (S i).asSubmodule) = ⨆ i, (S i).asSubmodule := by simp
    rw [←hh]
    exact
      (isSemisimpleModule_biSup_of_isSemisimpleModule_submodule
        (s := Set.univ) (p := fun i => (S i).asSubmodule) (fun i _ => by
          let := simple_asSubmodule (S i) (hS i)
          infer_instance))
  let pe : P.asSubmodule ≃ₗ[(ZMod 2)[D]] P.toRepresentation.asModule := by
    let z : P.asSubmodule →ₗ[(ZMod 2)[D]] P.toRepresentation.asModule := {
      toFun := fun v => P.toRepresentation.asModuleEquiv.symm ⟨ρ.asModuleEquiv v.val,v.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a v
        induction a using MonoidAlgebra.induction_linear with
        | zero => simp
        | add a b ha hb =>
          simp only [RingHom.id_apply,add_smul] at ha hb ⊢
          exact congrArg₂ (· + ·) ha hb
        | single g a =>
          apply Subtype.ext
          simp only [RingHom.id_apply,SetLike.val_smul,Representation.single_smul]
          rfl }
    exact LinearEquiv.ofBijective z ⟨fun v w h => Subtype.ext (congrArg Subtype.val h),
      fun v => ⟨⟨v.val,v.property⟩,rfl⟩⟩
  let : IsSemisimpleModule (ZMod 2)[D] P.toRepresentation.asModule :=
    IsSemisimpleModule.congr pe.symm
  obtain ⟨p,hp⟩ := IsSemisimpleModule.extension_property (R := (ZMod 2)[D])
    (M := P.toRepresentation.asModule) (N := Q.toRepresentation.asModule) (P := τ.asModule) a
    (show Function.Injective a from hli) b
  let q := (IntertwiningMap.equivLinearMapAsModule P.toRepresentation τ).symm p
  have hqf : q.comp l = f := by
    apply IntertwiningMap.ext
    ext v
    exact LinearMap.congr_fun hp v
  have hqn : q ≠ 0 := by
    intro he
    apply hf
    rw [←hqf,he]
    rfl
  have hsurj := (IsIrreducible.surjective_or_eq_zero q).resolve_right hqn
  obtain ⟨j,hj⟩ := IsSemisimpleModule.lifting_property (R := (ZMod 2)[D])
    (M := P.toRepresentation.asModule) (N := τ.asModule) (P := τ.asModule) p
    (show Function.Surjective p from hsurj)
    (LinearMap.id : τ.asModule →ₗ[(ZMod 2)[D]] τ.asModule)
  let j' := (IntertwiningMap.equivLinearMapAsModule τ P.toRepresentation).symm j
  have hji : Function.Injective j' := by
    intro v w he
    have hv := LinearMap.congr_fun hj v
    have hw := LinearMap.congr_fun hj w
    exact hv.symm.trans ((congrArg p he).trans hw)
  let jV : τ.IntertwiningMap ρ := {
    toLinearMap := P.toSubmodule.subtype.comp j'.toLinearMap
    isIntertwining' g := by ext v; exact congrArg Subtype.val (j'.isIntertwining _ _ g v) }
  have hjVi : Function.Injective jV := P.toSubmodule.subtype_injective.comp hji
  let eJ : τ.Equiv jV.range.toRepresentation := .mk
    (LinearEquiv.ofInjective jV.toLinearMap hjVi) (by
      intro g; ext v
      exact jV.isIntertwining _ _ g v)
  let : IsIrreducible jV.range.toRepresentation :=
    (RepEquiv.ofRepresentationEquiv eJ.symm).irreducible_of_euqiv hi
  let s : Set (Submodule (ZMod 2)[D] ρ.asModule) := Set.range (fun i => (S i).asSubmodule)
  let : ∀ m : s, IsSimpleModule (ZMod 2)[D] m.val := by
    rintro ⟨m,i,rfl⟩
    exact simple_asSubmodule (S i) (hS i)
  let := simple_asSubmodule jV.range (inferInstance : IsIrreducible jV.range.toRepresentation)
  have hle : jV.range.asSubmodule ≤ sSup s := by
    rw [sSup_range]
    change jV.range.asSubmodule ≤ ⨆ i, os (S i)
    rw [←os.map_iSup S]
    rintro _ ⟨v,rfl⟩
    exact (j' v).property
  obtain ⟨J,⟨i,rfl⟩,⟨bJ⟩⟩ := jV.range.asSubmodule.linearEquiv_of_le_sSup s hle
  let c := ((BinaryOffender.Homogeneous.sameModule_iff_linearEquiv jV.range (S i)).mpr
    ⟨bJ⟩)
  obtain ⟨d⟩ := (BinaryOffender.Homogeneous.sameModule_iff_repEquiv _ _).mp c
  exact ⟨i,⟨d.symm.toRepresentationEquiv.trans eJ.symm⟩⟩
end Representation.QuadraticFourGroup

namespace Representation.QuadraticFourGroup
variable {k D V W X : Type*} [Field k] [Group D]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  [AddCommGroup X] [Module k X]
  {ρ : Representation k D V} {σ : Representation k D W} {τ : Representation k D X}

/-- An equivariant epimorphism from a submodule presents its simple target as a section. -/
theorem IsIrreducibleSection.of_submodule_surjection
    (U : Subrepresentation ρ) (f : U.toRepresentation.IntertwiningMap τ)
    (hf : Function.Surjective f) (hi : IsIrreducible τ) : IsIrreducibleSection ρ τ := by
  refine ⟨hi,U,f.ker,⟨.mk (f.toLinearMap.quotKerEquivOfSurjective hf) ?_⟩⟩
  intro g
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | H v => exact LinearMap.congr_fun (f.isIntertwining' g) v

/-- A simple section of an equivariantly embedded module is a section of the larger module. -/
theorem IsIrreducibleSection.of_injective_intertwining
    (f : ρ.IntertwiningMap σ) (hf : Function.Injective f)
    (hs : IsIrreducibleSection ρ τ) : IsIrreducibleSection σ τ := by
  obtain ⟨hi,U,N,⟨e⟩⟩ := hs
  let a : U.toRepresentation.IntertwiningMap σ := {
    toLinearMap := f.toLinearMap.comp U.toSubmodule.subtype
    isIntertwining' g := by ext v; exact f.isIntertwining _ _ g v.val }
  have ha : Function.Injective a := hf.comp U.toSubmodule.subtype_injective
  let b : U.toRepresentation.Equiv a.range.toRepresentation := .mk
    (LinearEquiv.ofInjective a.toLinearMap ha) (by
      intro g; ext v; exact a.isIntertwining _ _ g v)
  let q : U.toRepresentation.IntertwiningMap N.quotientRepresentation := {
    toLinearMap := N.toSubmodule.mkQ
    isIntertwining' _ := rfl }
  let p := (e.toIntertwiningMap.comp q).comp b.symm.toIntertwiningMap
  exact IsIrreducibleSection.of_submodule_surjection a.range p
    (e.toLinearEquiv.surjective.comp (N.toSubmodule.mkQ_surjective.comp b.symm.toLinearEquiv.surjective)) hi
end Representation.QuadraticFourGroup
