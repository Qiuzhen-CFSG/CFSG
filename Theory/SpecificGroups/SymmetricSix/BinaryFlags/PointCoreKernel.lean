module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.LinearAlgebra.BinaryTriangularPGroup
/-!
# The kernel on the natural point quotient lies in the point core

An element fixing the distinguished point and acting trivially on its
perpendicular modulo that point lies in the actual two-core of the point
stabilizer. The kernel is normal. Its displacement operator lowers the
three-step flag V > V₁-perpendicular > V₁ > 0, so its cube vanishes.
Faithfulness of the natural representation makes this normal kernel a
two-group. Coordinate conjugation gives the same statement for any point.

Source: Aschbacher--Smith, proof of 13.5.7, printed pp.917--918.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreKernel
open NaturalGeometry NaturalPairing PointAction
private theorem fixed_point (g:H1) : naturalRepresentation Ω g.val (pairVector 4 5)=pairVector 4 5 := by
  rw [pairVector_map]
  apply (pairVector_eq_iff (g.val.injective.ne (by decide)) (by decide)).mpr
  have h:=g.property
  change (pair 4 5).image g.val=pair 4 5 at h
  simpa only [pair,Finset.image_insert,Finset.image_singleton] using h
private theorem fixed_line (g:H1) (v:V) (hv:v∈canonicalLine) : naturalRepresentation Ω g.val v=v := by
  obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hv
  rw [map_smul,fixed_point]
private theorem stable_perp (g:H1) (v:V) (hv:v∈Hyperplane) :
    naturalRepresentation Ω g.val v∈Hyperplane := by
  change _ ∈ form.orthogonal canonicalLine
  rw [←orthogonal_invariant canonicalLine g.val (canonicalLine_map_of_mem g.property)]
  exact Submodule.mem_map_of_mem hv
private theorem displacement_perp (g:H1) (v:V) :
    naturalRepresentation Ω g.val v-v∈Hyperplane := by
  intro w hw
  obtain ⟨a,rfl⟩:=Submodule.mem_span_singleton.mp hw
  have h:=form_invariant g.val (pairVector 4 5) v
  rw [fixed_point] at h
  rw [map_smul,LinearMap.smul_apply,map_sub,h,sub_self,smul_zero]
private def star : Subgroup H1 where
  carrier := {g | ∀v∈Hyperplane, naturalRepresentation Ω g.val v-v∈canonicalLine}
  one_mem' := by intro v _;simp
  mul_mem' := by
    intro g h hg hh v hv
    change naturalRepresentation Ω (g.val*h.val) v-v∈canonicalLine
    have he : naturalRepresentation Ω (g.val*h.val) v-v =
        naturalRepresentation Ω g.val (naturalRepresentation Ω h.val v-v) +
        (naturalRepresentation Ω g.val v-v) := by
      rw [map_mul,Module.End.mul_apply,map_sub];abel
    rw [he,fixed_line g _ (hh v hv)]
    exact canonicalLine.add_mem (hh v hv) (hg v hv)
  inv_mem' := by
    intro g hg v hv
    have hh:=hg (naturalRepresentation Ω g.val⁻¹ v) (stable_perp g⁻¹ v hv)
    have hi : naturalRepresentation Ω g.val (naturalRepresentation Ω g.val⁻¹ v)=v := by
      rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
    rw [hi] at hh
    change naturalRepresentation Ω g.val⁻¹ v-v∈canonicalLine
    simpa only [neg_sub] using canonicalLine.neg_mem hh
private theorem star_normal : star.Normal := by
  constructor
  intro a ha g v hv
  have hw:=stable_perp g⁻¹ v hv
  have hd:=ha (naturalRepresentation Ω g.val⁻¹ v) hw
  have he : naturalRepresentation Ω (g.val*a.val*g.val⁻¹) v-v =
      naturalRepresentation Ω g.val (naturalRepresentation Ω a.val (naturalRepresentation Ω g.val⁻¹ v)-
        naturalRepresentation Ω g.val⁻¹ v) := by
    rw [map_sub]
    have hi : naturalRepresentation Ω g.val (naturalRepresentation Ω g.val⁻¹ v)=v := by
      rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
    rw [hi,map_mul,map_mul]
    rfl
  change naturalRepresentation Ω (g.val*a.val*g.val⁻¹) v-v∈canonicalLine
  rw [he,fixed_line g _ hd]
  exact hd
private theorem star_two : IsPGroup 2 star := by
  let : Nontrivial V := Module.nontrivial_of_finrank_pos (by
    rw [finrank_natural_even Ω (by decide)];decide)
  let : ExpChar (Module.End (ZMod 2) V) 2 := expChar_of_injective_algebraMap
    (FaithfulSMul.algebraMap_injective (ZMod 2) (Module.End (ZMod 2) V)) 2
  let f := (naturalRepresentation Ω).comp (H1.subtype.comp star.subtype)
  have hi : Function.Injective f :=
    (naturalRepresentation_injective Ω (by decide)).comp
      (H1.subtype_injective.comp star.subtype_injective)
  apply IsPGroup.of_injective_unipotent_binary f hi
  intro g
  refine ⟨3,?_⟩
  ext v : 1
  change (naturalRepresentation Ω g.val.val - LinearMap.id : Module.End (ZMod 2) V)
    ((naturalRepresentation Ω g.val.val - LinearMap.id : Module.End (ZMod 2) V)
      ((naturalRepresentation Ω g.val.val - LinearMap.id : Module.End (ZMod 2) V) v))=0
  have hmem := g.property (naturalRepresentation Ω g.val.val v-v) (displacement_perp g.val v)
  change naturalRepresentation Ω g.val.val
    (naturalRepresentation Ω g.val.val (naturalRepresentation Ω g.val.val v-v) -
      (naturalRepresentation Ω g.val.val v-v)) -
    (naturalRepresentation Ω g.val.val (naturalRepresentation Ω g.val.val v-v) -
      (naturalRepresentation Ω g.val.val v-v))=0
  rw [fixed_line g.val _ hmem,sub_self]

theorem mem_pointCore_of_seed_displacement (g:S) (hg:g∈H1)
    (hs:∀v∈Hyperplane,naturalRepresentation Ω g v-v∈canonicalLine) :g∈pointCore := by
  have hle : star≤pCore 2 H1 := le_sSup ⟨star_normal,star_two⟩
  rw [←H1_core_eq_pointCore]
  exact ⟨⟨g,hg⟩,hle hs,rfl⟩

theorem mem_conjugate_pointCore_of_seed_displacement (g a:S) (v:V)
    (hg:naturalRepresentation Ω g (pairVector 4 5)=v)
    (ha:naturalRepresentation Ω a v=v)
    (hs:∀w∈Perpendicular v,naturalRepresentation Ω a w-w∈Submodule.span (ZMod 2) {v}) :
    a∈pointCore.map (MulAut.conj g).toMonoidHom := by
  let b := g⁻¹*a*g
  have hb : naturalRepresentation Ω b (pairVector 4 5)=pairVector 4 5 := by
    change naturalRepresentation Ω (g⁻¹*a*g) (pairVector 4 5)=pairVector 4 5
    simp only [map_mul,Module.End.mul_apply]
    rw [hg,ha,←hg,←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  have hbH : b∈H1 := by
    rw [pairVector_map] at hb
    have hp := (pairVector_eq_iff (b.injective.ne (by decide)) (by decide)).mp hb
    change (pair 4 5).image b=pair 4 5
    simpa only [pair,Finset.image_insert,Finset.image_singleton] using hp
  have hbcore : b∈pointCore := by
    apply mem_pointCore_of_seed_displacement b hbH
    intro w hw
    have hd : naturalRepresentation Ω g w∈Perpendicular v :=
      (transport g v hg (Multiplicative.ofAdd ⟨w,hw⟩)).toAdd.property
    have hmem:=hs _ hd
    have hp : canonicalLine.map (naturalRepresentation Ω g)=Submodule.span (ZMod 2) {v} := by
      rw [canonicalLine,Submodule.map_span,Set.image_singleton,hg]
    rw [←hp] at hmem
    obtain ⟨u,hu,he⟩:=hmem
    have hi : Function.Injective (naturalRepresentation Ω g) :=
      (LinearMap.GeneralLinearGroup.toLinearEquiv ((naturalRepresentation Ω).asGroupHom g)).injective
    have he' : naturalRepresentation Ω g (naturalRepresentation Ω b w-w)=
        naturalRepresentation Ω a (naturalRepresentation Ω g w)-naturalRepresentation Ω g w := by
      rw [map_sub,←Module.End.mul_apply,←map_mul]
      have hgb : g*b=a*g := by dsimp [b];group
      rw [hgb,map_mul,Module.End.mul_apply]
    have heu : u=naturalRepresentation Ω b w-w := hi (he.trans he'.symm)
    exact heu ▸ hu
  refine ⟨b,hbcore,?_⟩
  change g*b*g⁻¹=a
  dsimp [b]
  group
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreKernel
