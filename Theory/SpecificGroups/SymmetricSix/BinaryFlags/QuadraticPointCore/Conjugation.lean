module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreKernel
public import Theory.Representation.BinaryOffender.IrreducibleTransport
/-!
# Transport of quadratic point-core alternatives

Conjugating a subgroup of the actual permutation group preserves
quadraticity and transports its literal moved subspace. Thus the canonical
point-core bound and order-four plane conclusion apply with any compatible
point marking. This keeps the same permutation and natural-module maps.

Source: Aschbacher--Smith, proof of 13.5.7, printed pp.917--918.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore
open NaturalGeometry Representation.BinaryOffender

theorem quadratic_conjugate (A:Subgroup S) (hA:Quadratic A) (g:S) :
    Quadratic (A.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩ v
  change naturalRepresentation Ω (g*a*g⁻¹) (naturalRepresentation Ω (g*b*g⁻¹) v-v)=
    naturalRepresentation Ω (g*b*g⁻¹) v-v
  rw [map_mul,map_mul]
  change naturalRepresentation Ω g (naturalRepresentation Ω a
    (naturalRepresentation Ω g⁻¹ (naturalRepresentation Ω (g*b*g⁻¹) v-v)))=_
  rw [map_sub]
  have hi : naturalRepresentation Ω g⁻¹ (naturalRepresentation Ω (g*b*g⁻¹) v)=
      naturalRepresentation Ω b (naturalRepresentation Ω g⁻¹ v) := by
    rw [←Module.End.mul_apply,←map_mul]
    have he:g⁻¹*(g*b*g⁻¹)=b*g⁻¹ := by group
    rw [he,map_mul,Module.End.mul_apply]
  rw [hi,hA a ha b hb,map_sub]
  have hcancel : naturalRepresentation Ω g (naturalRepresentation Ω g⁻¹ v)=v := by
    rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  rw [hcancel,map_mul,map_mul]
  rfl

theorem moved_conjugate (A:Subgroup S) (g:S) :
    subspaceCommutator (naturalRepresentation Ω) ⊤ A =
      (subspaceCommutator (naturalRepresentation Ω) ⊤
        (A.map (MulAut.conj g⁻¹).toMonoidHom)).map (naturalRepresentation Ω g) := by
  let e:=LinearMap.GeneralLinearGroup.toLinearEquiv ((naturalRepresentation Ω).asGroupHom g)
  have hact : ∀a w, naturalRepresentation Ω a (naturalRepresentation Ω g w)=
      naturalRepresentation Ω g (naturalRepresentation Ω ((MulAut.conj g⁻¹) a) w) := by
    intro a w
    rw [←Module.End.mul_apply,←map_mul,←Module.End.mul_apply,←map_mul]
    congr 2
    change a*g=g*(g⁻¹*a*g)
    group
  have he := subspaceCommutator_map_embedding (naturalRepresentation Ω) (naturalRepresentation Ω)
    (MulAut.conj g⁻¹).toMonoidHom (naturalRepresentation Ω g) hact A ⊤
  have hr : (naturalRepresentation Ω g).range = ⊤ :=
    LinearMap.range_eq_top.mpr (show Function.Surjective (naturalRepresentation Ω g) from e.surjective)
  rw [Submodule.map_top,hr] at he
  exact he

theorem conjugate_core_bound (A:Subgroup S) (g:S)
    (hcore:A≤pointCore.map (MulAut.conj g).toMonoidHom) (hq:Quadratic A) :
    Nat.card A≤4 := by
  let B:=A.map (MulAut.conj g⁻¹).toMonoidHom
  have hB:B≤pointCore := by
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨b,hb,he⟩:=hcore ha
    rw [←he]
    change g⁻¹*(g*b*g⁻¹)*g∈pointCore
    have heq : g⁻¹*(g*b*g⁻¹)*g=b := by group
    rw [heq]
    exact hb
  have hh:=quadratic_card_le_four B hB (quadratic_conjugate A hq g⁻¹)
  rwa [card_map_of_injective (MulAut.conj g⁻¹).injective] at hh

theorem conjugate_core_four_moved_plane (A:Subgroup S) (g:S)
    (hcore:A≤pointCore.map (MulAut.conj g).toMonoidHom) (hq:Quadratic A)
    (hcard:Nat.card A=4) :
    ∃a∈L1, subspaceCommutator (naturalRepresentation Ω) ⊤ A =
      canonicalPlane.map (naturalRepresentation Ω (g*a)) := by
  let B:=A.map (MulAut.conj g⁻¹).toMonoidHom
  have hB:B≤pointCore := by
    rintro _ ⟨a,ha,rfl⟩
    obtain ⟨b,hb,he⟩:=hcore ha
    rw [←he]
    change g⁻¹*(g*b*g⁻¹)*g∈pointCore
    have heq : g⁻¹*(g*b*g⁻¹)*g=b := by group
    rw [heq]
    exact hb
  have hBc:Nat.card B=4 := (card_map_of_injective (MulAut.conj g⁻¹).injective).trans hcard
  obtain ⟨a,ha,he⟩:=quadratic_four_moved_plane B hB (quadratic_conjugate A hq g⁻¹) hBc
  refine ⟨a,ha,?_⟩
  rw [moved_conjugate A g,he,←Submodule.map_comp,map_mul]
  rfl
theorem conjugate_core_four_flag (A:Subgroup S) (g:alternatingGroup Ω)
    (hcore:A≤pointCore.map (MulAut.conj g.val).toMonoidHom) (hq:Quadratic A)
    (hcard:Nat.card A=4) :
    ∃a:alternatingGroup Ω,
      canonicalLine.map (naturalRepresentation Ω g.val)=
        canonicalLine.map (naturalRepresentation Ω a.val) ∧
      subspaceCommutator (naturalRepresentation Ω) ⊤ A=
        canonicalPlane.map (naturalRepresentation Ω a.val) := by
  obtain ⟨b,hb,hplane⟩:=conjugate_core_four_moved_plane A g.val hcore hq hcard
  let bA:alternatingGroup Ω:=⟨b,hb.2⟩
  refine ⟨g*bA,?_,hplane⟩
  change canonicalLine.map (naturalRepresentation Ω g.val)=
    canonicalLine.map (naturalRepresentation Ω (g.val*b))
  rw [map_mul,Module.End.mul_eq_comp,Submodule.map_comp,canonicalLine_map_of_mem hb.1]
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore
