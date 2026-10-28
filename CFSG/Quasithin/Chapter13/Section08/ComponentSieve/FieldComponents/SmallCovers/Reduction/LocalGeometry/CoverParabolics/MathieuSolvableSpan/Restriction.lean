module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.MathieuSolvableSpan.Geometry
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Mathlib.GroupTheory.Nilpotent

/-!
# The genuine six-point restriction of an automorphism hexad stabilizer

Conjugation is realized by actual permutations of the 22-point Witt design.
Restricting to a fixed hexad and labelling its points gives the six-point
homomorphism. On inner automorphisms it is exactly the existing M₂₂ hexad
restriction, so its image contains A₆.

The pointwise kernel is solvable even in the presence of an outer supplement.
Permutation sign maps it to an abelian group; the sign kernel is the image
of the actual inner pointwise hexad kernel of order sixteen. This proves
solvability by an extension, without assuming a splitting or an abstract
parabolic model.

Source: the invariant-hexad geometry used in Aschbacher--Smith 13.8.21(2),
printed p.956 (PDF p.973).
-/

@[expose] public section

open Subgroup
open scoped Pointwise
open Sporadic.Mathieu Sporadic.Mathieu.M22ValueBound.Concrete
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.MathieuSolvableSpan

noncomputable def pointAction : MulAut M22 →* Equiv.Perm (Fin 22) :=
  m22DesignAut.subtype.comp designAutEquiv.symm.toMonoidHom

theorem pointAction_injective : Function.Injective pointAction :=
  m22DesignAut.subtype_injective.comp designAutEquiv.symm.injective

theorem pointAction_mem_design (a : MulAut M22) : pointAction a ∈ m22DesignAut :=
  (designAutEquiv.symm a).property

@[simp] theorem pointAction_inner (g : M22) : pointAction (MulAut.conj g) = g.val := by
  change (designAutEquiv.symm (MulAut.conj g)).val = g.val
  rw [← designAutEquiv_inclusion, MulEquiv.symm_apply_apply]
  rfl

noncomputable abbrev fullHexad (B : Hexad) : Subgroup (MulAut M22) :=
  MulAction.stabilizer (MulAut M22) B

noncomputable def innerToHexad (B : Hexad) :
    MulAction.stabilizer M22 B.val →* fullHexad B :=
  ((MulAut.conj : M22 →* MulAut M22).comp
    (MulAction.stabilizer M22 B.val).subtype).codRestrict _ (by
      intro g
      change MulAut.conj g.val • B = B
      rw [inner_smul]
      exact Subtype.ext g.property)

noncomputable def setRestriction (B : Hexad) : fullHexad B →* Equiv.Perm B.val where
  toFun g := (pointAction g.val).subtypePerm (by
    exact MulAction.mem_stabilizer_finset.mp
      (show pointAction g.val ∈ MulAction.stabilizer (Equiv.Perm (Fin 22)) B.val from
        congrArg Subtype.val g.property))
  map_one' := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    change pointAction 1 a.val = a.val
    rw [map_one]
    rfl
  map_mul' g h := by
    apply Equiv.ext
    intro a
    apply Subtype.ext
    change pointAction (g.val * h.val) a.val = pointAction g.val (pointAction h.val a.val)
    rw [map_mul]
    rfl

noncomputable def sixAction (B : Hexad) : fullHexad B →* Equiv.Perm (Fin 6) :=
  (m22HexadLabels B.property).permCongrHom.toMonoidHom.comp (setRestriction B)

@[simp] theorem sixAction_apply (B : Hexad) (g : fullHexad B) (a : B.val) :
    sixAction B g (m22HexadLabels B.property a) =
      m22HexadLabels B.property (setRestriction B g a) := by
  change m22HexadLabels B.property (setRestriction B g
    ((m22HexadLabels B.property).symm (m22HexadLabels B.property a))) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem sixAction_inner (B : Hexad) (g : MulAction.stabilizer M22 B.val) :
    sixAction B (innerToHexad B g) = m22HexadAction B.property g := by
  apply Equiv.ext
  intro i
  obtain ⟨a, rfl⟩ := (m22HexadLabels B.property).surjective i
  rw [sixAction_apply, m22HexadAction_apply]
  apply congrArg (m22HexadLabels B.property)
  apply Subtype.ext
  change pointAction (MulAut.conj g.val) a.val = g.val.val a.val
  rw [pointAction_inner]

theorem sixAction_range_contains_alternating (B : Hexad) :
    alternatingGroup (Fin 6) ≤ (sixAction B).range := by
  intro a ha
  rw [← m22HexadAction_range B.property] at ha
  obtain ⟨g, rfl⟩ := ha
  exact ⟨innerToHexad B g, sixAction_inner B g⟩

noncomputable def innerKernelMap (B : Hexad) :
    (m22HexadAction B.property).ker →* (sixAction B).ker :=
  ((innerToHexad B).comp (m22HexadAction B.property).ker.subtype).codRestrict _ (by
    intro g
    change sixAction B (innerToHexad B g.val) = 1
    rw [sixAction_inner]
    exact g.property)

theorem sixAction_ker_solvable (B : Hexad) : Group.IsSolvable (sixAction B).ker := by
  have hc : Nat.card (m22HexadAction B.property).ker = 2 ^ 4 := by
    rw [m22HexadAction_ker]
    exact m22HexadKernel_card B.property
  let := (IsPGroup.of_card hc).isNilpotent
  let q : (sixAction B).ker →* ℤˣ :=
    (Equiv.Perm.sign.comp pointAction).comp
      ((fullHexad B).subtype.comp (sixAction B).ker.subtype)
  apply Group.isSolvable_of_ker_le_range (innerKernelMap B) q
  intro k hk
  let g : M22 := ⟨pointAction k.val.val, pointAction_mem_design _, hk⟩
  have hconj : MulAut.conj g = k.val.val := by
    apply pointAction_injective
    exact pointAction_inner g
  have hg : g ∈ MulAction.stabilizer M22 B.val := by
    have h : MulAut.conj g • B = B := hconj.symm ▸ k.val.property
    rw [inner_smul] at h
    exact congrArg Subtype.val h
  let y : MulAction.stabilizer M22 B.val := ⟨g, hg⟩
  have hy : innerToHexad B y = k.val := Subtype.ext hconj
  have hker : y ∈ (m22HexadAction B.property).ker := by
    change m22HexadAction B.property y = 1
    rw [← sixAction_inner, hy]
    exact k.property
  exact ⟨⟨y, hker⟩, Subtype.ext (Subtype.ext hconj)⟩


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.MathieuSolvableSpan
