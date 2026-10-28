module

public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.Envelope
public import CFSG.Quasithin.MainConverse.OddClassicalSections.UnitaryFour.IrreducibleSections.MaximalCover.Geometry
public import Theory.SpecificGroups.PSp4Three.ProjectiveGeometry
public import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The concrete symplectic subfield branch in PSU₄(3)

Extend the standard Sp₄(3) matrices entrywise from F₃ to F₉, reindex their
basis, and conjugate by an arbitrary invertible F₉ matrix. The kernel of the
resulting map to PGL₄(9) is exactly the center of Sp₄(3): a central symplectic
matrix is scalar, and conversely a matrix becoming scalar after extension
commutes with the faithful extended symplectic representation.

The first isomorphism theorem therefore identifies the actual projective
image with `ClassicalGroup.PSp 2 (ZMod 3)`. A projective unitary subgroup
contained in this image embeds in that target. Its full SU preimage maps to
the same target with precisely the scalar-projection kernel, which is solvable.
Neither simplicity nor a maximal-subgroup table is used in this construction.

`IsSymplecticSubfield` records actual projective matrix containment. Proving
that this case and the exceptional cases exhaust primitive absolutely
irreducible maximals remains an obligation of `Primitive.lean`.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), condition K, printed
pp.4 and 482 of `refs/quasithin.pdf`; GLS3, §2.7 for unitary and symplectic
matrix conventions (`refs/KGroup/GLS3/chapter2.tex`). The scalar-center lemma
is reused from the attributed ATLAS port `PSp4Three.ProjectiveGeometry`.
-/

public noncomputable section
namespace CFSG.Quasithin.MainConverse.UnitaryFourIrreducible
namespace Primitive

open Matrix
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree

private def symplecticReindex :
    GL (Fin 2 ⊕ Fin 2) FiniteField.Nine ≃* GL (Fin 4) FiniteField.Nine :=
  Units.mapEquiv (Matrix.reindexRingEquiv FiniteField.Nine finSumFinEquiv).toMulEquiv

/-- Extend the standard symplectic matrices from F₃ to F₉ and reindex the basis. -/
@[expose] def symplecticSubfieldLinear :
    Matrix.PSp4Three.Sp 2 (ZMod 3) →* GL (Fin 4) FiniteField.Nine :=
  (Units.mapEquiv
    (Matrix.reindexRingEquiv FiniteField.Nine finSumFinEquiv).toMulEquiv).toMonoidHom.comp
    ((GeneralLinearGroup.map (algebraMap (ZMod 3) FiniteField.Nine)).comp
      Matrix.PSp4Three.toGL)

/-- Entrywise identification with the prescribed F₃ matrices. -/
theorem symplecticSubfieldLinear_apply (s : Matrix.PSp4Three.Sp 2 (ZMod 3))
    (i j : Fin 4) :
    (symplecticSubfieldLinear s).val i j =
      algebraMap (ZMod 3) FiniteField.Nine
        (s.val (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) := rfl

private theorem symplecticSubfieldLinear_injective :
    Function.Injective symplecticSubfieldLinear := by
  have hm : Function.Injective
      (GeneralLinearGroup.map (n := Fin 2 ⊕ Fin 2)
        (algebraMap (ZMod 3) FiniteField.Nine)) := by
    intro x y h
    apply Units.ext
    ext i j
    apply (algebraMap (ZMod 3) FiniteField.Nine).injective
    exact congrArg (fun z : GL (Fin 2 ⊕ Fin 2) FiniteField.Nine => z.val i j) h
  exact symplecticReindex.injective.comp (hm.comp Matrix.PSp4Three.toGL_injective)

private theorem symplecticSubfieldLinear_central
    (s : Matrix.PSp4Three.Sp 2 (ZMod 3))
    (hs : s ∈ Subgroup.center (Matrix.PSp4Three.Sp 2 (ZMod 3))) :
    symplecticSubfieldLinear s ∈ Subgroup.center (GL (Fin 4) FiniteField.Nine) := by
  obtain ⟨a, ha⟩ := Matrix.PSp4Three.central_is_scalar s hs
  have hscalar : (Matrix.PSp4Three.toGL s).val = Matrix.scalar (Fin 2 ⊕ Fin 2) a := by
    change s.val = Matrix.scalar (Fin 2 ⊕ Fin 2) a
    ext i j
    have h := congrFun (ha (Pi.single j 1)) i
    simpa [Matrix.PSp4Three.smul_eq_mulVec, Matrix.mulVec_single,
      Matrix.scalar_apply, Matrix.diagonal_apply, Pi.single_apply, eq_comm] using h
  have hc : Matrix.PSp4Three.toGL s ∈
      Subgroup.center (GL (Fin 2 ⊕ Fin 2) (ZMod 3)) :=
    GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨a, hscalar.symm⟩
  exact (Subgroup.centerCongr symplecticReindex
    ⟨_, GeneralLinearGroup.map_center_le
      (algebraMap (ZMod 3) FiniteField.Nine) hc⟩).property

/-- The projective subfield image, with arbitrary change of F₉ basis. -/
@[expose] def symplecticSubfieldProject (b : GL (Fin 4) FiniteField.Nine) :
    Matrix.PSp4Three.Sp 2 (ZMod 3) →* ProjGenLinGroup (Fin 4) FiniteField.Nine :=
  (MulAut.conj (ProjGenLinGroup.mk b)).toMonoidHom.comp
    (ProjGenLinGroup.mk.comp symplecticSubfieldLinear)

theorem symplecticSubfieldProject_apply (b : GL (Fin 4) FiniteField.Nine)
    (s : Matrix.PSp4Three.Sp 2 (ZMod 3)) :
    symplecticSubfieldProject b s =
      ProjGenLinGroup.mk (b * symplecticSubfieldLinear s * b⁻¹) := by
  simp [symplecticSubfieldProject, MulAut.conj_apply]

/-- Scalar extension and change of basis introduce no extra projective kernel. -/
theorem symplecticSubfieldProject_kernel (b : GL (Fin 4) FiniteField.Nine) :
    (symplecticSubfieldProject b).ker =
      Subgroup.center (Matrix.PSp4Three.Sp 2 (ZMod 3)) := by
  ext s
  have he : symplecticSubfieldProject b s = 1 ↔
      ProjGenLinGroup.mk (symplecticSubfieldLinear s) = 1 := by
    exact (MulAut.conj (ProjGenLinGroup.mk b)).map_eq_one_iff
  change symplecticSubfieldProject b s = 1 ↔ _
  rw [he, ProjGenLinGroup.mk_eq_one]
  constructor
  · intro hs
    apply Subgroup.mem_center_iff.mpr
    intro t
    apply symplecticSubfieldLinear_injective
    simpa only [map_mul] using
      Subgroup.mem_center_iff.mp hs (symplecticSubfieldLinear t)
  · exact symplecticSubfieldLinear_central s

/-- The actual projective matrix image is isomorphic to the requested PSp₄(3). -/
def symplecticSubfieldImageEquiv (b : GL (Fin 4) FiniteField.Nine) :
    (symplecticSubfieldProject b).range ≃* SymplecticTarget :=
  (QuotientGroup.quotientKerEquivRange (symplecticSubfieldProject b)).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (symplecticSubfieldProject_kernel b))

/-- Containment in the projective image of actual F₃ symplectic matrices after
an F₉ change of basis. This is a geometric predicate, not a coverage assertion. -/
@[expose] def IsSymplecticSubfield (U : Subgroup (Carrier 4)) : Prop :=
  ∃ b : GL (Fin 4) FiniteField.Nine, ∀ u : U,
    (u.val.val : ProjGenLinGroup (Fin 4) FiniteField.Nine) ∈
      (symplecticSubfieldProject b).range

/-- Subfield containment constructs an injective map into the concrete target. -/
theorem IsSymplecticSubfield.exists_injective_hom (U : Subgroup (Carrier 4))
    (hU : IsSymplecticSubfield U) :
    ∃ f : U →* SymplecticTarget, Function.Injective f := by
  obtain ⟨b, hb⟩ := hU
  let j : U →* (symplecticSubfieldProject b).range :=
    ((Carrier 4).subtype.comp U.subtype).codRestrict _ hb
  refine ⟨(symplecticSubfieldImageEquiv b).toMonoidHom.comp j, ?_⟩
  apply (symplecticSubfieldImageEquiv b).injective.comp
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : (symplecticSubfieldProject b).range => z.val) h

/-- The map on the full preimage kills precisely the full scalar kernel. -/
theorem IsSymplecticSubfield.exists_fullPreimage_hom (U : Subgroup (Carrier 4))
    (hU : IsSymplecticSubfield U) :
    ∃ f : fullPreimage U →* SymplecticTarget,
      f.ker = (preimageProjection U).ker := by
  obtain ⟨f, hf⟩ := hU.exists_injective_hom U
  exact ⟨f.comp (preimageProjection U),
    MonoidHom.ker_comp_of_injective (preimageProjection U) f hf⟩

/-- The full scalar preimage has the concrete PSp model with solvable kernel. -/
theorem IsSymplecticSubfield.fullPreimage_hasSolvableKernelModel
    (U : Subgroup (Carrier 4)) (hU : IsSymplecticSubfield U) :
    HasSolvableKernelModel (fullPreimage U) := by
  obtain ⟨f, hf⟩ := hU.exists_fullPreimage_hom U
  refine Or.inr (Or.inr ⟨f, ?_⟩)
  rw [hf]
  exact preimageProjection_kernel_isSolvable U

end Primitive
end CFSG.Quasithin.MainConverse.UnitaryFourIrreducible
