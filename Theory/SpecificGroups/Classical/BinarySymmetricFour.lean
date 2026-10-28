module
public import Theory.SpecificGroups.PSL3.LinearThreeBinaryLocals
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.FieldEmbeddings
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Mathlib.GroupTheory.Perm.ViaEmbedding
/-!
# Actual symmetric-four subgroups in binary rank-two groups

For PSL₃, transport the actual binary point local S₄ into the larger field;
projection is faithful because the point local fixes a nonzero vector.
For PSp₄, extend a permutation on four letters by two fixed letters, use
the faithful six-letter polar representation of Sp₄(2), and extend matrix
coefficients. The characteristic-two projective map is an equivalence.

These literal embeddings give the section obstruction in the Bender-target
case of Aschbacher–Smith 2.5.6, printed p.554.
-/
public section
open Subgroup
open scoped MatrixGroups
namespace Theory.SpecificGroups.Classical.BinarySymmetricFour
open Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [CharP F 2]
private noncomputable def pointMap : pointLocalSL (ZMod 2) →* pointLocalSL F :=
  ((Matrix.SpecialLinearGroup.map (ZMod.castHom (dvd_refl 2) F)).comp
    (pointLocalSL (ZMod 2)).subtype).codRestrict (pointLocalSL F) (by
      intro g
      rw [mem_pointLocalSL_iff]
      obtain ⟨h0,h1,h2⟩ := (mem_pointLocalSL_iff _ _).mp g.property
      change (ZMod.castHom (dvd_refl 2) F) ((g:SL(3,ZMod 2)).val 0 0)=1 ∧
        (ZMod.castHom (dvd_refl 2) F) ((g:SL(3,ZMod 2)).val 1 0)=0 ∧
        (ZMod.castHom (dvd_refl 2) F) ((g:SL(3,ZMod 2)).val 2 0)=0
      simp only [h0,h1,h2,map_one,map_zero,and_self])
private theorem pointMap_injective : Function.Injective (pointMap F) := by
  intro g h he
  apply Subtype.ext
  ext i j
  exact (ZMod.castHom (dvd_refl 2) F).injective
    (congrArg (fun a : pointLocalSL F => ((a:SL(3,F)).val i j)) he)

/-- The binary point local supplies an actual S₄ subgroup in every binary PSL₃. -/
noncomputable def linear : Equiv.Perm (Fin 4) →* PSL(3,F) :=
  (pointLocal F).subtype.comp ((pointLocalProjectEquiv F).toMonoidHom.comp
    ((pointMap F).comp (((binaryPointLocalEquivS4 (ZMod 2) (by simp)).symm.trans
      (pointLocalProjectEquiv (ZMod 2)).symm).toMonoidHom)))

theorem linear_injective : Function.Injective (linear F) :=
  (pointLocal F).subtype_injective.comp ((pointLocalProjectEquiv F).injective.comp
    ((pointMap_injective F).comp (((binaryPointLocalEquivS4 (ZMod 2) (by simp)).symm.trans
      (pointLocalProjectEquiv (ZMod 2)).symm).injective)))

/-- Extend four-point permutations by two fixed points, then use the original
six-point polar representation and coefficient embedding. -/
noncomputable def symplectic : Equiv.Perm (Fin 4) →* (Matrix.symplecticGroup (Fin 2) F ⧸ center (Matrix.symplecticGroup (Fin 2) F)) :=
  (SymplecticFour.EvenProjective.equiv (F:=F)).toMonoidHom.comp
    ((BinaryDerivedCubicRank.FieldEmbeddings.symplectic
      (ZMod.castHom (dvd_refl 2) F)).comp
      (SymplecticFour.Binary.symmetricSixEquiv.toMonoidHom.comp
        (Equiv.Perm.viaEmbeddingHom ⟨Fin.castAdd 2, Fin.castAdd_injective 4 2⟩)))

theorem symplectic_injective : Function.Injective (symplectic F) :=
  (SymplecticFour.EvenProjective.equiv (F:=F)).injective.comp
    ((BinaryDerivedCubicRank.FieldEmbeddings.symplectic_injective
      (ZMod.castHom (dvd_refl 2) F)).comp
      (SymplecticFour.Binary.symmetricSixEquiv.injective.comp
        (Equiv.Perm.viaEmbeddingHom_injective ⟨Fin.castAdd 2,Fin.castAdd_injective 4 2⟩)))
end Theory.SpecificGroups.Classical.BinarySymmetricFour
