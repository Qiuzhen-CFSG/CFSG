module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.Basic
public import Theory.SpecificGroups.SymmetricSix.Parabolics.Actions

/-!
# The binary alternating subgroup of a supplied symplectic socle

The faithful six-letter polar representation embeds A₆ in Sp₄(2). Extending
the matrix coefficients along the prime-field inclusion gives an embedding
in Sp₄(F). Every field automorphism fixes this subgroup pointwise. Transport
through a specified isomorphism to a subgroup preserves its actual image.

This supplies the intrinsic part of Malle's field-automorphism exclusion in
Section 2.2 of *The maximal subgroups of ²F₄(q²)*, J. Algebra 139 (1991),
52–69, DOI 10.1016/0021-8693(91)90283-E. The centralizer of its embedded
image in the Ree group is a separate geometric obligation.
-/

@[expose] public section

namespace ReeF4.MaximalSubgroups.SimpleNormal.NormalizerBound

open Subgroup Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms

noncomputable section

variable {F : Type*} [Field F] [CharP F 2]

/-- Extend binary symplectic matrices along the prime-field inclusion. -/
def binaryScalarMap : Sp (ZMod 2) →* Sp F where
  toFun g := ⟨g.val.map (ZMod.castHom (dvd_refl 2) F),
    SymplecticGroup.map_mem g.property (ZMod.castHom (dvd_refl 2) F)⟩
  map_one' := by
    apply Subtype.ext
    exact Matrix.map_one (n := Fin 2 ⊕ Fin 2) (ZMod.castHom (dvd_refl 2) F)
      (map_zero _) (map_one _)
  map_mul' _ _ := by
    apply Subtype.ext
    exact Matrix.map_mul

theorem binaryScalarMap_injective : Function.Injective (binaryScalarMap (F := F)) := by
  intro x y h
  apply Subtype.ext
  ext i j
  apply ZMod.castHom_injective F
  exact congrArg (fun g : Sp F => g.val i j) h

/-- Field automorphisms fix every matrix defined over the prime field. -/
theorem fieldAutomorphism_binaryScalarMap (σ : F ≃+* F) (g : Sp (ZMod 2)) :
    fieldAutomorphism σ (binaryScalarMap g) = binaryScalarMap g := by
  apply Subtype.ext
  ext i j
  change (σ.toRingHom.comp (ZMod.castHom (dvd_refl 2) F)) (g.val i j) =
    (ZMod.castHom (dvd_refl 2) F) (g.val i j)
  exact DFunLike.congr_fun (Subsingleton.elim _ _) _

/-- The actual binary A₆ in the four-dimensional symplectic matrix group. -/
def binaryAlternatingEmbedding : alternatingGroup (Fin 6) →* Sp F :=
  binaryScalarMap.comp (Theory.SpecificGroups.SymmetricSix.polarRepresentation.comp
    (alternatingGroup (Fin 6)).subtype)

theorem binaryAlternatingEmbedding_injective :
    Function.Injective (binaryAlternatingEmbedding (F := F)) :=
  binaryScalarMap_injective.comp
    (Theory.SpecificGroups.SymmetricSix.polarRepresentation_injective.comp
      (alternatingGroup (Fin 6)).subtype_injective)

theorem fieldAutomorphism_binaryAlternatingEmbedding (σ : F ≃+* F)
    (a : alternatingGroup (Fin 6)) :
    fieldAutomorphism σ (binaryAlternatingEmbedding a) = binaryAlternatingEmbedding a :=
  fieldAutomorphism_binaryScalarMap σ _

/-- Embed the binary A₆ in the supplied subgroup, using the specified
symplectic equivalence and the literal subgroup inclusion. -/
def binaryAlternatingInSubgroup {G : Type*} [Group G]
    (S : Subgroup G) (e : S ≃* Sp F) : alternatingGroup (Fin 6) →* G :=
  S.subtype.comp (e.symm.toMonoidHom.comp binaryAlternatingEmbedding)

theorem binaryAlternatingInSubgroup_injective {G : Type*} [Group G]
    (S : Subgroup G) (e : S ≃* Sp F) :
    Function.Injective (binaryAlternatingInSubgroup S e) :=
  S.subtype_injective.comp
    (e.symm.injective.comp binaryAlternatingEmbedding_injective)

end

end ReeF4.MaximalSubgroups.SimpleNormal.NormalizerBound
