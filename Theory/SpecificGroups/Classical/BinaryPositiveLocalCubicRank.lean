module
public import Theory.SpecificGroups.Alternating.PositiveLocalCubicRank
public import Theory.SpecificGroups.Classical.BinaryDerivedCubicRank.FieldEmbeddings
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# Positive local cubic rank in binary symplectic groups

The normal four-group in A₄ supplies a nontrivial two-local with an element
of order three. The marked polar equivalence Sp₄(2)′ ≃ A₆ and coefficient
transport embed this witness in each actual characteristic-two symplectic
commutator subgroup. Local-rank monotonicity then gives the full and
projective versions, including the small derived projective row.

These are the local contributions in the nonnormal-component rank budget
of Aschbacher–Smith A.3.8, printed pp.45–46. The actual maps are those used
by the imported ordinary-rank and binary polar constructions.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.Classical.BinaryPositiveLocalCubicRank

private def derivedMap {G H : Type*} [Group G] [Group H] (f : G →* H) :
    commutator G →* commutator H :=
  (f.comp (commutator G).subtype).codRestrict (commutator H) (by
    have hc : (commutator G).map f ≤ commutator H := by
      rw [map_commutator_eq]
      exact Subgroup.commutator_mono le_top le_top
    intro x
    exact hc ⟨x, x.property, rfl⟩)

private theorem derivedMap_injective {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) : Function.Injective (derivedMap f) := by
  intro x y h
  exact Subtype.ext (hf (congrArg Subtype.val h))

private def binaryDerivedEquiv :
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) ≃* alternatingGroup (Fin 6) := by
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

/-- The literal derived symplectic group contains the binary A₆ local witness. -/
theorem symplectic_derived {F : Type*} [Field F] [Finite F] [CharP F 2] :
    1 ≤ twoLocalPrimeRank 3 (commutator (Matrix.symplecticGroup (Fin 2) F)) := by
  have hb : 1 ≤ twoLocalPrimeRank 3
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) := by
    exact (Theory.Quasithin.alternating_one_le_twoLocalPrimeRank (by decide : 4≤6)).trans
      (twoLocalPrimeRank_le_of_injective 3 binaryDerivedEquiv.symm.toMonoidHom
        binaryDerivedEquiv.symm.injective)
  exact hb.trans (twoLocalPrimeRank_le_of_injective 3
    (derivedMap (BinaryDerivedCubicRank.FieldEmbeddings.symplectic
      (ZMod.castHom (dvd_refl 2) F)))
    (derivedMap_injective _ (BinaryDerivedCubicRank.FieldEmbeddings.symplectic_injective _)))

/-- The local cubic witness remains in the full characteristic-two symplectic group. -/
theorem symplectic {F : Type*} [Field F] [Finite F] [CharP F 2] :
    1 ≤ twoLocalPrimeRank 3 (Matrix.symplecticGroup (Fin 2) F) :=
  (symplectic_derived (F:=F)).trans (twoLocalPrimeRank_le_of_injective 3
    (commutator (Matrix.symplecticGroup (Fin 2) F)).subtype Subtype.val_injective)

/-- The same local witness in the literal projective symplectic carrier. -/
theorem symplectic_projective {F : Type*} [Field F] [Finite F] [CharP F 2] :
    1 ≤ twoLocalPrimeRank 3
      (Matrix.symplecticGroup (Fin 2) F ⧸ center (Matrix.symplecticGroup (Fin 2) F)) := by
  exact (symplectic (F:=F)).trans (twoLocalPrimeRank_le_of_injective 3
    (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F:=F)).toMonoidHom
    (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F:=F)).injective)

/-- The small derived projective row is the marked A₆ carrier. -/
theorem symplectic_projective_derived_two :
    1 ≤ twoLocalPrimeRank 3
      (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2) ⧸
        center (Matrix.symplecticGroup (Fin 2) (ZMod 2)))) := by
  exact (Theory.Quasithin.alternating_one_le_twoLocalPrimeRank (by decide : 4≤6)).trans
    (twoLocalPrimeRank_le_of_injective 3
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix.symm.toMonoidHom
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix.symm.injective)

end Theory.SpecificGroups.Classical.BinaryPositiveLocalCubicRank
