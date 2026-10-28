module

public import CFSG.Quasithin.ChapterA.Section02.Statements
public import Theory.GroupTheory.QuasithinBasic
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.Alternating.TwoThreeCycles


/-!
# Excluding the even symplectic models at three-rank one

The actual polar representation embeds A₆ into Sp₄(2). Coefficient extension
embeds the binary symplectic group into Sp₄(F) for every field of characteristic
two, whose center is trivial. Thus every PSp₄(2^f) has three-rank at least two.
For the small derived endpoint, the proved isomorphism of the commutator of
the projective group with A₆ gives the same obstruction. These arguments use
actual homomorphisms, not recognition by order.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, the symplectic
alternatives in A.2.3--4, printed p.33, as used in the proof of 15.3.38,
printed p.1137. The polar representation is developed from I.5.4 and I.5.8--9
in the imported modules; no model simplicity theorem is needed here.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne
variable {S : Type*} [Group S] [Finite S]

/-- The exact small derived carrier in Theorem C is A₆ and has rank at least two. -/
theorem rank_ne_one_of_symplectic_derived
    (hmodel : Nonempty (S ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    primeRank 3 S ≠ 1 := by
  obtain ⟨e⟩ := hmodel
  let a := e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
  have h := alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide : 6 ≤ 6)
  rw [← primeRank_equiv 3 a] at h
  omega

private def binarySpMap {F : Type*} [Field F] [CharP F 2] :
    Matrix.symplecticGroup (Fin 2) (ZMod 2) →* Matrix.symplecticGroup (Fin 2) F := by
  let f : ZMod 2 →+* F := ZMod.castHom (by simp) F
  exact
    { toFun g := ⟨g.val.map f, SymplecticGroup.map_mem g.property f⟩
      map_one' := by apply Subtype.ext; exact Matrix.map_one (n := Fin 2 ⊕ Fin 2) f f.map_zero f.map_one
      map_mul' g h := by apply Subtype.ext; exact Matrix.map_mul }

private theorem binarySpMap_injective {F : Type*} [Field F] [CharP F 2] :
    Function.Injective (binarySpMap (F := F)) := by
  intro x y h
  apply Subtype.ext
  ext i j
  apply (ZMod.castHom (by simp) F).injective
  exact congrArg (fun z : Matrix.symplecticGroup (Fin 2) F => z.val i j) h

/-- Coefficient extension of the polar A₆ rules out every even symplectic model. -/
theorem rank_ne_one_of_symplectic_even {f : ℕ}
    (hmodel : ClassicalGroup.IsPSp S 2 (2 ^ f)) : primeRank 3 S ≠ 1 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let a := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv
  let b := Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)
  let j := e.symm.toMonoidHom.comp (b.toMonoidHom.comp
    (binarySpMap.comp (a.toMonoidHom.comp (alternatingGroup (Fin 6)).subtype)))
  have hj : Function.Injective j := e.symm.injective.comp (b.injective.comp
    (binarySpMap_injective.comp (a.injective.comp Subtype.val_injective)))
  have h := (alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide : 6 ≤ 6)).trans
    (primeRank_le_of_injective 3 j hj)
  omega

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.RankOne
