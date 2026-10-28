module

public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular
public import Mathlib.GroupTheory.Sylow

/-!
# Solvability of the Sylow normalizer in a binary SL₂ pair

The projections of the specified Sylow subgroup are Sylow in each SL₂
factor. Its normalizer embeds in the product of their solvable normalizers.
No simplicity or lower field-size hypothesis is needed.

This is the quotient Borel calculation for the original exchanged pair in
Aschbacher--Smith, 10.2.3, printed p.745.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem pair_sylow_normalizer_solvable
    (S : Sylow 2 (SL(2,F) × SL(2,F))) :
    Group.IsSolvable (normalizer (S : Set (SL(2,F) × SL(2,F)))) := by
  let f := MonoidHom.fst SL(2,F) SL(2,F)
  let g := MonoidHom.snd SL(2,F) SL(2,F)
  let S1 := S.mapSurjective (f := f) (fun x => ⟨(x,1),rfl⟩)
  let S2 := S.mapSurjective (f := g) (fun x => ⟨(1,x),rfl⟩)
  let N := normalizer (S : Set (SL(2,F) × SL(2,F)))
  let N1 := normalizer (S1 : Set SL(2,F))
  let N2 := normalizer (S2 : Set SL(2,F))
  let : Group.IsSolvable N1 :=
    Theory.SpecificGroups.LinearSylowNormalizers.isSolvable_sylow_normalizer
      2 F (by decide) S1
  let : Group.IsSolvable N2 :=
    Theory.SpecificGroups.LinearSylowNormalizers.isSolvable_sylow_normalizer
      2 F (by decide) S2
  have hf : N.map f ≤ N1 := le_normalizer_map f
  have hg : N.map g ≤ N2 := le_normalizer_map g
  let i : N →* N1 × N2 :=
    ((f.comp N.subtype).codRestrict N1 (fun x => hf (mem_map_of_mem f x.property))).prod
      ((g.comp N.subtype).codRestrict N2 (fun x => hg (mem_map_of_mem g x.property)))
  apply Group.isSolvable_of_isSolvable_injective (f := i)
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : N1 × N2 => (z.1 : SL(2,F))) h
  · exact congrArg (fun z : N1 × N2 => (z.2 : SL(2,F))) h

end Matrix.SpecialLinearGroup
