module
public import Theory.Mathieu.M12.ExceptionalParabolics.EightExtensions.Automorphisms

/-!
# Restrictions of 128 explicit endpoint automorphism words

The tables give words in the four certified automorphisms and their images of
the three literal overlap generators. The three generator-image certificates
are checked separately. Tables are stored in blocks of sixteen to keep kernel
lookup paths short. Source: the marked M₁₂ local model in
`SmallParabolicPair.Seeds`, following Aschbacher--Smith 14.2.21, printed p.988.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.EightExtensions
set_option maxRecDepth 1000000
set_option Elab.async false

def candidateTable : Array (Array (List (Fin 4))) := #[
  #[[],[0],[1],[2],[3],[0,0],[1,0],[2,0],[3,0],[2,1],[3,1],[0,2],[3,2],[0,3],[2,3],[0,0,0]],
  #[[1,0,0],[2,0,0],[3,0,0],[2,1,0],[3,1,0],[0,2,0],[3,2,0],[0,3,0],[2,3,0],[0,2,1],[3,2,1],[0,3,1],[2,3,1],[0,0,2],[2,0,2],[3,0,2]],
  #[[0,3,2],[2,3,2],[0,0,3],[2,0,3],[3,0,3],[0,2,3],[3,2,3],[1,0,0,0],[2,0,0,0],[3,0,0,0],[2,1,0,0],[3,1,0,0],[0,2,0,0],[3,2,0,0],[0,3,0,0],[2,3,0,0]],
  #[[0,2,1,0],[3,2,1,0],[0,3,1,0],[2,3,1,0],[0,0,2,0],[2,0,2,0],[3,0,2,0],[2,3,2,0],[0,0,3,0],[2,0,3,0],[3,0,3,0],[3,2,3,0],[0,0,2,1],[2,0,2,1],[3,0,2,1],[0,3,2,1]],
  #[[2,3,2,1],[0,0,3,1],[2,0,3,1],[3,0,3,1],[0,2,3,1],[3,2,3,1],[0,0,0,2],[2,0,0,2],[0,2,0,2],[0,3,0,2],[2,3,0,2],[0,2,3,2],[3,2,3,2],[0,2,0,3],[0,3,0,3],[0,3,2,3]],
  #[[2,1,0,0,0],[3,1,0,0,0],[0,2,0,0,0],[0,3,0,0,0],[0,2,1,0,0],[3,2,1,0,0],[0,3,1,0,0],[2,3,1,0,0],[3,0,2,0,0],[2,0,3,0,0],[0,0,2,1,0],[2,0,2,1,0],[3,0,2,1,0],[2,3,2,1,0],[0,0,3,1,0],[2,0,3,1,0]],
  #[[3,0,3,1,0],[3,2,3,1,0],[0,0,0,2,0],[2,0,0,2,0],[0,2,0,2,0],[2,3,0,2,0],[0,2,3,2,0],[3,2,3,2,0],[0,3,0,3,0],[0,3,2,3,0],[0,0,0,2,1],[2,0,0,2,1],[0,2,0,2,1],[0,3,0,2,1],[2,3,0,2,1],[0,2,3,2,1]],
  #[[3,2,3,2,1],[0,2,0,3,1],[0,3,0,3,1],[0,3,2,3,1],[0,2,1,0,0,0],[0,3,1,0,0,0],[3,0,2,1,0,0],[2,0,3,1,0,0],[0,0,0,2,1,0],[2,0,0,2,1,0],[0,2,0,2,1,0],[2,3,0,2,1,0],[0,2,3,2,1,0],[3,2,3,2,1,0],[0,3,0,3,1,0],[0,3,2,3,1,0]]]

def candidateWord (k : Fin 128) : List (Fin 4) :=
  (candidateTable[k.val / 16]!)[k.val % 16]!

def candidateImage (k : Fin 128) (i : Fin 192) : Fin 192 := wordImage (candidateWord k) i

def restrictionTable : Array (Array (Array (Fin 64))) := #[
  #[#[1,2,3],#[58,23,51],#[1,2,13],#[23,56,48],#[2,1,49],#[11,2,13],#[58,23,55],#[12,1,16],#[23,58,44],#[23,56,18],#[2,1,21],#[2,1,48],#[58,20,45],#[23,58,21],#[56,23,15],#[56,23,55]],
  #[#[11,2,3],#[20,56,18],#[12,1,21],#[12,1,46],#[23,58,14],#[20,58,46],#[11,2,19],#[2,11,44],#[1,12,24],#[2,1,18],#[58,20,15],#[23,58,49],#[56,23,45],#[23,58,48],#[56,23,3],#[1,2,45]],
  #[#[11,12,19],#[12,11,21],#[2,11,49],#[1,12,45],#[58,23,13],#[1,2,24],#[20,58,18],#[56,23,51],#[2,1,46],#[20,58,14],#[20,56,48],#[12,1,49],#[12,1,18],#[56,20,15],#[20,58,49],#[58,23,45]],
  #[#[20,58,16],#[11,2,24],#[2,11,14],#[1,12,19],#[12,11,16],#[11,12,55],#[56,23,24],#[20,56,14],#[23,56,44],#[56,20,24],#[1,12,51],#[2,11,46],#[23,58,18],#[56,23,13],#[1,2,15],#[11,12,24]],
  #[#[12,11,49],#[2,11,21],#[1,12,15],#[58,23,3],#[1,2,19],#[20,58,48],#[2,11,48],#[1,12,3],#[1,2,51],#[58,23,19],#[23,56,21],#[20,56,49],#[11,12,13],#[58,20,19],#[11,2,55],#[12,11,18]],
  #[#[2,1,16],#[20,58,44],#[23,58,16],#[12,11,14],#[12,1,48],#[56,20,45],#[20,58,21],#[58,23,15],#[11,2,15],#[11,12,15],#[12,11,46],#[11,12,51],#[56,23,19],#[20,56,44],#[23,56,14],#[56,20,19]],
  #[#[1,12,55],#[2,11,16],#[20,56,46],#[58,20,51],#[56,20,3],#[2,1,44],#[12,1,14],#[56,20,55],#[58,20,13],#[23,56,16],#[2,11,18],#[1,12,13],#[1,2,55],#[58,23,24],#[23,56,49],#[20,56,21]],
  #[#[11,12,3],#[58,20,24],#[11,2,51],#[12,11,48],#[23,58,46],#[12,11,44],#[11,2,45],#[11,12,45],#[20,56,16],#[58,20,55],#[56,20,13],#[2,1,14],#[12,1,44],#[56,20,51],#[58,20,3],#[23,56,46]]]

def restriction (k : Fin 128) (j : Fin 3) : Fin 64 :=
  ((restrictionTable[k.val / 16]!)[k.val % 16]!)[j.val]!

private theorem candidateImage_generator_0 : ∀ k,
    candidateImage k (Coordinates.overlapIndex 1) =
      Coordinates.overlapIndex (restriction k 0) := by decide +kernel

private theorem candidateImage_generator_1 : ∀ k,
    candidateImage k (Coordinates.overlapIndex 2) =
      Coordinates.overlapIndex (restriction k 1) := by decide +kernel

private theorem candidateImage_generator_2 : ∀ k,
    candidateImage k (Coordinates.overlapIndex 3) =
      Coordinates.overlapIndex (restriction k 2) := by decide +kernel

theorem candidateImage_generators (k : Fin 128) (j : Fin 3) :
    candidateImage k (Coordinates.overlapIndex ⟨j.val + 1, by omega⟩) =
      Coordinates.overlapIndex (restriction k j) := by
  fin_cases j
  · exact candidateImage_generator_0 k
  · exact candidateImage_generator_1 k
  · exact candidateImage_generator_2 k

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.EightExtensions
