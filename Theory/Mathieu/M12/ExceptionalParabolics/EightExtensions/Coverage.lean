module
public import Theory.Mathieu.M12.ExceptionalParabolics.EightExtensions.Restrictions
public import Theory.Mathieu.M12.Properties.SylowAutomorphismGroup.Certificate

/-!
# Coverage of the eight-preserving M₁₂ overlap restrictions

The 128 listed words in the four certified endpoint automorphisms have the
listed images of the overlap generators. The existing seven power tests on a
triple, together with membership of the product of its first two entries in
the specified eight, imply that it is one of these triples. This finite
implication does not assume that a candidate triple already defines a homomorphism.
The final extension theorem applies it to the images under an actual automorphism.

All tables are untrusted data checked in the kernel; `source/generate.py`
reconstructs them. Source: the marked permutations of `SmallParabolicPair.Seeds`
and the M₁₂ case of Aschbacher--Smith F.1.11--12, printed pp.262--263.
-/

@[expose] public section
namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.EightExtensions
set_option maxRecDepth 1000000
set_option Elab.async false

def inEight (i : Fin 64) : Prop :=
  i = 0 ∨ i = 4 ∨ i = 5 ∨ i = 25 ∨ i = 35 ∨ i = 39 ∨ i = 41 ∨ i = 42

instance inEightDecidable (i : Fin 64) : Decidable (inEight i) := inferInstanceAs (Decidable (_ ∨ _))

private def pairIndex : Array ℕ := #[0,0,1,0,0,0,0,0,0,0,0,2,3,0,0,0,0,0,0,0,4,0,0,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,6,0,7,0,0,0,0,0]
private def thirdIndex : Array ℕ := #[0,0,0,0,0,0,0,0,0,0,0,0,0,1,2,3,4,0,5,6,0,7,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,10,11,0,12,13,0,14,0,0,0,15,0,0,0,0,0,0,0,0]
private def choiceTable : Array (Array (Array (Fin 128))) := #[
  #[#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,2,0,62,0,0,68,0,37,0,31,0,0,0,72,108],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[71,107,0,66,0,0,51,0,24,0,35,0,0,0,58,96],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
  #[#[0,0,123,0,80,25,0,10,0,101,0,40,11,4,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,50,0,97,106,0,65,0,23,0,59,70,34,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
  #[#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[16,5,0,88,0,0,22,0,49,0,118,0,0,0,114,78],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[112,76,0,89,0,0,32,0,63,0,119,0,0,0,91,53],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
  #[#[0,0,102,0,7,44,0,18,0,124,0,19,84,43,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,83,0,52,79,0,33,0,117,0,90,115,64,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
  #[#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,55,0,120,17,0,111,0,93,0,98,42,75,0,0],#[0,0,41,0,48,38,0,86,0,81,0,21,69,46,0,0]],
  #[#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,94,0,105,9,0,74,0,56,0,127,3,110,0,0],#[0,0,20,0,82,60,0,13,0,8,0,116,29,27,0,0]],
  #[#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[100,122,0,45,0,0,95,0,57,0,85,0,0,0,125,103],#[30,61,0,14,0,0,92,0,54,0,28,0,0,0,39,15],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]],
  #[#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[126,104,0,26,0,0,77,0,113,0,12,0,0,0,99,121],#[67,36,0,87,0,0,73,0,109,0,47,0,0,0,1,6],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]]]

private def choice (a b c : Fin 64) : Fin 128 :=
  ((choiceTable[pairIndex[a.val]!]!)[pairIndex[b.val]!]!)[thirdIndex[c.val]!]!

set_option maxHeartbeats 2000000 in
/-- Necessary order tests and the image of the marked product suffice to select
one of the explicit endpoint automorphisms. -/
theorem covers : ∀ a b c : Fin 64,
    SylowAutomorphismGroup.admissible a b c →
    inEight (SylowAutomorphismGroup.multiply a b) →
    ∃ k : Fin 128, ∀ j : Fin 3,
      candidateImage k (Coordinates.overlapIndex ⟨j.val + 1, by omega⟩) =
        Coordinates.overlapIndex (![a,b,c] j) := by
  have check : ∀ a : Fin 64, SylowAutomorphismGroup.powerTest a 4 →
      ∀ b : Fin 64, SylowAutomorphismGroup.powerTest b 4 →
      SylowAutomorphismGroup.powerTest (SylowAutomorphismGroup.multiply a b) 2 →
      inEight (SylowAutomorphismGroup.multiply a b) →
      ∀ c : Fin 64, SylowAutomorphismGroup.powerTest c 8 →
      SylowAutomorphismGroup.powerTest (SylowAutomorphismGroup.multiply a c) 4 →
      SylowAutomorphismGroup.powerTest (SylowAutomorphismGroup.multiply b c) 2 →
      SylowAutomorphismGroup.powerTest
        (SylowAutomorphismGroup.multiply (SylowAutomorphismGroup.multiply a c) c) 2 →
      ∀ j : Fin 3, restriction (choice a b c) j = ![a,b,c] j := by
    intro a
    fin_cases a <;> decide +kernel
  rintro a b c ⟨ha,hb,hc,hab,hac,hbc,hacc⟩ he
  have hk := check a ha b hb hab he c hc hac hbc hacc
  exact ⟨choice a b c, fun j =>
    (candidateImage_generators _ j).trans (congrArg _ (hk j))⟩

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.EightExtensions
