module

public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates.First
public import Theory.SpecificGroups.Janko4.Model.ThreeConjugates.Second

/-!
# Three-conjugate generation for the actual J₄ model

The two certified triples and the proved involution-class coverage give a
generating triple for every involution of the binary ATLAS carrier. Full
innerness then gives the automorphism version, with conjugators in that same
carrier and with the literal conjugation homomorphism.

Source: Revin–Zavarnitsine, https://arxiv.org/abs/2505.05173v2, Theorem 1.
The inherited simple and perfect hypotheses are needed only in the passage
to automorphisms; the element-generation theorem has no such premises.
-/

public section
namespace Janko4.ThreeConjugates
open Theory.GroupTheory

/-- Every nonidentity involution has three conjugates generating the actual model. -/
theorem involutions_generate {x : Model} (hx : x ≠ 1) (hx2 : x ^ 2 = 1) :
    ThreeConjugatesGenerate x :=
  involutions_of_representatives first_three_conjugates_generate
    second_three_conjugates_generate hx hx2

/-- Every involutory automorphism has three inner conjugates whose generated
subgroup contains the whole inner automorphism group. -/
theorem automorphisms [IsSimpleGroup Model] [Group.IsPerfect Model] :
    ThreeConjugateAutomorphisms Model :=
  automorphisms_of_representatives first_three_conjugates_generate
    second_three_conjugates_generate

end Janko4.ThreeConjugates
