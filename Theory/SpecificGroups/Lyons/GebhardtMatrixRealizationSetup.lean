module

public import Theory.SpecificGroups.Lyons.GebhardtPresentation
public import Theory.SpecificGroups.Lyons.Atlas111LocalIndexSetup

/-!
# Data for Gebhardt matrix realization certificates

Four words in the literal ATLAS local pair and one word in the ambient pair
specify candidate images of `a,b,c,d,z`. Two further words in these five
images recover the ambient generators. A certificate consists of the 25
relator identities and the two recovery identities in the faithful matrix
representation. The universal property of the presentation then gives a
surjective homomorphism; membership of the first four images in the specified
local subgroup follows directly from their words.

The assembly is proved in `GebhardtMatrixRealization`. Keeping the data
contract here allows concrete words and arithmetic certificates to feed that
module without an import cycle. No generator correspondence is assumed.

Source: V. Gebhardt, "Two Short Presentations for Lyons' Sporadic Simple
Group", Experimental Mathematics 9 (2000), 333–338, Section 3B. See
`GebhardtPresentation` for the literal relations and `Atlas111OrderSetup`
for the exact local pair. The source's five generators are distinct from
the two ATLAS standard generators.
-/

namespace Lyons.Gebhardt.MatrixRealization

/-- The local pair, with `false` selecting the first ATLAS program output. -/
@[expose] public def localPair : Bool → LyonsGroup
  | false => OrderCertificate.localA
  | true => OrderCertificate.localB

/-- Every word in the local pair belongs to the specified local subgroup. -/
public theorem localWord_mem (w : FreeGroup Bool) :
    FreeGroup.lift localPair w ∈ OrderCertificate.localSubgroup := by
  apply FreeGroup.range_lift_le (s := OrderCertificate.localSubgroup) ?_ ⟨w, rfl⟩
  rintro _ ⟨b, rfl⟩
  cases b
  · exact OrderCertificate.localA_mem
  · exact OrderCertificate.localB_mem

/-- Candidate words, without any unproved identification or generation claim. -/
public structure WordData where
  /-- Images of `a,b,c,d`, as words in `localA,localB`. -/
  localWords : Fin 4 → FreeGroup Bool
  /-- Image of `z`, as a word in `generatorA,generatorB`. -/
  outerWord : FreeGroup Bool
  /-- A word in `a,b,c,d,z` that should recover `generatorA`. -/
  recoverA : FreeGroup Alphabet
  /-- A word in `a,b,c,d,z` that should recover `generatorB`. -/
  recoverB : FreeGroup Alphabet

/-- Interpret the candidate five generators in the fixed matrix group. -/
@[expose] public def WordData.assignment (w : WordData) (i : Alphabet) : LyonsGroup :=
  if h : i.val < 4 then FreeGroup.lift localPair (w.localWords ⟨i.val, h⟩)
  else FreeGroup.lift OrderCertificate.indexGenerator w.outerWord

/-- The first four images lie in the required subgroup by construction. -/
public theorem WordData.assignment_mem (w : WordData) (i : Alphabet) (hi : i.val < 4) :
    w.assignment i ∈ OrderCertificate.localSubgroup := by
  simp only [WordData.assignment, dif_pos hi]
  exact localWord_mem _

/-- The finite matrix identities needed for the realization.

No order, simplicity, subgroup recognition, or coset bound enters this contract.
The `relations` field ranges over the literal 25 words in `GebhardtPresentation`.
-/
public structure WordCertificate (w : WordData) : Prop where
  relations : ∀ r ∈ relators,
    matrixRepresentation (FreeGroup.lift w.assignment r) = 1
  recoverA : matrixRepresentation (FreeGroup.lift w.assignment w.recoverA) = atlasAMatrix
  recoverB : matrixRepresentation (FreeGroup.lift w.assignment w.recoverB) = atlasBMatrix

end Lyons.Gebhardt.MatrixRealization
