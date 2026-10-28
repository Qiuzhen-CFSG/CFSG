module

public import Theory.SpecificGroups.ONan.ProjectiveSimplicity.PrimeCoverage.Reduction
public import Theory.GroupTheory.BinaryNormalForm

/-!
# Fixed binary words for an O'Nan two-subgroup certificate

The ATLAS program `ONG1-max9W1` specifies two words in the actual projective
matrix generators. Nine further words specify candidate binary normal forms.
The definitions assert no order, closure, distinctness, or fusion property.
Those finite matrix identities are separate certification obligations.

`PrimeCoverage/Two.lean` assembles closure, distinctness and involution fusion
into local coverage of order two. The two types of certificate can therefore
be checked independently against these fixed words.

Source: R. A. Wilson, R. A. Parker, J. N. Bray and the ATLAS contributors,
https://brauer.maths.qmul.ac.uk/Atlas/spor/ON/words/ONG1-max9W1.
The source program, derived word table, and discovery procedure are in
`Two/source/`. External computations are only discovery aids.
-/

@[expose] public section

namespace ONan.Simplicity.TwoCertificate

/-- Evaluation of the two outputs of the preserved ATLAS program. -/
def localGenerators {G : Type*} [Group G] (a b : G) : Fin 2 → G :=
  let c := a * b
  let d := c * b
  let e := c * d
  let f := c * e
  let h := c * (f * e)
  ![(c ^ 4)⁻¹ * a * c ^ 4, (d ^ 4)⁻¹ * h ^ 4 * d ^ 4]

/-- Zero-based generator indices; products are read from left to right. -/
def basisWords : Fin 9 → List (Fin 2) :=
  ![[0, 1, 1, 0, 1, 0, 1],
    [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0],
    [0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0],
    [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0],
    [1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1],
    [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1],
    [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0],
    [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0],
    [1, 0, 1, 1, 0, 1, 0, 1, 1] ]

/-- The nine candidate binary generators in any group. -/
def basis {G : Type*} [Group G] (a b : G) (i : Fin 9) : G :=
  ((basisWords i).map (localGenerators a b)).prod

/-- The candidate binary generators in the supplied projective matrix model. -/
def generators : Fin 9 → Model := basis generatorA generatorB

/-- The 512 specified ordered products, before any uniqueness assertion. -/
def normalForm : (Fin 9 → Bool) → Model :=
  Subgroup.BinaryNormalForm.product generators

/-- The first local generator is already conjugate to the fixed involution. -/
theorem localGenerator_zero_conjugate :
    generatorA = (generatorA * generatorB) ^ 4 *
      localGenerators generatorA generatorB 0 * ((generatorA * generatorB) ^ 4)⁻¹ := by
  simp [localGenerators, mul_assoc]

end ONan.Simplicity.TwoCertificate
