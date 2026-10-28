module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Coordinates

/-!
# Concrete words for the four max2 involution fibers

The four lifts are words in the original ATLAS outputs, transported by the
certified conjugation equivalence. Eleven further words fix the contracts for
finite fiber coverage and ambient fusion. Their proposed orbit sizes are only
numerical bounds to be proved, not assertions of a class table.

The witness words were found by finite exploration of the certified row
quotient and the 8192 binary kernel products. The motivation for counting their
classes is Aschbacher--Smith, `refs/quasithin.pdf`, pp.64--65, A.6.1--4.
-/

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound Coordinates

/-- The actual image of the certified row quotient. -/
abbrev Q := quotientSubgroup

/-- The quotient homomorphism with its actual image as codomain. -/
noncomputable def q : H →* Q :=
  localQuotientMap.codRestrict quotientSubgroup (fun u => by
    rw [← localQuotientMap_range]
    exact ⟨u, rfl⟩)

@[simp] theorem coe_q (u : H) : (q u : QuotientMatrixˣ) = localQuotientMap u := rfl

theorem q_surjective : Function.Surjective q := by
  intro u
  have hu : u.val ∈ localQuotientMap.range := by
    rw [localQuotientMap_range]
    exact u.property
  obtain ⟨v, hv⟩ := hu
  exact ⟨v, Subtype.ext hv⟩

/-- Four fixed lifts; quotient involution coverage remains a certificate. -/
def sourceLift : Fin 4 → sourceSubgroup :=
  ![1, sourceX, (sourceX * sourceY)^7, ((sourceX * sourceY)^5 * sourceY)^4]

noncomputable def lift (j : Fin 4) : H := sourceSubgroupEquivLocal (sourceLift j)

/-- Which of the four fibers contains a prescribed representative. -/
def fiberIndex : Fin 11 → Fin 4 := ![0, 0, 0, 0, 1, 2, 2, 3, 3, 3, 3]

/-- Binary masks in the already certified increasing-bit product convention. -/
def kernelIndex : Fin 11 → Fin 8192 := ![0, 1, 6, 26, 0, 0, 1, 0, 12, 304, 305]

/-- Eleven actual elements of H, with no assumed classification or fusion. -/
noncomputable def representative (i : Fin 11) : H :=
  localKernelProduct (kernelIndex i) * lift (fiberIndex i)

@[simp] theorem q_localKernelProduct (i : Fin 8192) : q (localKernelProduct i) = 1 := by
  apply Subtype.ext
  exact (localQuotientMap_sourceEquiv (kernelProduct i)).trans
    (map_kernelProduct_eq_one quotientMap quotientMap_seed i)

@[simp] theorem q_representative (i : Fin 11) :
    q (representative i) = q (lift (fiberIndex i)) := by
  rw [representative, map_mul, q_localKernelProduct, one_mul]

/-- Proposed bounds for the four quotient classes, still requiring certificates. -/
def quotientBound : Fin 4 → ℕ := ![1, 4158, 990, 1155]

/-- Proposed bounds in a single quotient fiber for the eleven local classes. -/
def fiberBound : Fin 11 → ℕ := ![1, 1, 1386, 2772, 128, 64, 64, 96, 192, 16, 16]

/-- The target of ambient fusion for each representative. -/
def firstTarget : Fin 11 → Model := ![1, z, z, t, t, z, t, z, t, t, z]

/-- The target of ambient fusion after multiplication by the marked involution. -/
def secondTarget : Fin 11 → Model := ![z, 1, z, t, t, t, z, z, t, z, t]

/-- The three requested B,B representatives, in increasing bound order. -/
noncomputable def bbRepresentative : Fin 3 → H :=
  ![representative 3, representative 8, representative 4]

/-- Evaluate signed letters in the original ATLAS source subgroup. -/
def sourceLetter (i : ℤ) : sourceSubgroup :=
  if i = 1 then sourceX else if i = -1 then sourceX⁻¹ else
    if i = 2 then sourceY else if i = -2 then sourceY⁻¹ else 1

def sourceWord (w : List ℤ) : sourceSubgroup := (w.map sourceLetter).prod

/-- Explicit candidate quotient-centralizer generators. Their centralizer
membership and generation are separate finite certificates. -/
def actorWords : Fin 4 → List (List ℤ) :=
  ![[[1],
    [2]],
    [[-1],
    [-1],
    [-1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, 2,
      -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2,
      1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, -1, -2, -1, -2, -1, 2,
      -1, 2, -1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, -1, -2,
      -1, -2, -1, 2, -1, -2, -1, 2, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2],
    [2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, 1, -2,
      1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1,
      2, -1, 2, -1, -2, -1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1,
      -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, -1, -2, -1, 2, -1]],
    [[-2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1],
    [2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 2,
      -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1],
    [-1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, 2,
      -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -2, 1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1,
      -2, -1, 2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1],
    [1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1,
      -2, 1, 2, 1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2,
      1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, -1, 2, -1, -2,
      -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -2]],
    [[-1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, 2,
      -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2,
      1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, -1, -2, -1, -2, -1, 2,
      -1, 2, -1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1,
      -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1],
    [-1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, 2, -1, 2,
      -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1,
      -2, 1, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -1, 2, -1, -2, -1, -2, -1, 2, -1,
      2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2],
    [1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1,
      -2, 1, 2, 1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, -1,
      2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -2, 1, 2, 1, -2, 1, 2,
      1, 2, 1, -2, 1, -2, 1, 2],
    [-2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, 2, -1,
      -2, -1, 2, -1, -2, -1, 2, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2],
    [1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1,
      -2, 1, 2, 1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2,
      1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2,
      1, -2, 1, 2, 1, 2, 1, -2, 1, -2, -1, -2, -1]]]

/-- Literal local lifts of the signed actor words. -/
noncomputable def actors (j : Fin 4) : List H :=
  (actorWords j).map (fun w => sourceSubgroupEquivLocal (sourceWord w))

noncomputable def quotientActors (j : Fin 4) : List Q := (actors j).map q

end Janko4.Cardinality.LocalInvolutionCensus
