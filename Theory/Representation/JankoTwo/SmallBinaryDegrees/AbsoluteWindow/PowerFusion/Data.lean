module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order

/-!
# Literal representatives for the Hall--Janko power-fusion calculation

The twenty-one candidate representatives and their fusion conjugators are elements
of the degree-100 ATLAS carrier, expressed using its certified four transversals.
Membership follows from `FirstParabolic.normalForm_mem`. Their fusion identities
are checked in `Checks`; exhaustive conjugacy coverage is a separate obligation.

Source: R. A. Wilson et al., ATLAS `J2G1-p100B0`, with the original attribution in
`Theory/SpecificGroups/LeechRelated/AtlasCarriers/source/README.md`. The adjacent
`source/` directory preserves the GAP word candidates and their conversion to
normal-form indices. External computations supply witnesses only.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.PowerFusionCertificate

open GeneratorPair.SecondOrbitCertificate

/-- A certified normal form, regarded as an element of the literal carrier. -/
def element (i : Index) : Carrier :=
  ⟨normalForm i, ExceptionalParabolics.FirstParabolic.normalForm_mem i⟩

@[simp] theorem inclusion_element (i : Index) : inclusion (element i) = normalForm i := rfl

/-- The normal forms cover the carrier, independently of conjugacy calculations. -/
theorem element_surjective : Function.Surjective element := by
  intro g
  obtain ⟨i, hi⟩ := normalForm_cover g
  exact ⟨i, inclusion_injective hi.symm⟩

/-- Indices of the twenty-one candidate conjugacy representatives. -/
def representativeIndex (i : Fin 21) : Index :=
  match i.val with
  | 0 => (0, 0, 0, 0)
  | 1 => (29, 26, 16, 1)
  | 2 => (56, 16, 8, 2)
  | 3 => (80, 26, 8, 2)
  | 4 => (50, 21, 7, 2)
  | 5 => (91, 27, 15, 0)
  | 6 => (56, 37, 4, 0)
  | 7 => (97, 13, 17, 1)
  | 8 => (75, 12, 0, 0)
  | 9 => (64, 17, 9, 0)
  | 10 => (30, 35, 0, 1)
  | 11 => (41, 56, 21, 2)
  | 12 => (67, 17, 13, 3)
  | 13 => (45, 47, 5, 0)
  | 14 => (29, 54, 15, 3)
  | 15 => (25, 25, 20, 2)
  | 16 => (89, 50, 12, 1)
  | 17 => (41, 20, 20, 1)
  | 18 => (77, 46, 18, 0)
  | 19 => (72, 32, 12, 1)
  | _ => (76, 9, 12, 1)

/-- Indices of carrier conjugators taking the eighth power to the thirty-second. -/
def conjugatorIndex (i : Fin 21) : Index :=
  match i.val with
  | 0 => (0, 0, 0, 0)
  | 1 => (0, 0, 0, 0)
  | 2 => (42, 55, 18, 2)
  | 3 => (42, 55, 18, 2)
  | 4 => (27, 15, 18, 2)
  | 5 => (27, 15, 18, 2)
  | 6 => (0, 0, 0, 0)
  | 7 => (0, 0, 0, 0)
  | 8 => (0, 0, 0, 0)
  | 9 => (0, 0, 0, 0)
  | 10 => (47, 17, 8, 2)
  | 11 => (47, 17, 8, 2)
  | 12 => (47, 17, 8, 2)
  | 13 => (47, 17, 8, 2)
  | 14 => (0, 0, 0, 0)
  | 15 => (57, 47, 4, 1)
  | 16 => (57, 47, 4, 1)
  | 17 => (0, 0, 0, 0)
  | 18 => (0, 0, 0, 0)
  | 19 => (39, 49, 18, 3)
  | _ => (0, 0, 0, 0)

/-- Candidate class representatives in the literal ATLAS carrier. -/
def representative (i : Fin 21) : Carrier := element (representativeIndex i)

/-- The explicit conjugator for the indicated representative. -/
def conjugator (i : Fin 21) : Carrier := element (conjugatorIndex i)

/-- The remaining exhaustive-coverage obligation. The finite fusion identities
alone do not establish this proposition. -/
def RepresentativeCoverage : Prop :=
  ∀ g : Carrier, ∃ i : Fin 21, IsConj (representative i) g

/-- A coverage certificate on the existing normal forms suffices for the actual
carrier. This transports coverage; it does not assert it. -/
theorem representativeCoverage_of_normalForms
    (h : ∀ j : Index, ∃ i : Fin 21, IsConj (representative i) (element j)) :
    RepresentativeCoverage := by
  intro g
  obtain ⟨j, rfl⟩ := element_surjective g
  exact h j

end Sporadic.LeechRelated.J2.PowerFusionCertificate
