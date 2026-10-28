module

public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.Model
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.CosetIdentification.OrbitCoordinates
public import Theory.Representation.HexacodeAction.TwelveDimensionalExclusion.CosetFiltration.CosetIdentification.WordGeometry
/-!
# From fixed-word geometry to literal central-coset coordinates

A bijection from the 135 listed central translates to the actual left-coset
space gives index 135. Since the cover has order 1080, the original subgroup
has order eight and is Sylow. The central-orbit coefficient construction
then gives an F-linear equivalence from the published 45-dimensional space
to the literal omega-eigenspace. Its standard coordinate vectors are exactly
the central projectors of the selected cosets. The ninety transporter
memberships prove both published generator equations.

`WordGeometry` proves `CosetTransversal` and `WordTransitions` for the original
published words. Substituting these certificates constructs `cosetCoordinates`
and proves `exists_cosetCoordinates` unconditionally. The filtration corollary
retains the independent word filtration; its discharge belongs to the parent
coset-filtration assembly. No filtration or irreducibility is used to construct
the coordinates.

Source: Aschbacher–Smith K.1.3, printed p.453 / PDF p.464, citing GM02
Theorem 6.2 and Table 6.3. The concrete ATLAS carrier is attributed to
Gerald Höhn and the ATLAS contributors; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public section
open Atlas.Codes
namespace Representation.Hexacode.TwelveDimensional.CosetCertificate.CosetIdentification

/-- The coordinate vectors are precisely the central projectors of the selected cosets. -/
theorem orbitCoordinates_single {P : Subgroup Cover} (q : Fin 45 → Cover ⧸ P)
    (hq : Function.Bijective (orbitPoint q)) (i : Fin 45) :
    orbitCoordinates q hq (Pi.single i 1) =
      ⟨centralProjector (cosetRepresentation P) (MonoidAlgebra.single (q i) 1),
        centralProjector_mem (cosetRepresentation P) _⟩ := by
  classical
  apply sample_injective q hq.2
  rw [sample_orbitCoordinates]
  funext r
  have h0 : q i = q r ↔ i = r := by
    constructor
    · intro h
      have hh : (i, (0 : Fin 3)) = (r, 0) := hq.1 (by simpa [orbitPoint] using h)
      exact congrArg Prod.fst hh
    · rintro rfl
      rfl
  have h1 : hexEvenZ • q i ≠ q r := by
    intro h
    have hh : (i, (1 : Fin 3)) = (r, 0) := hq.1 (by simpa [orbitPoint] using h)
    exact (by decide : (1 : Fin 3) ≠ 0) (congrArg Prod.snd hh)
  have h2 : hexEvenZ • (hexEvenZ • q i) ≠ q r := by
    intro h
    have hh : (i, (2 : Fin 3)) = (r, 0) :=
      hq.1 (by simpa [orbitPoint, pow_two, mul_smul] using h)
    exact (by decide : (2 : Fin 3) ≠ 0) (congrArg Prod.snd hh)
  change (Pi.single i (1 : F) : Space) r =
    (centralProjector (cosetRepresentation P) (MonoidAlgebra.single (q i) 1)).coeff (q r)
  simp [centralProjector, Representation.ofMulAction_single, MonoidAlgebra.coeff_add,
    MonoidAlgebra.coeff_single, Finsupp.single_apply, h0, h1, h2, Pi.single_apply, eq_comm]

/-- The transversal determines the index in the actual cover. -/
theorem candidate_index (h : CosetTransversal) : candidateSubgroup.index = 135 := by
  change Nat.card (Cover ⧸ candidateSubgroup) = 135
  rw [← Nat.card_congr (_root_.Equiv.ofBijective (orbitPoint basepoint) h)]
  simp only [Nat.card_prod, Nat.card_fin]

/-- Lagrange's theorem and the proved order 1080 force the subgroup to have order eight. -/
theorem candidate_card (h : CosetTransversal) : Nat.card candidateSubgroup = 8 := by
  have hc := candidateSubgroup.card_mul_index
  rw [candidate_index h, hexEven_card] at hc
  omega

/-- Exact coset enumeration supplies Sylow maximality; no extra Sylow premise is used. -/
noncomputable def candidateSylow (h : CosetTransversal) : Sylow 2 Cover :=
  Sylow.ofCard candidateSubgroup (by rw [candidate_card h, hexEven_card]; decide +kernel)

@[simp] theorem candidateSylow_coe (h : CosetTransversal) :
    (candidateSylow h : Subgroup Cover) = candidateSubgroup := rfl

/-- The finite word certificates yield all fields of the original coordinate contract. -/
noncomputable def coordinatesOfWords (hT : CosetTransversal) (hG : WordTransitions) :
    CosetCoordinates where
  sylow := candidateSylow hT
  coordinates := orbitCoordinates basepoint hT
  generator_coordinates := orbitCoordinates_generator basepoint hT (inverse_generator_basepoint hG)

theorem exists_cosetCoordinates_of_wordCertificates
    (hT : CosetTransversal) (hG : WordTransitions) : Nonempty CosetCoordinates :=
  ⟨coordinatesOfWords hT hG⟩

/-- Consumer application: the independent word filtration is kept explicit. -/
theorem cosetFiltration_of_wordCertificates (hT : CosetTransversal) (hG : WordTransitions)
    (hfil : FactorDegreeFiltration ({3, 9} : Set ℕ) representation) : CosetFiltration :=
  cosetFiltration_of_wordFiltration (coordinatesOfWords hT hG) hfil

end Representation.Hexacode.TwelveDimensional.CosetCertificate.CosetIdentification

namespace Representation.Hexacode.TwelveDimensional.CosetCertificate
open CosetIdentification

/-- The certified coordinates for the original Sylow subgroup in the literal
omega-eigenspace of its left-coset permutation module. -/
noncomputable def cosetCoordinates : CosetCoordinates :=
  coordinatesOfWords cosetTransversal wordTransitions

/-- The coordinate construction uses the closure of all three published Sylow words. -/
@[simp] theorem cosetCoordinates_sylow :
    (cosetCoordinates.sylow : Subgroup Cover) = candidateSubgroup := rfl

/-- The literal central coset coordinates exist without a filtration premise. -/
theorem exists_cosetCoordinates : Nonempty CosetCoordinates := ⟨cosetCoordinates⟩

/-- Consumer application with the concrete coordinate certificate discharged.
The independent word filtration remains the parent assembly's premise. -/
theorem cosetFiltration_of_certified_wordFiltration
    (hfil : FactorDegreeFiltration ({3, 9} : Set ℕ) representation) : CosetFiltration :=
  cosetFiltration_of_wordFiltration cosetCoordinates hfil

end Representation.Hexacode.TwelveDimensional.CosetCertificate
