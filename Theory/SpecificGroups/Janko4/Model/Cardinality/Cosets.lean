module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.Cosets.FixedVector
public import Theory.GroupTheory.PresentedGroupBounds

/-!
# Coset certificates from the concrete J₄ vector orbit

We construct genuine right-coset transitions from a parametrization of the
orbit defined in `Cosets.Orbit`. Choose one matrix-group element over each
orbit point, choosing the identity over the base point. The fiber criterion
then expresses right multiplication by each generator (or its inverse) as a
subgroup element times another representative. If the subgroup is the full
vector stabilizer, these right cosets are also distinct.

`max1_cosetCertificate_of_vectorOrbit` reduces the requested certificate to the
orbit count and the reverse stabilizer inclusion. These two concrete hypotheses
remain separate obligations; this module does not assert the index itself.
The proposed index comes from the ATLAS subgroup entry:
https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/J4G1-max1W1 .
-/

public section
namespace Janko4.Cardinality

private noncomputable def orbitRepresentative (x : CosetVectorOrbit) : Model :=
  if x = cosetOrbitPoint 1 then 1 else (cosetOrbitPoint_surjective x).choose

private theorem orbitRepresentative_initial : orbitRepresentative (cosetOrbitPoint 1) = 1 := by
  simp [orbitRepresentative]

private theorem orbitRepresentative_point (x : CosetVectorOrbit) :
    cosetOrbitPoint (orbitRepresentative x) = x := by
  classical
  unfold orbitRepresentative
  split
  · next h => exact h.symm
  · exact (cosetOrbitPoint_surjective x).choose_spec

private theorem orbitRepresentative_step
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hst : cosetVectorStabilizer ≤ max1Subgroup hA hB)
    (x : CosetVectorOrbit) (g : Model) :
    ∃ h : max1Subgroup hA hB, ∃ y : CosetVectorOrbit,
      orbitRepresentative x * g = h.val * orbitRepresentative y := by
  let y := cosetOrbitPoint (orbitRepresentative x * g)
  have he : cosetOrbitMap (orbitRepresentative x * g) =
      cosetOrbitMap (orbitRepresentative y) :=
    (congrArg Subtype.val (orbitRepresentative_point y)).symm
  have hm : (orbitRepresentative x * g) * (orbitRepresentative y)⁻¹ ∈
      max1Subgroup hA hB := hst ((cosetOrbitMap_eq_iff _ _).mp he)
  exact ⟨⟨_, hm⟩, y, by simp [mul_assoc]⟩

/-- A parametrization of the actual vector orbit gives matrix-group transitions
when every matrix fixing the vector belongs to the proposed subgroup. -/
noncomputable def vectorOrbitCover
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hst : cosetVectorStabilizer ≤ max1Subgroup hA hB)
    {ι : Type*} (e : CosetVectorOrbit ≃ ι) :
    Subgroup.GeneratorCosetCover (max1Subgroup hA hB) (sourceGenerators hA hB) ι where
  repr i := orbitRepresentative (e.symm i)
  initial := e (cosetOrbitPoint 1)
  initial_eq := by simp only [Equiv.symm_apply_apply, orbitRepresentative_initial]
  step i a := by
    obtain ⟨h, y, hy⟩ := orbitRepresentative_step hA hB hst (e.symm i)
      (sourceGenerators hA hB a)
    exact ⟨h, e y, by simpa only [Equiv.symm_apply_apply] using hy⟩
  inv_step i a := by
    obtain ⟨h, y, hy⟩ := orbitRepresentative_step hA hB hst (e.symm i)
      (sourceGenerators hA hB a)⁻¹
    exact ⟨h, e y, by simpa only [Equiv.symm_apply_apply] using hy⟩

/-- The certified fixed vector separates the orbit representatives into distinct
right cosets of the subgroup. -/
theorem vectorOrbitCover_separate
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (hst : cosetVectorStabilizer ≤ max1Subgroup hA hB)
    {ι : Type*} (e : CosetVectorOrbit ≃ ι) (i j : ι)
    (hij : (vectorOrbitCover hA hB hst e).repr i *
      ((vectorOrbitCover hA hB hst e).repr j)⁻¹ ∈ max1Subgroup hA hB) : i = j := by
  apply e.symm.injective
  have he := (cosetOrbitMap_eq_iff _ _).mpr (max1Subgroup_le_cosetVectorStabilizer hA hB hij)
  have hp : cosetOrbitPoint (orbitRepresentative (e.symm i)) =
      cosetOrbitPoint (orbitRepresentative (e.symm j)) := Subtype.ext he
  simpa only [orbitRepresentative_point] using hp

/-- The two concrete obligations suffice for the requested 173067389-coset
certificate. Neither premise is asserted by this conditional theorem. -/
theorem max1_cosetCertificate_of_vectorOrbit
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (horbit : Nat.card CosetVectorOrbit = 173067389)
    (hst : cosetVectorStabilizer ≤ max1Subgroup hA hB) :
    ∃ C : Subgroup.GeneratorCosetCover (max1Subgroup hA hB)
      (sourceGenerators hA hB) (Fin 173067389),
      ∀ i j, C.repr i * (C.repr j)⁻¹ ∈ max1Subgroup hA hB → i = j := by
  let e : CosetVectorOrbit ≃ Fin 173067389 :=
    (Nat.equivFinOfCardPos (by rw [horbit]; decide)).trans
      (Equiv.cast (congrArg Fin horbit))
  exact ⟨vectorOrbitCover hA hB hst e,
    vectorOrbitCover_separate hA hB hst e⟩

end Janko4.Cardinality
