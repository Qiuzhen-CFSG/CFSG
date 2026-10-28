module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianReselection.ExceptionalFusion.Coordinates
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianReselection.ExceptionalFusion.MarkedRealization.ModelInput
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianReselection.ExceptionalFusion.MarkedRealization.Ambient
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianReselection.ExceptionalFusion.MarkedRealization.Model
public import Theory.GroupTheory.CyclicByFourOuterInvolutions.CoreUniqueness

/-!
# Identifying the supplied core in marked hyperbolic coordinates

A cyclic inner subgroup of relative index at most four must be the unique
large cyclic subgroup of the inner semidihedral Sylow. The square-one
reflection needed for that calculation is the actual image of the coordinate
swap. Applying the outer-involution dichotomy to the supplied exceptional
element then identifies it with the field actor or its marked scalar multiple,
provided it does not already invert the supplied core.

These arguments construct the exact published `HyperbolicCoordinates` record
for the original supplied `d`. No replacement core or exceptional element is
chosen. The ambient transport retains the whole plane map. The concrete
determinant-corrected projective block construction discharges
`MarkedHyperbolicModelInput`, giving the unconditional realization when
the odd prime is congruent to one modulo four. SQTK and supplement
hypotheses are unnecessary for this intermediate result.

Source: Aschbacher--Smith E.1.14(7), p.214, referring to Aschbacher (1982),
Lemma 4.11; A.3.21(a,b), p.55.
-/

public section
open Matrix Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory
open Matrix.UnitaryQuaternionRotation
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection

variable {G F : Type*} [Group G] [Finite G] [Field F]
variable {L T : Subgroup G} {z : G} {J : HermitianForm 2 F}

/-- The supplied cyclic core is the marked rotation subgroup; its record is
used only for cyclicity, containment and the relative-index bound. -/
theorem core_eq_of_markedCyclicByFour (d : CyclicCoreData L T z)
    (q : MarkedCyclicByFour L T z J) : d.core = zpowers q.coordinates.a := by
  let _ := d.cyclic
  exact q.coordinates.cyclic_inner_eq_rotations q.reflection_sq d.core
    d.core_le_inner d.core_le_sylow d.core_relIndex

/-- A supplied non-inverting exceptional involution belongs to the canonical
field-actor pair, after identifying its original core. -/
theorem exceptional_pair_of_markedCyclicByFour (d : CyclicCoreData L T z)
    (q : MarkedCyclicByFour L T z J)
    (hnon : ¬ (∀ x ∈ d.core, d.exceptional * x * d.exceptional⁻¹ = x⁻¹)) :
    d.exceptional = q.coordinates.c ∨ d.exceptional = z * q.coordinates.c := by
  rcases q.coordinates.outer_dichotomy d.exceptional d.exceptional_mem
    d.exceptional_not_inner d.exceptional_sq with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact (hnon (by simpa only [core_eq_of_markedCyclicByFour d q] using h)).elim

/-- The marked plane realization gives the exact fusion input for an arbitrary
supplied non-inverting core. The concrete plane realization is still explicit. -/
theorem hyperbolicCoordinates_of_markedCyclicByFour (d : CyclicCoreData L T z)
    (q : MarkedCyclicByFour L T z J)
    (hnon : ¬ (∀ x ∈ d.core, d.exceptional * x * d.exceptional⁻¹ = x⁻¹)) :
    Nonempty (HyperbolicCoordinates d J) := by
  refine ⟨{
    form_eq := q.form_eq
    two_ne_zero := q.two_ne_zero
    r := q.r
    r_conj := q.r_conj
    i := q.i
    i_sq := q.i_sq
    i_conj := q.i_conj
    embedding := q.embedding
    marker_eq := q.marker_eq
    core_eq := ?_
    swap_mem := ?_
    actor := q.coordinates.c
    actor_action := q.actor_action
    exceptional_pair := exceptional_pair_of_markedCyclicByFour d q hnon }⟩
  · rw [q.rotation_eq]
    exact core_eq_of_markedCyclicByFour d q
  · rw [q.swap_eq]
    exact q.coordinates.b_mem

/-- For the actual ambient PSU₃ extension, the remaining premise is precisely
the marked concrete-model theorem. The original supplied core is preserved. -/
theorem hyperbolicCoordinates_of_modelInput [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (input : MarkedHyperbolicModelInput p) (hp : p.Prime) (ho : Odd p)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    (T : Sylow 2 G) {z : G} (hz : orderOf z = 2) (hzL : z ∈ generalizedFitting G)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (d : CyclicCoreData (generalizedFitting G) (T : Subgroup G) z)
    (hnon : ¬ (∀ x ∈ d.core, d.exceptional * x * d.exceptional⁻¹ = x⁻¹)) :
    ∃ (K : Type) (_ : Field K) (J₂ : HermitianForm 2 K),
      Nonempty (HyperbolicCoordinates d J₂) := by
  obtain ⟨K, _, _, J₂, ⟨q⟩⟩ := markedCyclicByFour_of_modelInput input hp ho hmodel T
    (fun h => d.exceptional_not_inner (h d.exceptional_mem)) hz hzL
    (d.core_le_sylow d.z_mem) hTz
  exact ⟨K, inferInstance, J₂, hyperbolicCoordinates_of_markedCyclicByFour d q hnon⟩

/-- Every supplied non-inverting cyclic core in the actual odd-prime PSU₃
extension has the full marked hyperbolic realization. All concrete-model
premises are discharged, and the original core and exceptional pair are retained. -/
theorem hyperbolicCoordinates_of_isPSU [IsSimpleGroup (generalizedFitting G)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmod : p % 4 = 1)
    (hmodel : ClassicalGroup.IsPSU (generalizedFitting G) 3 p)
    (T : Sylow 2 G) {z : G} (hz : orderOf z = 2) (hzL : z ∈ generalizedFitting G)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (d : CyclicCoreData (generalizedFitting G) (T : Subgroup G) z)
    (hnon : ¬ (∀ x ∈ d.core, d.exceptional * x * d.exceptional⁻¹ = x⁻¹)) :
    ∃ (K : Type) (_ : Field K) (J₂ : HermitianForm 2 K),
      Nonempty (HyperbolicCoordinates d J₂) :=
  hyperbolicCoordinates_of_modelInput (markedHyperbolicModelInput hp ho hmod)
    hp ho hmodel T hz hzL hTz d hnon

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.AbelianReselection
