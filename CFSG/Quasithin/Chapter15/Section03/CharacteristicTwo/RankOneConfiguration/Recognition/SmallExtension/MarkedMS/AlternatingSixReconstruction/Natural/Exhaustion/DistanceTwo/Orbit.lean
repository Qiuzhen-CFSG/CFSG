module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Frattini
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticDistanceTwo.OrbitFixedKernel
public import Theory.ElementaryAbelian.Join
public import Theory.Representation.BinaryConjugationSection.FullMovement

/-!
# The terminal paired-orbit argument without a natural subgroup

The orbit and fixed kernel are the literal normal closure and fixed-space
preimage in MS93 (3.6). The geometric package records the two actual critical
orbits and their commutators; it contains no whole-core conclusion and no
coordinates on the initial moving subgroup. An elementary paired commutator makes
the fixed kernel elementary once the displacement bound is known. A transitive
action on the fixed quotient then propagates an involution from the critical
plane to every orbit element, contradicting the geometric movement.

The geometric package and the two representation inputs still need independent
source proofs for the original alternating-six replacement. In particular none
of these declarations assert that the package exists.
Source: MS93 (3.6), symplectic paragraph, printed p.871.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
variable {M : Type*} [Group M] [Finite M] (K R : Subgroup M)
  (geo : Geometry R)

/-- The actual paired critical-orbit geometry before representation recognition.
The selected opposite orbit and every kernel use the same two vertices. -/
structure PairedOrbit where
  c : Vertex R
  b : Vertex R
  opposite : Subgroup (FreeAmalgam R)
  distance_two : geo.b R = 2
  critical : CriticalPair R (alpha R) c (geo.exists_critical _ rfl)
  adjacent_left : Adjacent R (alpha R) b
  adjacent_right : Adjacent R c b
  orbit_le_core : criticalOrbitNative R c b ≤ pCore 2 M
  layer_le : orbitLayer R ≤ criticalOrbitNative R c b
  full_movement : criticalOrbitNative R c b = ⁅K, criticalOrbitNative R c b⁆ ⊔ orbitLayer R
  commutator_le_layer : ⁅pCore 2 M, criticalOrbitNative R c b⁆ ≤ orbitLayer R
  opposite_le : opposite ≤ Q R c
  opposite_normalized : stabilizer R c ≤ normalizer (opposite : Set (FreeAmalgam R))
  commutator_elementary :
    IsElementaryAbelian 2 (⁅criticalOrbit R c b, opposite⁆ : Subgroup (FreeAmalgam R))
  opposite_commutator : ⁅Q R c, opposite⁆ ≤ Z R b
  opposite_movement : ⁅opposite, Ltilde R c⁆ = core R c
  strict_index :
    2 * (commutatorPreimage (criticalOrbit R c b) opposite (Z R (alpha R))).relIndex
      (criticalOrbit R c b) ≤ (Q R c).relIndex (criticalOrbit R c b)
  ordered_index : (Q R c).relIndex (criticalOrbit R c b) ≤ (Q R (alpha R)).relIndex opposite
  full_image : criticalOrbit R c b ⊔ Q R c = Q R b
  fixed_central : orbitFixedKernel K R c b ≤ centralizer (criticalOrbitNative R c b : Set M)
  plane_not_fixed : ¬ (criticalPlane R c b).comap (embedM R) ≤ orbitFixedKernel K R c b
  movement : ⁅criticalOrbit R c b, criticalPlane R c b⁆ ≠ ⊥

namespace PairedOrbit
variable {K R geo} (o : PairedOrbit K R geo)

private theorem end_color : color R o.c = false :=
  critical_endpoint_color R (alpha R) rfl _ o.critical

include o in
omit [Finite M] in
private theorem positive (a : Vertex R) (ha : color R a = false) :
    0 < criticalDistance R a (geo.exists_critical a ha) := by
  rw [geo.distance_constant a ha]
  change 0 < geo.b R
  rw [o.distance_two]
  decide

/-- Positivity supplies elementary critical planes on the actual graph. -/
theorem plane_elementary : IsElementaryAbelian 2 (criticalPlane R o.c o.b) := by
  let := Z_elementary_of_positive R geo o.c o.end_color (o.positive o.c o.end_color)
  exact IsElementaryAbelian.of_le ((closure_le _).mpr (fun _ hx => hx.1))

/-- The plane lies in the original vertex carrier, so its pullback loses nothing. -/
theorem plane_le_orbit : criticalPlane R o.c o.b ≤ criticalOrbit R o.c o.b := by
  have hZ : Z R o.c ≤ (embedM R).range := by
    change Z R o.c ≤ Mbar R
    rw [← stabilizer_m_base R]
    apply Z_le_stabilizer_of_dist_le o.c (geo.exists_critical o.c o.end_color)
    change (cosetGraph R).dist o.c (alpha R) ≤ criticalDistance R o.c _
    rw [SimpleGraph.dist_comm, o.critical.1,
      geo.distance_constant _ rfl, geo.distance_constant _ o.end_color]
  have hY : criticalPlane R o.c o.b ≤ (embedM R).range :=
    ((closure_le _).mpr (fun _ hx => hx.1)).trans hZ
  have he : ((criticalPlane R o.c o.b).comap (embedM R)).map (embedM R) =
      criticalPlane R o.c o.b := map_comap_eq_self hY
  rw [← he]
  exact map_mono le_normalClosure

/-- Only the orbit quotient is elementary at this stage. -/
theorem quotient_elementary : IsElementaryAbelian 2 (OrbitQuotient R o.c o.b) := by
  let A := criticalOrbitNative R o.c o.b
  let Y := (criticalPlane R o.c o.b).comap (embedM R)
  let := o.plane_elementary
  let := IsElementaryAbelian.comap_of_injective (p := 2) (embedM R) (embedM_injective R)
    (criticalPlane R o.c o.b)
  have hab : IsMulCommutative (OrbitQuotient R o.c o.b) := by
    apply Normal.quotient_commutative_iff_commutator_le.mpr
    have hh : ⁅A, A⁆ ≤ orbitLayer R :=
      (commutator_mono o.orbit_le_core le_rfl).trans o.commutator_le_layer
    intro a ha
    apply hh
    rw [← map_subtype_commutator]
    exact mem_map_of_mem A.subtype ha
  change IsElementaryAbelian 2 (normalClosure (Y : Set M) ⧸
    (orbitLayer R).subgroupOf (normalClosure (Y : Set M)))
  exact normalClosure_quotient_elementary 2 Y _ hab

/-- Literal conjugation on the orbit quotient is fully moved by its component. -/
theorem quotient_full_movement :
    letI := o.quotient_elementary
    Representation.BinaryOffender.subspaceCommutator (orbitRepresentation R o.c o.b)
      ⊤ (K.subgroupOf ⊤) = ⊤ := by
  let := o.quotient_elementary
  exact (orbitSection R o.c o.b o.layer_le).subspaceCommutator_eq_top_of_movement
    K le_top o.full_movement

/-- The remaining module calculation concerns the canonical fixed quotient
and the literal displacement of its kernel, allowing a central fixed line. -/
def Recognized [K.Normal] : Prop :=
  letI := o.quotient_elementary
  let ρ := orbitFixedQuotientRepresentation K R o.c o.b o.layer_le
  (∀ u v, u ≠ 0 → v ≠ 0 → ∃ m : (⊤ : Subgroup M), ρ m u = v) ∧
    (orbitFixedKernel K R o.c o.b).map (embedM R) ≤
      ⁅criticalOrbit R o.c o.b, o.opposite⁆ ⊔ Z R (alpha R)

/-- Normalization and the elementary paired commutator control the full fixed
kernel through its specified embedding, without splitting a natural module. -/
theorem fixed_elementary (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hD : (orbitFixedKernel K R o.c o.b).map (embedM R) ≤
      ⁅criticalOrbit R o.c o.b, o.opposite⁆ ⊔ Z R (alpha R)) :
    IsElementaryAbelian 2 (orbitFixedKernel K R o.c o.b) := by
  let A := criticalOrbit R o.c o.b
  have hd : (cosetGraph R).dist (alpha R) o.c = 2 :=
    o.critical.1.trans ((geo.distance_constant _ rfl).trans o.distance_two)
  have hAQ : A ≤ Q R (alpha R) := by
    rw [Q_alpha R hp hQR]
    exact map_mono o.orbit_le_core
  have hBA : o.opposite ≤ normalizer (A : Set (FreeAmalgam R)) :=
    (o.opposite_le.trans (Q_le_stabilizer_of_dist_two R o.c (alpha R) o.end_color
      (by rwa [SimpleGraph.dist_comm]))).trans
      (ChapterC.NaturalSixControl.SymplecticSetup.Source.criticalOrbit_normalized o.c o.b)
  have hcomm : ⁅A, o.opposite⁆ ≤ A :=
    le_normalizer_iff_commutator_le_left.mp hBA
  let := o.commutator_elementary
  let := Z_elementary_of_positive R geo (alpha R) rfl (o.positive _ rfl)
  have hZC : Z R (alpha R) ≤ centralizer ((⁅A, o.opposite⁆ : Subgroup (FreeAmalgam R)) : Set _) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R (alpha R) rfl)).trans
      (centralizer_le (hcomm.trans hAQ))
  let : IsElementaryAbelian 2 (⁅A, o.opposite⁆ ⊔ Z R (alpha R) : Subgroup (FreeAmalgam R)) :=
    IsElementaryAbelian.sup_of_le_centralizer hZC
  let : IsElementaryAbelian 2 ((orbitFixedKernel K R o.c o.b).map (embedM R)) :=
    IsElementaryAbelian.of_le hD
  let e := (orbitFixedKernel K R o.c o.b).equivMapOfInjective (embedM R) (embedM_injective R)
  exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective

/-- The source terminal contradiction on the original normal closure and plane. -/
theorem false_of_recognized [K.Normal] (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hr : o.Recognized) : False := by
  let := o.quotient_elementary
  obtain ⟨htrans, hD⟩ := hr
  let s := canonicalOrbitFixedSection K R o.c o.b o.layer_le
  let := o.fixed_elementary hp hQR hD
  let := o.plane_elementary
  have hele : IsElementaryAbelian 2 (criticalOrbitNative R o.c o.b) := by
    apply s.elementary_of_transitive o.fixed_central
    · exact fun y hy => elemPow_eq_one_of_isElementaryAbelian y hy
    · obtain ⟨y, hy, hny⟩ := Set.not_subset.mp o.plane_not_fixed
      have hyA : y ∈ criticalOrbitNative R o.c o.b := le_normalClosure hy
      refine ⟨⟨y, hyA⟩, ?_, ?_⟩
      · apply Subtype.ext
        change y ^ 2 = 1
        apply embedM_injective R
        rw [map_pow, map_one]
        exact elemPow_eq_one_of_isElementaryAbelian (A := criticalPlane R o.c o.b) _ hy
      · exact fun he => hny ((s.coordinates_eq_one_iff _).mp he)
    · exact htrans
  let := hele
  apply o.movement
  apply le_bot_iff.mp
  apply (commutator_mono le_rfl o.plane_le_orbit).trans
  change ⁅(criticalOrbitNative R o.c o.b).map (embedM R),
    (criticalOrbitNative R o.c o.b).map (embedM R)⁆ ≤ ⊥
  rw [← map_commutator, commutator_self_eq_bot_iff.mpr inferInstance, Subgroup.map_bot]

end PairedOrbit
end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
