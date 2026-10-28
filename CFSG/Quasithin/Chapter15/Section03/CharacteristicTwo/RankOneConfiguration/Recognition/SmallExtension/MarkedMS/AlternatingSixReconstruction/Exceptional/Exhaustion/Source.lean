module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.DistanceTwoCubic

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.DistanceTwo

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Graph
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Quotient
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.InitialAction
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Parabolics
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Source

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LocalBounds
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.Critical

/-!
# Exceptional source preparation and faithful distance-two exhaustion

The original pair satisfies every clause of MS93's extension hypothesis (A)
with its central cubic covering kernel retained. The quotient by that kernel
has trivial two-core and acts faithfully on its marked alternating-six
component. Both possible initial-action kernels now give a faithful S₆
permutation embedding of M/E with its original component marking. A single
incident duad--syntheme flag contains the original radical image. The full
weak-BN local data is now constructed, and its lifted ordered residuals
generate precisely the original component. The two local commutator bounds
therefore suffice for exhaustion and feed the unchanged rank-two consumer.
The initial FF classification identifies the graph U with
[X_alpha,Ltilde_alpha], keeping X_alpha distinct from Z_alpha. Thus the
source equality V = U is precisely the entire intrinsic exhaustion target.
The graph Frattini bound
also suffices for the entire exceptional core and the original C.1.32
consumer, through the literal factor embedding.

Critical-endpoint detection now supplies the exact failed comparison in
the non-Frattini branch of (3.6), retaining the cubic kernel. At distance two
the original Q is the source-(3.3) actor. For the faithful initial kernel,
the finite hexacode calculation, actual vertex coordinates and a favorable
critical orientation now prove exhaustion with no extra local premises.
The resulting entire-core facts and rank-two conclusion are applied below.
The cubic initial-kernel and large-distance cases still remain with this
owner; the full alternating-six reconstruction is not yet proved.
Source: MS93 Hypothesis (A), pp.828--829, and (3.6), p.870;
Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion
universe u

/-- All three extension clauses of MS93 (A) for the original pair. No
exhaustion, action-kernel or module-classification premise is used. -/
theorem extension_hypothesis_A
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
    (h : SmallMSPair κ L R) (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    pPrimeCore 2 (extensionKernel h) = ⊥ ∧
      Nat.Coprime 2 (pCore 2 (extensionKernel h)).index ∧
      ∀ F : Subgroup (L ⊔ R : Subgroup G),
        L.subgroupOf (L ⊔ R) ≤ F ⊔ extensionKernel h →
        extensionKernel h ≤ F ⊔ (extensionKernel h).pCoreIn 2 :=
  ⟨extensionKernel_oddCore h, extensionKernel_odd_index h hz,
    extensionKernel_no_supplement h⟩

/-- Source C_alpha stays inside the retained extension kernel under the
actual factor embedding. Its odd quotient is not silently discarded. -/
theorem graph_C_le_extensionKernel
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
    (h : SmallMSPair κ L R) (e : CentralMarking L) :
    C (edge L R) (alpha (edge L R)) ≤
      (extensionKernel h).map (embedM (edge L R)) := by
  intro x hx
  have hxM : x ∈ (embedM (edge L R)).range :=
    by
    change x ∈ Mbar (edge L R)
    rw [← stabilizer_m_base]
    exact hx.1
  obtain ⟨m, rfl⟩ := hxM
  apply mem_map_of_mem
  apply orbit_centralizer_le_extensionKernel h e
  intro z hz
  apply embedM_injective (edge L R)
  simpa only [map_mul] using hx.2 (embedM (edge L R) z)
    (by rw [graph_Z]; exact mem_map_of_mem (embedM (edge L R)) hz)

/-- The literal X-kernel at the base vertex is either Q_alpha or the full
embedded E. This is a dichotomy, not an assumed faithful quotient action. -/
theorem graph_centralOmega_kernel_cases
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    let T := edge L R
    stabilizer T (alpha T) ⊓ centralizer (X T (alpha T) : Set (FreeAmalgam T)) =
      Q T (alpha T) ∨
    stabilizer T (alpha T) ⊓ centralizer (X T (alpha T) : Set (FreeAmalgam T)) =
      (extensionKernel h).map (embedM T) := by
  dsimp only
  have hi : stabilizer (edge L R) (alpha (edge L R)) ⊓
      centralizer (X (edge L R) (alpha (edge L R)) : Set (FreeAmalgam (edge L R))) =
      (centralizer (centralOmega L R : Set (L ⊔ R : Subgroup G))).map (embedM (edge L R)) := by
    ext x
    constructor
    · rintro ⟨hxM, hx⟩
      have hm : x ∈ (embedM (edge L R)).range := by
        change x ∈ Mbar (edge L R)
        rw [← stabilizer_m_base]
        exact hxM
      obtain ⟨m, rfl⟩ := hm
      apply mem_map_of_mem
      intro z hz
      apply embedM_injective (edge L R)
      simpa only [map_mul] using hx (embedM (edge L R) z)
        (by rw [graph_X h]; exact mem_map_of_mem (embedM (edge L R)) hz)
    · rintro ⟨m, hm, rfl⟩
      refine ⟨(stabilizer_m_base (edge L R)).symm ▸ ⟨m, rfl⟩, ?_⟩
      intro x hx
      rw [graph_X h] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      simpa only [map_mul] using congrArg (embedM (edge L R)) (hm z hz)
  rw [hi]
  rcases centralOmega_centralizer_cases h e hz with hc | hc
  · left
    rw [hc]
    exact (Q_alpha _ h.relative_radical.isPGroup h.relative_radical.twoCore_le).symm
  · exact Or.inr (congrArg (Subgroup.map (embedM (edge L R))) hc)

/-- The first branch of source (3.6) already supplies the original C.1.32
exceptional conclusion, without weak-BN or critical-distance inputs. -/
theorem rankTwo_of_graph_frattini
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hc : core (edge L R) (alpha (edge L R)) ≤
      (frattini (Q (edge L R) (alpha (edge L R)))).map
        (Q (edge L R) (alpha (edge L R))).subtype ⊔ X (edge L R) (alpha (edge L R))) :
    RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz (coreExhaustion_of_graph_frattini h hc)

/-- The initial graph subgroup U is the commutator with X, although the
source definitions of Z and X remain distinct. This is the initial-layer
identity in MS93 (3.2), transported through the actual factor embedding. -/
theorem graph_U_eq_X_commutator
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    U (edge L R) (alpha (edge L R)) =
      ⁅X (edge L R) (alpha (edge L R)), Ltilde (edge L R) (alpha (edge L R))⁆ := by
  change ⁅Z (edge L R) (alpha (edge L R)), Ltilde (edge L R) (alpha (edge L R))⁆ = _
  rw [graph_Z, graph_component h, graph_X h, ← map_commutator, ← map_commutator,
    omegaOrbit_moved_eq h e hz]

/-- For the actual exceptional pair, the outstanding source equality V = U
is exactly the intrinsic exhaustion target. All initial-action premises in
this comparison are discharged by the original MS pair. -/
theorem coreExhaustion_iff_graph_core_eq_U
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    CoreExhaustion L R ↔ core (edge L R) (alpha (edge L R)) =
      U (edge L R) (alpha (edge L R)) := by
  constructor
  · intro hx
    rw [graph_U_eq_X_commutator h e hz, graph_core h, graph_X h,
      graph_component h, ← map_commutator]
    exact congrArg (Subgroup.map (embedM (edge L R))) hx
  · exact coreExhaustion_of_graph_core_eq_U h

/-- The source V = U conclusion supplies the unchanged rank-two consumer.
Its non-Frattini critical-distance proof remains with this assembly owner. -/
theorem rankTwo_of_graph_core_eq_U
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hc : core (edge L R) (alpha (edge L R)) = U (edge L R) (alpha (edge L R))) :
    RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz ((coreExhaustion_iff_graph_core_eq_U h e hz).mpr hc)


/-- The actual component has precisely the alternating image under the
source permutation embedding, on the original quotient by E. -/
theorem source_permutation_component_image
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    ((L.subgroupOf (L ⊔ R)).map (QuotientGroup.mk' (extensionKernel h))).map
        (extensionPermutationAction h e hz) = alternatingGroup (Fin 6) := by
  let K := L.subgroupOf (L ⊔ R)
  let π := QuotientGroup.mk' (extensionKernel h)
  ext x
  constructor
  · rintro ⟨y, ⟨k, hk, rfl⟩, rfl⟩
    rw [extensionPermutationAction_component h e hz (⟨k, hk⟩ : K)]
    exact (extensionKernel_component_equiv h e (π.subgroupMap K ⟨k, hk⟩)).property
  · intro hx
    obtain ⟨k, hk⟩ := (extensionKernel_component_equiv h e).surjective ⟨x, hx⟩
    obtain ⟨j, rfl⟩ := π.subgroupMap_surjective K k
    refine ⟨π j, mem_map_of_mem π j.property, ?_⟩
    rw [extensionPermutationAction_component]
    exact congrArg Subtype.val hk

open Theory.SpecificGroups.SymmetricSix in
/-- The original exceptional pair supplies the faithful quotient coordinates
and incident flag required for the weak-BN construction. This discharges the
parabolic-type and radical-placement premises; local rank-one data and the
critical-distance exhaustion are still owned by this task. -/
theorem source_permutation_flag
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3) :
    ∃ g : Equiv.Perm (Fin 6),
      Function.Injective (extensionPermutationAction h e hz) ∧
      ((L.subgroupOf (L ⊔ R)).map (QuotientGroup.mk' (extensionKernel h))).map
        (extensionPermutationAction h e hz) = alternatingGroup (Fin 6) ∧
      ((R.subgroupOf (L ⊔ R)).map (QuotientGroup.mk' (extensionKernel h))).map
        (extensionPermutationAction h e hz) ≤ borel.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := extensionPermutationAction_radical_flag h e hz
  exact ⟨g, extensionPermutationAction_injective h e hz,
    source_permutation_component_image h e hz, hg⟩

/-- One actual critical-endpoint bound gives the complete exceptional
C.1.32 conclusion through the already-proved recognition. Its local estimate
is still explicit and must be discharged by this reconstruction owner. -/
theorem rankTwo_of_critical_commutator_le
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (c : Vertex (edge L R))
    (hc : CriticalPair (edge L R) (alpha (edge L R)) c
      ((sourceGeometry h).exists_critical (alpha (edge L R)) rfl))
    (hcomm : ⁅Q (edge L R) (alpha (edge L R)), Z (edge L R) c⁆ ≤
      (frattini (Q (edge L R) (alpha (edge L R)))).map
        (Q (edge L R) (alpha (edge L R))).subtype ⊔ X (edge L R) (alpha (edge L R))) :
    RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz (coreExhaustion_of_critical_commutator_le h e hz c hc hcomm)

/-- The actual distance-two source-(3.3) bound supplies the original rank-two
consumer, including every exceptional block clause. Final unconditional
assembly retains the finite-action proof of this bound with this task. -/
theorem rankTwo_of_source33_bound
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hb : sourceDistance h = 2) (c : Vertex (edge L R))
    (hc : CriticalPair (edge L R) (alpha (edge L R)) c
      ((sourceGeometry h).exists_critical (alpha (edge L R)) rfl))
    (hcomm : ⁅Z (edge L R) c,Q (edge L R) (alpha (edge L R))⁆ ≤
      ⁅X (edge L R) (alpha (edge L R)),X (edge L R) c⁆ ⊔
        ⁅X (edge L R) (alpha (edge L R)) ⊓ Q (edge L R) c,
          Q (edge L R) (alpha (edge L R))⁆) : RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz (coreExhaustion_of_source33_bound h e hz hb c hc hcomm)

open ChapterC in
/-- All exceptional core clauses in the faithful distance-two branch. The
literal entire blockU, including its order and full centralizer, is retained. -/
theorem core_facts_of_distanceTwo_faithful
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hfaith : layerKernel L R = pCore 2 (L ⊔ R : Subgroup G))
    (hb : sourceDistance h = 2) :
    IsElementaryAbelian 2 (blockU L) ∧
      blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      BlockModuleIrreducible L ∧ Nat.card (blockU L) = 2 ^ 6 ∧
      centralizer (blockU L : Set L) = pCore 2 L :=
  core_facts_of_exhaustion h e hz (coreExhaustion_of_distanceTwo_faithful h e hz hfaith hb)

/-- The original C.1.32 consumer for the completed faithful distance-two
branch. No module, offender, or commutator-bound premise remains. -/
theorem rankTwo_of_distanceTwo_faithful
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hfaith : layerKernel L R = pCore 2 (L ⊔ R : Subgroup G))
    (hb : sourceDistance h = 2) : RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz (coreExhaustion_of_distanceTwo_faithful h e hz hfaith hb)

open ChapterC in
/-- Every exceptional whole-core clause in the distance-two cubic case
with derived natural actor. The proof also shows this subcase impossible. -/
theorem core_facts_of_distanceTwo_cubic_even
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hk : layerKernel L R = extensionKernel h)
    (hb : sourceDistance h = 2)
    (himage : (CubicAction.projection h e hz hk).range = alternatingGroup (Fin 6)) :
    IsElementaryAbelian 2 (blockU L) ∧
      blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      BlockModuleIrreducible L ∧ Nat.card (blockU L) = 2 ^ 6 ∧
      centralizer (blockU L : Set L) = pCore 2 L :=
  core_facts_of_exhaustion h e hz
    (CubicAction.coreExhaustion_of_distanceTwo_even h e hz hk hb himage)

/-- Apply the completed cubic derived-image subcase to the original C.1.32
consumer, with the original entire blockU and quotient conventions. -/
theorem rankTwo_of_distanceTwo_cubic_even
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hk : layerKernel L R = extensionKernel h)
    (hb : sourceDistance h = 2)
    (himage : (CubicAction.projection h e hz hk).range = alternatingGroup (Fin 6)) :
    RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz
    (CubicAction.coreExhaustion_of_distanceTwo_even h e hz hk hb himage)

open ChapterC CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph in
/-- The rank-three critical-image branch supplies every clause for the
original entire exceptional core. -/
theorem core_facts_of_distanceTwo_cubic_rankThree
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hk : layerKernel L R = extensionKernel h)
    (hb : sourceDistance h = 2) (c : Vertex (edge L R))
    (hc : CriticalPair (edge L R) (alpha (edge L R)) c
      ((sourceGeometry h).exists_critical (alpha (edge L R)) rfl))
    (hi : Representation.BinaryOffender.rank
      (CubicAction.graphImage h e hz hk (X (edge L R) c)) = 3) :
    IsElementaryAbelian 2 (blockU L) ∧
      blockU L ≤ centralizer (pCore 2 L : Set L) ∧
      BlockModuleIrreducible L ∧ Nat.card (blockU L) = 2 ^ 6 ∧
      centralizer (blockU L : Set L) = pCore 2 L :=
  core_facts_of_exhaustion h e hz
    (CubicAction.coreExhaustion_of_distanceTwo_rankThree h e hz hk hb c hc hi)

open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph in
/-- Apply the rank-three critical-image branch to the actual C.1.32 consumer. -/
theorem rankTwo_of_distanceTwo_cubic_rankThree
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hk : layerKernel L R = extensionKernel h)
    (hb : sourceDistance h = 2) (c : Vertex (edge L R))
    (hc : CriticalPair (edge L R) (alpha (edge L R)) c
      ((sourceGeometry h).exists_critical (alpha (edge L R)) rfl))
    (hi : Representation.BinaryOffender.rank
      (CubicAction.graphImage h e hz hk (X (edge L R) c)) = 3) :
    RankTwoAlternatives L R :=
  rankTwo_of_exhaustion h e hz
    (CubicAction.coreExhaustion_of_distanceTwo_rankThree h e hz hk hb c hc hi)

end AlternatingSixReconstruction.Exceptional.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
