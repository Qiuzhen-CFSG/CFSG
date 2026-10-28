module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates.Commutator
public import Theory.Frattini.NormalClosureElementary
public import Theory.Frattini.Intersection

/-!
# Squares in the common central attachment of the paired orbits

An elementary plane normally generates each orbit, so its Frattini subgroup
lies in its commutator with the vertex two-core. The local calculations put
that commutator in the edge layer and make it centralize the residual.
Transport along the retained reversed-orbit conjugation gives the same bound
at the other endpoint. Thus squares in the paired commutator are fixed by
both residuals and have order at most two.

This proves an exponent-four bound, not the exponent-two source target.
In particular no disjointness of the two central attachments is asserted.
The literal selected-orbit consumer is in PairEstimates.Source.
Adapted from SymplecticDistanceTwo/OrbitFrattini.lean; source: MS93 (3.6),
printed p.871, the Frattini calculation below the favorable-pair estimate.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} {geo : Geometry R}

/-- The elementary plane bounds the native orbit's Frattini subgroup without
requiring a natural complement or disjoint moving layers. -/
theorem orbit_frattini_le_commutator (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hl : LocalCalculations R geo) (hb : geo.b R = 2)
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical _ rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b) :
    (frattini (criticalOrbit R c b)).map (criticalOrbit R c b).subtype ≤
      ⁅Q R (alpha R),criticalOrbit R c b⁆ := by
  have hc0 := critical_endpoint_color R (alpha R) rfl _ hc
  have hpos : 0 < criticalDistance R c (geo.exists_critical c hc0) := by
    rw [geo.distance_constant c hc0]
    change 0 < geo.b R
    omega
  let := Z_elementary_of_positive R geo c hc0 hpos
  let : IsElementaryAbelian 2 (criticalPlane R c b) :=
    IsElementaryAbelian.of_le (criticalPlane_le_opposite c b)
  let := IsElementaryAbelian.comap_of_injective (p := 2) (embedM R) (embedM_injective R)
    (criticalPlane R c b)
  have hh := normalClosure_frattini_image_le_commutator
    ((criticalPlane R c b).comap (embedM R)) (pCore 2 M) pCore_isPGroup
    (hl.orbit_core c b hc hab hcb)
  change (frattini ((criticalOrbitNative R c b).map (embedM R))).map
    ((criticalOrbitNative R c b).map (embedM R)).subtype ≤ _
  rw [frattini_image_map _ _ (embedM_injective R),Q_alpha R hp hQR,criticalOrbit,
    ←map_commutator]
  exact map_mono hh

/-- Squares in the original orbit lie in the central edge layer and are
fixed by the component. The possible central attachment is retained. -/
theorem orbit_square_central_edge (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hl : LocalCalculations R geo) (hb : geo.b R = 2)
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical _ rfl))
    (hab : Adjacent R (alpha R) b) (hcb : Adjacent R c b)
    {x : FreeAmalgam R} (hx : x ∈ criticalOrbit R c b) :
    x ^ 2 ∈ Z R b ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) := by
  let A := criticalOrbit R c b
  have hAQ : A ≤ Q R (alpha R) := by
    rw [Q_alpha R hp hQR]
    exact map_mono (hl.orbit_core c b hc hab hcb)
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite A := Finite.of_injective
    (inclusion (hAQ.trans (show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1)))
    (inclusion_injective _)
  let : Fact (IsPGroup 2 A) := ⟨(Q_isPGroup R hp hQR (alpha R) rfl).of_injective
    (inclusion hAQ) (inclusion_injective _)⟩
  have hphi : x ^ 2 ∈ (frattini A).map A.subtype :=
    mem_map_of_mem A.subtype (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨x,hx⟩ : A))
  have hcomm := orbit_frattini_le_commutator hp hQR hl hb hc hab hcb hphi
  refine ⟨hl.commutator_edge c b hc hab hcb hcomm,?_⟩
  apply commutator_eq_bot_iff_le_centralizer.mp _ hcomm
  rw [Q_alpha R hp hQR,criticalOrbit,Ltilde_alpha,←map_commutator,←map_commutator,
    hl.commutator_central c b hc hab hcb,Subgroup.map_bot]

/-- The same central-square bound follows the literal reversed-orbit conjugation. -/
theorem rebased_square_central_edge (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hl : LocalCalculations R geo) (hb : geo.b R = 2)
    {c b : Vertex R} {B : Subgroup (FreeAmalgam R)}
    (hr : RebasedOrbit R geo c b B) {x : FreeAmalgam R} (hx : x ∈ B) :
    x ^ 2 ∈ Z R b ⊓ centralizer (Ltilde R c : Set (FreeAmalgam R)) := by
  obtain ⟨g,d,hga,_,hgb,hd,hdb,rfl⟩ := hr
  obtain ⟨y,hy,rfl⟩ := hx
  let i := (MulAut.conj g⁻¹).toMonoidHom
  have hZ : (Z R (beta R)).map i = Z R b := by rw [←Z_act,hgb]
  have hL : (Ltilde R (alpha R)).map i = Ltilde R c := by rw [←Ltilde_act,hga]
  obtain ⟨hyZ,hyC⟩ := orbit_square_central_edge hp hQR hl hb hd (base_adjacent R) hdb hy
  change (i y) ^ 2 ∈ _
  rw [←map_pow]
  refine ⟨hZ ▸ mem_map_of_mem i hyZ,?_⟩
  intro k hk
  rw [←hL] at hk
  obtain ⟨z,hz,rfl⟩ := hk
  exact (map_mul i z (y^2)).symm.trans ((congrArg i (hyC z hz)).trans (map_mul i (y^2) z))

namespace EarlyPair
variable (o : EarlyPair R geo)

/-- The square of a paired commutator element is trapped in the source's
central attachment, before its vanishing has been established. -/
theorem commutator_square_central_edge (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hl : LocalCalculations R geo)
    {x : FreeAmalgam R} (hx : x ∈ ⁅criticalOrbit R o.c o.b,o.opposite⁆) :
    x ^ 2 ∈ Z R o.b ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) := by
  have hBG : o.opposite ≤ stabilizer R (alpha R) :=
    (o.opposite_le.trans
      (Q_le_adjacent_h R (DistanceTwo.NaturalCore.edge_color o.adjacent_left)
        o.adjacent_right)).trans (fun _ hx => hx.2 _ (adjacent_symm R o.adjacent_left))
  exact orbit_square_central_edge hp hQR hl o.distance_two o.critical o.adjacent_left
    o.adjacent_right (le_normalizer_iff_commutator_le_left.mp
      (hBG.trans (criticalOrbit_normalized o.c o.b)) hx)

/-- The actual paired-commutator squares are fixed by both residuals.
This is a containment, not the unsupported assertion that this intersection vanishes. -/
theorem commutator_square_common_attachment (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hl : LocalCalculations R geo)
    {x : FreeAmalgam R} (hx : x ∈ ⁅criticalOrbit R o.c o.b,o.opposite⁆) :
    x ^ 2 ∈ Z R o.b ⊓ centralizer (Ltilde R (alpha R) : Set (FreeAmalgam R)) ⊓
      centralizer (Ltilde R o.c : Set (FreeAmalgam R)) := by
  refine ⟨o.commutator_square_central_edge hp hQR hl hx,?_⟩
  have hAQ : criticalOrbit R o.c o.b ≤ Q R (alpha R) := by
    rw [Q_alpha R hp hQR]
    exact map_mono o.orbit_le_core
  have hAG := hAQ.trans
    (DistanceTwo.NaturalCore.Q_le_endpoint_stabilizer o.adjacent_left o.adjacent_right)
  have hxB := le_normalizer_iff_commutator_le_right.mp (hAG.trans o.opposite_normalized) hx
  exact (rebased_square_central_edge hp hQR hl o.distance_two o.rebased hxB).2

/-- The proved local identities bound the paired commutator's exponent by four.
The square-one assertion still needs the source's central-attachment calculation. -/
theorem commutator_fourth_power (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hl : LocalCalculations R geo)
    {x : FreeAmalgam R} (hx : x ∈ ⁅criticalOrbit R o.c o.b,o.opposite⁆) : x ^ 4 = 1 := by
  have hxZ := (o.commutator_square_central_edge hp hQR hl hx).1
  have hZplane := edge_Z_le_criticalPlane geo o.critical o.adjacent_left o.adjacent_right
  let := o.plane_elementary
  have h2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (x ^ 2) (hZplane hxZ)
  simpa only [←pow_mul] using h2

end EarlyPair
end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
