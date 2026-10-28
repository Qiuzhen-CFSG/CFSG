module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Assembly.Noncentral.Source
public import Theory.Frattini.NormalClosureElementary
public import Theory.Frattini.Intersection

/-!
# Preliminary critical orbits before full edge-image identification

The favorable pair retains its literal orbit and common edge. Normal closure
and the source commutator identities control its squares and the opposite
vertex-core image without identifying that image with the whole radical.
Both central covers of orders sixteen and thirty-two are retained.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871.
Final distance-two exhaustion still requires the critical-plane calculations.
-/

@[expose] public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane.Exponent
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} {geo : Geometry R}

theorem orbit_frattini_le_commutator (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hb : geo.b R = 2)
    {c b : Vertex R}
    (hc : CriticalPair R (alpha R) c (geo.exists_critical _ rfl))
    (hA : criticalOrbitNative R c b ≤ pCore 2 M) :
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
    hA
  change (frattini ((criticalOrbitNative R c b).map (embedM R))).map
    ((criticalOrbitNative R c b).map (embedM R)).subtype ≤ _
  rw [frattini_image_map _ _ (embedM_injective R),Q_alpha R hp hQR,criticalOrbit,
    ←map_commutator]
  exact map_mono hh

universe u
variable {G : Type u} [Group G] [Finite G] {L T : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L T) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L T)

include h e hz hn in
theorem orbit_square_central_edge (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c b : Vertex d.radical}
    (hc : CriticalPair d.radical (alpha d.radical) c ((replacementGeometry h d).exists_critical _ rfl))
    (hab : Adjacent d.radical (alpha d.radical) b) (hcb : Adjacent d.radical c b)
    {x : FreeAmalgam d.radical} (hx : x ∈ criticalOrbit d.radical c b) :
    x ^ 2 ∈ Z d.radical b ⊓ centralizer (Ltilde d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) := by
  have hp := replacement_radical_isPGroup h d
  have hQR := replacement_core_le_radical h d
  let A := criticalOrbit d.radical c b
  have hAQ : A ≤ Q d.radical (alpha d.radical) := by
    rw [Q_alpha d.radical hp hQR]
    exact map_mono (replacement_orbit_le_core h e hz d hb hlarge hc hab hcb)
  let : Finite (stabilizer d.radical (alpha d.radical)) := finite_stabilizer d.radical (alpha d.radical)
  let : Finite A := Finite.of_injective
    (inclusion (hAQ.trans (show Q d.radical (alpha d.radical) ≤ stabilizer d.radical (alpha d.radical) from fun _ hx => hx.1)))
    (inclusion_injective _)
  let : Fact (IsPGroup 2 A) := ⟨(Q_isPGroup d.radical hp hQR (alpha d.radical) rfl).of_injective
    (inclusion hAQ) (inclusion_injective _)⟩
  have hphi : x ^ 2 ∈ (frattini A).map A.subtype :=
    mem_map_of_mem A.subtype (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨x,hx⟩ : A))
  have hcomm := orbit_frattini_le_commutator hp hQR hb hc
    (replacement_orbit_le_core h e hz d hb hlarge hc hab hcb) hphi
  refine ⟨orbit_commutator_le_edge_of_transposition h e hz hn d hb hlarge hc hab hcb hcomm,?_⟩
  apply commutator_eq_bot_iff_le_centralizer.mp _ hcomm
  rw [Q_alpha d.radical hp hQR,criticalOrbit,Ltilde_alpha,←map_commutator,←map_commutator,
    orbit_commutator_centralizes_residual_of_transposition h e hz hn d hb hlarge hc hab hcb,Subgroup.map_bot]

include h e hz hn in
theorem rebased_square_central_edge (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    {c b : Vertex d.radical} {B : Subgroup (FreeAmalgam d.radical)}
    (hr : RebasedOrbit d.radical (replacementGeometry h d) c b B) {x : FreeAmalgam d.radical} (hx : x ∈ B) :
    x ^ 2 ∈ Z d.radical b ⊓ centralizer (Ltilde d.radical c : Set (FreeAmalgam d.radical)) := by
  obtain ⟨g,c0,hga,_,hgb,hd,hdb,rfl⟩ := hr
  obtain ⟨y,hy,rfl⟩ := hx
  let i := (MulAut.conj g⁻¹).toMonoidHom
  have hZ : (Z d.radical (beta d.radical)).map i = Z d.radical b := by rw [←Z_act,hgb]
  have hL : (Ltilde d.radical (alpha d.radical)).map i = Ltilde d.radical c := by rw [←Ltilde_act,hga]
  obtain ⟨hyZ,hyC⟩ := orbit_square_central_edge h e hz hn d hb hlarge hd (base_adjacent d.radical) hdb hy
  change (i y) ^ 2 ∈ _
  rw [←map_pow]
  refine ⟨hZ ▸ mem_map_of_mem i hyZ,?_⟩
  intro k hk
  rw [←hL] at hk
  obtain ⟨z,hz,rfl⟩ := hk
  exact (map_mul i z (y^2)).symm.trans ((congrArg i (hyC z hz)).trans (map_mul i (y^2) z))

include h e hz hn in
theorem paired_square_eq_one
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    (o : PreliminaryPair d.radical (replacementGeometry h d))
    {x : FreeAmalgam d.radical}
    (hx : x ∈ ⁅criticalOrbit d.radical o.c o.b,o.opposite⁆) : x ^ 2 = 1 := by
  have hp := replacement_radical_isPGroup h d
  have hQR := replacement_core_le_radical h d
  let A := criticalOrbit d.radical o.c o.b
  have hAQ : A ≤ Q d.radical (alpha d.radical) := by
    rw [Q_alpha d.radical hp hQR]
    exact map_mono o.orbit_le_core
  have hAG := hAQ.trans (DistanceTwo.NaturalCore.Q_le_endpoint_stabilizer
    o.adjacent_left o.adjacent_right)
  have hBG : o.opposite ≤ stabilizer d.radical (alpha d.radical) :=
    (o.opposite_le.trans (Q_le_adjacent_h d.radical
      (DistanceTwo.NaturalCore.edge_color o.adjacent_left) o.adjacent_right)).trans
      (fun _ hy => hy.2 _ (adjacent_symm d.radical o.adjacent_left))
  have hxA := le_normalizer_iff_commutator_le_left.mp
    (hBG.trans (criticalOrbit_normalized o.c o.b)) hx
  have hxB := le_normalizer_iff_commutator_le_right.mp (hAG.trans o.opposite_normalized) hx
  let : Finite (stabilizer d.radical (alpha d.radical)) := finite_stabilizer _ _
  let : Finite A := Finite.of_injective
    (inclusion (hAQ.trans (show Q d.radical (alpha d.radical) ≤ stabilizer d.radical (alpha d.radical)
      from fun _ hy => hy.1))) (inclusion_injective _)
  let : Fact (IsPGroup 2 A) := ⟨(Q_isPGroup d.radical hp hQR (alpha d.radical) rfl).of_injective
    (inclusion hAQ) (inclusion_injective _)⟩
  have hphi : x ^ 2 ∈ (frattini A).map A.subtype :=
    mem_map_of_mem A.subtype (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨x,hxA⟩ : A))
  have hcomm := orbit_frattini_le_commutator hp hQR hb o.critical o.orbit_le_core hphi
  rw [orbit_commutator_eq_plane_of_transposition h e hz hn d hb hlarge o.critical o.adjacent_left o.adjacent_right] at hcomm
  have hfixed := (rebased_square_central_edge h e hz hn d hb hlarge o.rebased hxB).2
  exact mem_bot.mp ((PairEstimates.plane_commutator_inf_opposite_fixed_eq_bot h e hz hn d hb hlarge
    o.critical o.adjacent_left o.adjacent_right) ▸ ⟨hcomm,hfixed⟩)


include h e hz hn in
 theorem paired_commutator_elementary
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical))
    (o : PreliminaryPair d.radical (replacementGeometry h d)) :
    IsElementaryAbelian 2 (⁅criticalOrbit d.radical o.c o.b,o.opposite⁆ :
      Subgroup (FreeAmalgam d.radical)) := by
  let D := (⁅criticalOrbit d.radical o.c o.b,o.opposite⁆ : Subgroup (FreeAmalgam d.radical))
  have hs (x : D) : x ^ 2 = 1 := by
    apply Subtype.ext
    exact paired_square_eq_one h e hz hn d hb hlarge o x.property
  exact {
    toIsMulCommutative := ⟨⟨fun a b =>
      Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (hs x)) a b⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane.Exponent
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
