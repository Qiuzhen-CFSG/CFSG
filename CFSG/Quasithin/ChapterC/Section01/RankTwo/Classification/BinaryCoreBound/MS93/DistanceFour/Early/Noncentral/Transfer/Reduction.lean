module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Prerequisites
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Noncentral.Reduction
public import Theory.GroupTheory.CommutatorPreimage

/-!
# From critical edge centrality to the moving-kernel bound

Under the contrary hypothesis in the second MS93 (4.6.6), conjugacy makes
all radius-derived subgroups central in their own vertex stabilizers.
A radius generator Z_d outside B_c forces V_c to escape Q_d: otherwise
Z_d would be central in V_c and (4.6.1) would put it in B_c. An escaping
M-colored generator of V_c then completes a critical path with midpoint c.

For the final transfer, let P be the subgroup of G_c whose commutator with
Q_c centralizes G_c. If the generators outside B_c lie in P, then every
radius generator commutes with Ltilde_c modulo P: those in B_c do so
modulo Z_c, and those in P do so by relative normality of P. Consequently
Vcirc_c lies in P and its kernel commutator lies in the literal fixedCore.

The missing critical edge-plane comparison on pp.903--904 is not asserted
here. Transfer.lean applies this reduction to that explicit premise.
Source: Meierfrankenfeld--Stellmacher (1993), second (4.6.6), pp.903--904.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
open Initial
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- Centrality of the radius-derived subgroup transports between M-vertices. -/
theorem derived_central_at_all (a : Vertex R) (ha : color R a = false)
    (hcentral : ⁅V R a, V R a⁆ ≤
      (center (stabilizer R a)).map (stabilizer R a).subtype)
    (c : Vertex R) (hc : color R c = false) :
    ⁅V R c, V R c⁆ ≤ (center (stabilizer R c)).map (stabilizer R c).subtype := by
  obtain ⟨u, hu⟩ := exists_mVertex_of_color R ha
  obtain ⟨v, hv⟩ := exists_mVertex_of_color R hc
  let g := u⁻¹ * v
  have hg : act R g a = c := by
    rw [hu, act_mVertex]
    simpa only [g, mul_inv_cancel_left] using hv.symm
  rw [← hg, V_act, stabilizer_act,
    ← map_embeddedCenter _ _ (MulAut.conj g⁻¹).injective, ← map_commutator]
  exact map_mono hcentral

/-- Every radius generator outside B completes to a genuine critical pair,
with the original vertex as midpoint. Only (4.6.1) is needed from InitialFacts. -/
theorem critical_through_nonfixed_generator
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (initial : InitialFacts R geometry)
    (c d : Vertex R) (hc : color R c = false) (hd : color R d = false)
    (hnu : nu R geometry c d) :
    ∃ e, CriticalPair R d e (geometry.exists_critical d hd) ∧
      (cosetGraph R).dist c e = 2 := by
  have hout : ¬ V R c ≤ Q R d := by
    intro hV
    apply hnu.2
    apply le_trans _ (initial.center_le_B c hc)
    have hdV : Z R d ≤ V R c := le_iSup_of_le d (le_iSup_of_le hnu.1.le le_rfl)
    intro x hx
    refine ⟨⟨x, hdV hx⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext ((commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes d hd)) hx y (hV y.property))
  obtain ⟨e, he, hec, hescape⟩ : ∃ e, color R e = false ∧
      (cosetGraph R).dist e c ≤ 2 ∧ ¬ Z R e ≤ Q R d := by
    by_contra! h
    exact hout (radius_le_of_generators c hc (Q R d) h)
  have hlow := criticalDistance_le R e (geometry.exists_critical e he) hescape
  rw [geometry.distance_constant e he] at hlow
  change geometry.b R ≤ (cosetGraph R).dist e d at hlow
  have htri := (cosetGraph_connected R).dist_triangle (u := e) (v := c) (w := d)
  have hcd : (cosetGraph R).dist c d = 2 := by rw [SimpleGraph.dist_comm, hnu.1]
  rw [hcd] at htri
  have hed : (cosetGraph R).dist e d = 4 := by omega
  have hec' : (cosetGraph R).dist e c = 2 := by omega
  have hecrit : CriticalPair R e d (geometry.exists_critical e he) := by
    refine ⟨?_, hescape⟩
    rw [hed, geometry.distance_constant e he]
    exact hb.symm
  exact ⟨e, common.critical_reverse e he d hd hecrit, by rwa [SimpleGraph.dist_comm]⟩

/-- Bounds on the nonfixed generators give the actual moving-kernel bound.
The generators inside B are handled using the definition of B, without
assuming that B equals the radius center. -/
theorem moving_kernel_fixed_of_nonfixed_generator_bounds
    (common : CommonFacts R source geometry)
    (a : Vertex R) (ha : color R a = false)
    (hgen : ∀ d, nu R geometry a d →
      ⁅Z R d, Q R a⁆ ≤ centralizer (stabilizer R a : Set (FreeAmalgam R))) :
    ⁅Vcirc R a, Q R a⁆ ≤ fixedCore R a := by
  let G := stabilizer R a
  let C := centralizer (G : Set (FreeAmalgam R))
  let P := commutatorPreimage G (Q R a) C
  have hGC : G ≤ normalizer C :=
    (le_centralizer_iff.mpr le_rfl).trans (Subgroup.centralizer_le_normalizer _)
  have hGP : G ≤ normalizer P :=
    commutatorPreimage_normalized G (Q R a) C G hGC G.le_normalizer
      (Q_normalized R a) hGC
  have hL : Ltilde R a ≤ G := map_subtype_le _
  have hV : V R a ≤ G := (radius_le_Q common a ha).trans (fun _ hx => hx.1)
  have hZP : Z R a ≤ P := le_commutatorPreimage (Z_le_stabilizer R a)
    ((geometry.centralizes a ha).le.trans bot_le)
  have hBP : ⁅B R a (geometry.Z_normal a), Ltilde R a⁆ ≤ P := by
    apply le_trans _ hZP
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl x hx
    exact ((mem_B_iff R a (geometry.Z_normal a) hV x).mp hx).2 l hl
  have hVP : V R a ≤ commutatorPreimage G (Ltilde R a) P := by
    apply radius_le_of_generators a ha
    intro d hd hda
    have hdV : Z R d ≤ V R a := le_iSup_of_le d (le_iSup_of_le hda le_rfl)
    apply le_commutatorPreimage (hdV.trans hV)
    by_cases hB : Z R d ≤ B R a (geometry.Z_normal a)
    · exact (commutator_mono hB le_rfl).trans hBP
    · have htwo : (cosetGraph R).dist d a = 2 := by
        have heven : Even ((cosetGraph R).dist d a) := by
          obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist d a
          rw [← hp, walk_even_iff_color_eq, hd, ha]
        have hzero : (cosetGraph R).dist d a ≠ 0 := by
          intro h
          have heq := (cosetGraph_connected R).dist_eq_zero_iff.mp h
          subst d
          exact hB (Z_le_B common a ha)
        obtain ⟨n, hn⟩ := heven
        omega
      have hdP : Z R d ≤ P := le_commutatorPreimage (hdV.trans hV) (hgen d ⟨htwo, hB⟩)
      exact (commutator_mono hdP le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp (hL.trans hGP))
  have hmove : Vcirc R a ≤ P :=
    (commutator_mono hVP le_rfl).trans
      (commutator_commutatorPreimage_le G (Ltilde R a) P hGP)
  have hfixed := (commutator_mono hmove le_rfl).trans
    (commutator_commutatorPreimage_le G (Q R a) C hGC)
  apply le_inf
  · exact (commutator_mono ((DistanceEight.Vcirc_le_V R a).trans
      (radius_le_Q common a ha)) le_rfl).trans (commutator_le_self _)
  · exact hfixed.trans (centralizer_le hL)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early
