module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans.Centrality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans.Offender
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.Basic

/-!
# Centrality and abelianness of the escaping-neighbor span

The seed centrality theorem propagates to the actual stabilizer-conjugate
span. Its commutator with the kernel is precisely the original order-two
seed. Consequently the derived subgroup is central in the local stabilizer.

For an actual offender for the radius quotient V_alpha/Z_alpha,
InitialFacts places V_alpha' in U_alpha. The span's derived subgroup then
lies in the fixed part of U_alpha, which is trivial by the marked direct-sum
decomposition. The `Offender` prerequisite discharges this interface in the
nonabelian-span case: it constructs the actual paired central-quotient
actions and rules out a faithful self-dual binary SL₃(2) FF-module. Thus the
bad-neighbor hypotheses imply abelianness with no extra offender or
module-classification premise. The terminal edge-containment contradiction
belongs to the parent development.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.4), first paragraph,
printed p.902. The quotient fixed subgroup is the literal radiusFixed.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry)

private theorem mapped_center_le_centralizer {G : Type*} [Group G] (H : Subgroup G) :
    (center H).map H.subtype ≤ centralizer (H : Set G) := by
  rintro x ⟨z,hz,rfl⟩ y hy
  exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y,hy⟩)

include common

/-- Conjugate generation preserves the central order-two displacement. -/
theorem escaping_neighborSpan_commutator (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    ⁅neighborSpan a d, Q R a⁆ = ⁅Z R d, Q R a⁆ := by
  have hd := (escaping_neighbor_geometry common initial a b d ha hab hdb hbad).2.1
  exact neighborSpan_commutator_eq_of_central common a d ha hd.le
    ((escaping_neighbor_commutator_le_local_center common initial hb a b d ha hab hdb hbad).trans
      (mapped_center_le_centralizer _))

/-- The whole span has central kernel displacement in G_alpha. -/
theorem escaping_neighborSpan_commutator_le_local_center (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    ⁅neighborSpan a d, Q R a⁆ ≤ (center (stabilizer R a)).map (stabilizer R a).subtype := by
  rw [escaping_neighborSpan_commutator common initial hb a b d ha hab hdb hbad]
  exact escaping_neighbor_commutator_le_local_center common initial hb a b d ha hab hdb hbad

/-- The natural moving layer has no local fixed elements, so a central
span-derived subgroup contained there must vanish. -/
theorem neighborSpan_commutative_of_radius_derived_le (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a))
    (hderived : ⁅V R a, V R a⁆ ≤ U R a) : IsMulCommutative (neighborSpan a d) := by
  have hd := (escaping_neighbor_geometry common initial a b d ha hab hdb hbad).2.1
  have hWV := neighborSpan_le_radius a d hd.le
  have hWU := (commutator_mono hWV hWV).trans hderived
  have hWC := (commutator_mono le_rfl (hWV.trans (radius_le_Q common a ha))).trans
    ((escaping_neighborSpan_commutator_le_local_center common initial hb a b d ha hab hdb hbad).trans
      ((mapped_center_le_centralizer _).trans (centralizer_le (Ltilde_le_stabilizer a))))
  apply commutator_self_eq_bot_iff.mp
  exact le_bot_iff.mp ((le_inf hWU hWC).trans (Flags.U_fixed_eq_bot common a ha).le)

/-- The last abelianness implication in (4.6.4), with every offender premise
on the actual radius quotient explicit. The offender need not use the
original edge. -/
theorem neighborSpan_commutative_of_radius_offender (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a))
    (t : Vertex R) (hat : Adjacent R a t) (A : Subgroup (FreeAmalgam R))
    (hAt : A ≤ Q R t) (hAa : ¬ A ≤ Q R a)
    (hPhi : (frattini A).map A.subtype ≤ Q R a)
    (hindex : (radiusFixed geometry a A).relIndex (V R a) ≤ (Q R a).relIndex A) :
    IsMulCommutative (neighborSpan a d) :=
  neighborSpan_commutative_of_radius_derived_le common initial hb a b d ha hab hdb hbad
    (initial.offender_derived_le a t ha hat A hAt hAa hPhi hindex)

/-- The escaping neighbor's actual stabilizer-conjugate span is abelian.
All offender premises are discharged from the bad-neighbor hypotheses. -/
theorem escaping_neighborSpan_commutative (initial : InitialFacts R geometry)
    (hb : geometry.b R = 4) (a b d : Vertex R) (ha : color R a = false)
    (hab : Adjacent R a b) (hdb : Adjacent R d b)
    (hbad : ¬ ⁅Z R d, Q R b⁆ ≤ B R a (geometry.Z_normal a)) :
    IsMulCommutative (neighborSpan a d) := by
  by_contra hnon
  obtain ⟨t, A, hat, hAt, hAa, hPhi, hindex⟩ :=
    exists_radius_offender_of_noncommutative_neighborSpan
      common initial hb a b d ha hab hdb hbad hnon
  exact hnon (neighborSpan_commutative_of_radius_offender
    common initial hb a b d ha hab hdb hbad t hat A hAt hAa hPhi hindex)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment
