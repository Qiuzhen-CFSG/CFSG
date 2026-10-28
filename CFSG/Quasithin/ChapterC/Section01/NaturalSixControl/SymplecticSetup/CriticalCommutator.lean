module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Seed
public import Theory.GroupTheory.Commutator.NormalClosureSupplement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.CriticalPairs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.SectionFive.RadiusCentrality
/-!
# The moving image of the actual critical commutator

The local Z-layer is the normal closure of the radical omega-center. Since
that seed is centralized by the radical, the component and full stabilizer
have the same commutator on Z. Thus the genuine critical Z commutator lies
in both moving layers. The radius intersection in the penultimate M-kernel
centralizes this commutator and normalizes the opposite Z-layer.

The final theorem applies these inputs to the original characteristic
replacement and its literal critical path. These are the group-theoretic
inputs to the point-core calculation in MS93 (3.3)/(5.2); the final marked
image containment is separate.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3), printed pp.866--867,
and (5.0)--(5.2), printed pp.912--914.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s
theorem Z_full_commutator_alpha : ⁅Z R (alpha R),stabilizer R (alpha R)⁆ = U R (alpha R) := by
  have hcentral : omegaCenter R ≤ centralizer (R : Set M) :=
    fun _ hx => (mem_omegaCenter_iff.mp hx).2.2
  have he := normalClosure_commutator_eq_of_centralizing_supplement
    (omegaCenter R) L R s.sup_eq_top hcentral
  have hfull : ⁅normalClosure (omegaCenter R : Set M),(⊤ : Subgroup M)⁆ =
      ⁅normalClosure (omegaCenter R : Set M),L⁆ := by
    apply le_antisymm _ (commutator_mono le_rfl le_top)
    rw [he]
    exact commutator_mono le_normalClosure le_rfl
  rw [U,SymplecticSeed.Z_eq_seedHull,Ltilde_alpha,s.residual]
  have htop : stabilizer R (alpha R) = (⊤ : Subgroup M).map (embedM R) := by
    rw [←MonoidHom.range_eq_map]
    exact stabilizer_m_base R
  rw [htop,←map_commutator,←map_commutator,hfull]

/-- The full local stabilizer moves the same subgroup of Z as the residual. -/
theorem Z_full_commutator (a : Vertex R) (ha : color R a = false) :
    ⁅Z R a,stabilizer R a⁆ = U R a := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  have hh := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom)
    s.Z_full_commutator_alpha
  rw [map_commutator,← Z_act,← stabilizer_act,← U_act] at hh
  simpa only [alpha,act_mVertex,one_mul] using hh

open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

/-- The genuine critical Z commutator lies in both moving layers. -/
theorem critical_Z_commutator_le_moving {a a' : Vertex R}
    (p : CriticalPath R s.geometry a a') :
    ⁅Z R a,Z R a'⁆ ≤ U R a ⊓ U R a' := by
  have hza : Z R a ≤ stabilizer R a' :=
    Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hza' : Z R a' ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le a' (s.geometry.exists_critical a' p.end_color)
    rw [SimpleGraph.dist_comm,p.critical.1,s.geometry.distance_constant a p.start_color,
      s.geometry.distance_constant a' p.end_color]
  apply le_inf
  · rw [←s.Z_full_commutator a p.start_color]
    exact commutator_mono le_rfl hza'
  · rw [commutator_comm,←s.Z_full_commutator a' p.end_color]
    exact commutator_mono le_rfl hza

/-- Radius elements in the penultimate M-kernel centralize the critical
Z commutator; this is the actual centralizer input for source (3.3). -/
theorem critical_radius_intersection_centralizes
    (hb : 2 < s.geometry.b R) {a a' : Vertex R}
    (p : CriticalPath R s.geometry a a') :
    V R a ⊓ Q R (p.walk.getVert (p.walk.length-2)) ≤
      centralizer ((⁅Z R a,Z R a'⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  have hR : ⁅Z R a,Z R a'⁆ ≤ Z R a :=
    (s.critical_Z_commutator_le_moving p).trans inf_le_left |>.trans
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.U_le_Z R a)
  have hQ : Q R a ≤ centralizer (Z R a : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q R a p.start_color))
  exact ((inf_le_left.trans (V_le_Q R p.start_color hb)).trans hQ).trans
    (centralizer_le hR)

/-- The same radius intersection acts on the literal endpoint Z-layer. -/
theorem critical_radius_intersection_normalizes_endpoint
    (hb : s.geometry.b R = 4) {a a' : Vertex R}
    (p : CriticalPath R s.geometry a a') :
    V R a ⊓ Q R (p.walk.getVert (p.walk.length-2)) ≤
      normalizer (Z R a' : Set (FreeAmalgam R)) := by
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have he : color R (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    rw [hl]
    decide
  have hd : (cosetGraph R).dist (p.walk.getVert (p.walk.length-2)) a' = 2 := by
    rw [p.dist_end,hl]
  exact (inf_le_right.trans (Q_le_stabilizer_of_dist_two R _ a' he hd)).trans
    (Z_normalized R a')
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
variable {K : Type*} [Group K] [Finite K]
    {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
    (d : CFSG.Quasithin.ChapterC.NaturalSixControl.SourceData L W T)
/-- The actual characteristic replacement supplies the centralizer and endpoint
normalizer input of source (3.3), on its literal critical path. -/
theorem reducedSource_critical_commutator_inputs (h : IntrinsicMSPair d)
    (c : CharacteristicReduction (L.subgroupOf (L ⊔ d.B))
      (d.B.subgroupOf (L ⊔ d.B)))
    (hb : ((originalSource d h).reduce c).geometry.b c.radical = 4)
    {a a' : Vertex c.radical}
    (p : CriticalPath c.radical ((originalSource d h).reduce c).geometry a a') :
    let R₀ := ⁅Z c.radical a,Z c.radical a'⁆
    let Y := V c.radical a ⊓ Q c.radical (p.walk.getVert (p.walk.length-2))
    R₀ ≤ U c.radical a ⊓ U c.radical a' ∧
      Y ≤ centralizer (R₀ : Set (FreeAmalgam c.radical)) ∧
      Y ≤ normalizer (Z c.radical a' : Set (FreeAmalgam c.radical)) := by
  let s := (originalSource d h).reduce c
  exact ⟨s.critical_Z_commutator_le_moving p,
    s.critical_radius_intersection_centralizes (by omega) p,
    s.critical_radius_intersection_normalizes_endpoint hb p⟩
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
