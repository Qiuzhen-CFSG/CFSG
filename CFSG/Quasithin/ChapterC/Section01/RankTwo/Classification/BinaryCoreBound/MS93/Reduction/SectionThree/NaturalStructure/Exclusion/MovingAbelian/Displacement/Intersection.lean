module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.Exclusion.MovingAbelian.Displacement.Transfer

/-!
# The radius intersection and the literal source-(3.3) bound

For a critical path a--c--a' of length four, the radius intersection
V_a intersect Q_c lies in the penultimate edge kernel and centralizes the
source commutator [Z_a,Z_a']. The additional commutator on the right of
(3.3) vanishes because V_a lies in Q_a. This proves the bound on Z_a'.
In the doubled and central-extension branches X_a' equals Z_a', giving the
full endpoint bound. The index-two outer extension needs its own calculation;
this module does not identify its X and Z.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3), pp.866--868, and the
radius-intersection paragraph of (3.8), printed p.878.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open ModuleAlternatives
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The literal source-(3.3) estimate for the radius intersection acts on
Z at the critical endpoint. This proof retains that endpoint layer. -/
theorem radius_intersection_Z (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (hbad : BadCase source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (c : Vertex R) (hac : (cosetGraph R).dist a c = 2)
    (hca' : (cosetGraph R).dist c a' = 2) :
    ⁅V R a ⊓ Q R c, Z R a'⁆ ≤ ⁅X R a, X R a'⁆ := by
  obtain ⟨t, hct, ha't⟩ := exists_common_neighbor_of_dist_two R c a' hca'
  have ha' := critical_endpoint_color R a ha _ hc
  have ht : color R t = true := by
    have hn := adjacent_color_ne R ha't
    cases he : color R t <;> simp_all
  have hd : (cosetGraph R).dist a a' = 4 :=
    (hc.1.trans (geometry.distance_constant a ha)).trans (distance_eq_four source geometry hb hbad)
  have hpath : (cosetGraph R).dist a t + 1 = (cosetGraph R).dist a a' := by
    have hct1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hct)
    have hta'1 := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R ha't))
    have h₁ := (cosetGraph_connected R).dist_triangle (u := a) (v := c) (w := t)
    have h₂ := (cosetGraph_connected R).dist_triangle (u := a) (v := t) (w := a')
    omega
  let Y := V R a ⊓ Q R c
  have hYQ : Y ≤ Q R a := inf_le_left.trans (geometry.V_le_Q hb a ha)
  have hYC : Y ≤ centralizer (X R a : Set (FreeAmalgam R)) :=
    hYQ.trans (Q_le_centralizer_X R a)
  have hzero : ⁅X R a ⊓ Q R a', Y⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (inf_le_left.trans (le_centralizer_iff.mp hYC))
  have hZXa := geometry.omega_bound a ha (by
    rw [geometry.distance_constant a ha]; change 0 < geometry.b R; omega)
  have hZXa' := (critical_endpoint_choice source geometry (by omega) a ha a' hc).1
  have hRX : ⁅Z R a, Z R a'⁆ ≤ X R a :=
    (commutator_mono hZXa hZXa').trans
      ((critical_commutator_le_intersection source geometry (by omega) a ha a' hc).trans inf_le_left)
  have hY : Y ≤ Q R t ⊓ centralizer ((⁅Z R a, Z R a'⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) :=
    le_inf (inf_le_right.trans (Q_le_adjacent_h R ht hct)) (hYC.trans (centralizer_le hRX))
  have h := badCase_source33Bound source geometry (by omega) hbad a ha a' hc t ha't hpath Y hY
  rwa [hzero, sup_bot_eq, commutator_comm] at h

/-- The doubled branch supplies the full X-endpoint intersection bound. -/
theorem splitDouble_radius_intersection_X (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (h : SplitDouble source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (c : Vertex R) (hac : (cosetGraph R).dist a c = 2)
    (hca' : (cosetGraph R).dist c a' = 2) :
    ⁅V R a ⊓ Q R c, X R a'⁆ ≤ ⁅X R a, X R a'⁆ := by
  have hh := radius_intersection_Z source geometry hb (Or.inl h) a ha a' hc c hac hca'
  rwa [← SourceCalculation.splitDouble_X_eq_Z source geometry (by omega) h a'
    (critical_endpoint_color R a ha _ hc)] at hh

/-- The central-extension branch supplies the same full X-endpoint bound. -/
theorem centralExtension_radius_intersection_X (source : LocalSource L R) (geometry : Geometry R)
    (hb : 2 < geometry.b R) (h : CentralExtension source)
    (a : Vertex R) (ha : color R a = false) (a' : Vertex R)
    (hc : CriticalPair R a a' (geometry.exists_critical a ha))
    (c : Vertex R) (hac : (cosetGraph R).dist a c = 2)
    (hca' : (cosetGraph R).dist c a' = 2) :
    ⁅V R a ⊓ Q R c, X R a'⁆ ≤ ⁅X R a, X R a'⁆ := by
  have hh := radius_intersection_Z source geometry hb (Or.inr (Or.inl h)) a ha a' hc c hac hca'
  rwa [← SourceCalculation.centralExtension_X_eq_Z source geometry (by omega) h a'
    (critical_endpoint_color R a ha _ hc)] at hh

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
