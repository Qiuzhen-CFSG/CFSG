module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticRadiusChief
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalRootNormalizer
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Frattini and quadratic kernel action on the original radius

Every original radius satisfies [V,Φ(Q)] ≤ C(V) and [V,Q,Q] ≤ C(V).
If radius centrality holds, these follow immediately. Otherwise every
critical image has order four. The original midpoint kernel normalizes
both endpoint seeds, and the root-normalizer calculation kills its Frattini
subgroup and its repeated action modulo the full opposite kernel.
Generation by the literal radius seeds gives the two stated bounds.

These are unconditional original-overgroup applications, including outer
ambient actions. The first commutator [V,Q] need not vanish modulo C(V)
by this argument; small-image radius centrality, the terminal distance-four
exclusion and full SymplecticPlaneRecognition remain required.

Source: MS93 (5.2)(ii), pp.914--915, with the outer extension treated explicitly
for the original group in Aschbacher--Smith 9.3.10, pp.734--735.
-/

open scoped IsMulCommutative commutatorElement
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.SourceComparison
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

/-- Both bounds hold on every original radius, with no inner-action or
large-critical-image premise. -/
theorem original_radius_kernel_action_bounds
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (_geometry : Geometry R) (a : Vertex R), color R a = false →
      ⁅V R a,(frattini (Q R a)).map (Q R a).subtype⁆ ≤ centralizer (V R a : Set (FreeAmalgam R)) ∧
      ⁅⁅V R a,Q R a⁆,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
  intro R geometry a ha
  have hphiP : (frattini (Q R a)).map (Q R a).subtype ≤ Q R a := map_subtype_le _
  by_cases hcentral : ⁅V R a,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R))
  · exact ⟨(commutator_mono le_rfl hphiP).trans hcentral,
      (le_normalizer_iff_commutator_le_left.mp
        (normalizer_commutator_ge_right (V R a) (Q R a))).trans hcentral⟩
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hcard,hsq,hQne⟩ :=
    source_tensor_sp4_quotient_data D m.sylow_not_normalizes_component c.M
      (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
      c.outside c.sylow (pResidual 2 c.M) c.component_product.1
      BinaryField.four.card_eq eK c.fitting_center.1 c.component_product.2.2.2
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hself : centralizer (pCore 2 c.M : Set c.M) ≤ pCore 2 c.M := by
    simpa only [c.fitting_center.1] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := c.M))
  have hne : R ≠ ⊥ := fun hr => hQne (le_bot_iff.mp (hr ▸ hodd.twoCore_le))
  have hb : geometry.b R = 4 := c.original_geometry_eq_four eK geometry
  have hlocal {u z : Vertex R} (hu : color R u = false) (hz : color R z = false)
      (hua : (cosetGraph R).dist u a ≤ 2) (hza : (cosetGraph R).dist z a ≤ 2) :
      ⁅Z R u,(frattini (Q R a)).map (Q R a).subtype⁆ ≤ Q R z ∧
        ⁅⁅Z R u,Q R a⁆,Q R a⁆ ≤ Q R z := by
    have hPz : Q R a ≤ stabilizer R z :=
      Q_le_stabilizer_of_dist_le_two a z ha hz (by rwa [SimpleGraph.dist_comm])
    have hPu : Q R a ≤ stabilizer R u :=
      Q_le_stabilizer_of_dist_le_two a u ha hu (by rwa [SimpleGraph.dist_comm])
    have hNQ : ⁅Q R z,Q R a⁆ ≤ Q R z :=
      le_normalizer_iff_commutator_le_left.mp (hPz.trans (Q_normalized R z))
    by_cases hUZ : Z R u ≤ Q R z
    · have hfirst : ⁅Z R u,Q R a⁆ ≤ Q R z :=
        (commutator_mono hUZ le_rfl).trans hNQ
      exact ⟨(commutator_mono le_rfl hphiP).trans hfirst,
        (commutator_mono hfirst le_rfl).trans hNQ⟩
    have htri := (cosetGraph_connected R).dist_triangle (u := u) (v := a) (w := z)
    rw [SimpleGraph.dist_comm (u := a) (v := z)] at htri
    have hcrit : CriticalPair R u z (geometry.exists_critical u hu) := by
      refine ⟨le_antisymm ?_ (criticalDistance_le R u _ hUZ),hUZ⟩
      rw [geometry.distance_constant u hu]
      change (cosetGraph R).dist u z ≤ geometry.b R
      omega
    let path : CriticalPath R geometry u z := CriticalPath.ofPair hu hcrit
    have hsmall := (c.original_noncentral_radius_small_critical_data eK geometry ha
      hcentral path).1
    change (Q R z).relIndex (Z R u) = 4 at hsmall
    exact original_small_critical_normalizer_bounds R hms hodd.isPGroup hne hodd.twoCore_le
      hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      hcard hBC hsq path (by omega) (Q R a)
      (Q_isPGroup R hodd.isPGroup hodd.twoCore_le a ha) hPz
      (hPu.trans (Z_normalized R u)) (by omega)
  let I := {u : Vertex R // color R u = false ∧ (cosetGraph R).dist u a ≤ 2}
  have hUV (u : I) : Z R u.val ≤ V R a :=
    le_iSup_of_le u.val (le_iSup_of_le u.property.2 le_rfl)
  have hV : V R a = ⨆ u : I,Z R u.val := by
    apply le_antisymm
    · apply (V_le_iff R ha _).mpr
      intro u hu hua
      exact le_iSup_of_le (⟨u,hu,hua⟩ : I) le_rfl
    · exact iSup_le hUV
  have hcent (u : I) :
      ⁅Z R u.val,(frattini (Q R a)).map (Q R a).subtype⁆ ≤ centralizer (V R a : Set (FreeAmalgam R)) ∧
      ⁅⁅Z R u.val,Q R a⁆,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
    constructor
    · apply le_centralizer_iff.mp
      apply (V_le_iff R ha _).mpr
      intro z hz hza
      exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z hz)).trans
        (centralizer_le (hlocal u.property.1 hz u.property.2 hza).1)
    · apply le_centralizer_iff.mp
      apply (V_le_iff R ha _).mpr
      intro z hz hza
      exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z hz)).trans
        (centralizer_le (hlocal u.property.1 hz u.property.2 hza).2)
  have hUQ (u : I) : Z R u.val ≤ Q R a :=
    (hUV u).trans (geometry.V_le_Q (by omega) a ha)
  have hcommUQ (u : I) : ⁅Z R u.val,Q R a⁆ ≤ Q R a := by
    apply (le_normalizer_iff_commutator_le_left.mp ?_).trans (hUQ u)
    exact (Q_le_stabilizer_of_dist_le_two a u.val ha u.property.1
      (by rw [SimpleGraph.dist_comm]; exact u.property.2)).trans (Z_normalized R u.val)
  refine ⟨?_,?_⟩
  · have hnormal : V R a ≤ normalizer (centralizer (V R a : Set (FreeAmalgam R)) : Set _) :=
      (le_centralizer_iff.mpr le_rfl).trans (Subgroup.centralizer_le_normalizer _)
    have hh := commutator_iSup_le_of_relative_normal (V R a)
      ((frattini (Q R a)).map (Q R a).subtype)
      (centralizer (V R a : Set (FreeAmalgam R))) (fun u : I => Z R u.val)
      hnormal hUV (fun u => (hcent u).1)
    rwa [←hV] at hh
  · have heq : ⁅⁅V R a,Q R a⁆,Q R a⁆ = ⨆ u : I,⁅⁅Z R u.val,Q R a⁆,Q R a⁆ := by
      rw [hV,commutator_iSup_of_le _ _ hUQ,commutator_iSup_of_le _ _ hcommUQ]
    rw [heq]
    exact iSup_le fun u => (hcent u).2

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
