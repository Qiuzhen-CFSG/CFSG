module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition.Dynamics.Kernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.First.Layer.Displacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.LocalStructure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.Selection.Pencil.Choices.LocalAction
public import Theory.GroupTheory.Commutator.CentralizingFactor

/-!
# The first orbit factor has faithful action

The early product hat W_a Q_d = T_t identifies [hat W_a,Z_d] with the
edge displacement of order four. The earlier radius argument places it
in H_c, and the actual critical window and turn put H_c inside U_a.
Irreducibility of the natural group U_a of order eight excludes invariance
of this commutator under G_a. The recorded quotient-conjugation formula
then excludes a nontrivial kernel on the first actual orbit quotient.

Only the literal product (4.5.1)(iv) remains explicit, with producer
`qt-c01-ms93-core-factors-early-layers`. No orbit action, small displacement,
quotient model, or later source conclusion is assumed. Moving generation
and the corresponding commutator obstruction for the selected delta remain
separate obligations; this module does not claim the full two-factor result.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5.1)(iv), printed p.896,
and the centralizer argument for (4.5.4)(iii), printed p.899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition
open NormalizerTransfer
variable {M : Type*} [Group M] {R L : Subgroup M} {geometry : Geometry R}
  {source : LocalSource L R}

private theorem natural_subgroup_dichotomy [Finite M]
    (common : CommonFacts R source geometry) (K : Subgroup (FreeAmalgam R))
    (hK : K ≤ U R (alpha R))
    (hn : stabilizer R (alpha R) ≤ normalizer K) :
    K = ⊥ ∨ K = U R (alpha R) := by
  open Escape.Propagation.Backward.Products.Selection.Choices in
  obtain ⟨model⟩ := localModel_nonempty source (PathCentrality.LocalCommutator.moduleFacts common)
    (alpha R) rfl
  let S := stabilizer R (alpha R)
  have hUS : U R (alpha R) ≤ S := (U_le_Z R _).trans (Z_le_stabilizer R _)
  let e := (subgroupOfEquivOfLe hUS).trans model.equiv
  let n : RankOnePairing.NaturalFactor model.projection ⊤ ((U R (alpha R)).subgroupOf S) ⊥ := {
    marking := MulEquiv.refl _
    coordinates := e.toMonoidHom
    surjective := e.surjective
    kernel := by rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective, bot_subgroupOf]
    normalized := by
      intro g _
      rw [← subgroupOf_normalizer_eq hUS]
      exact U_normalized _ g.property
    action := by
      intro g _ x y h
      exact congrArg Multiplicative.toAdd (model.action g
        ((subgroupOfEquivOfLe hUS) x) ((subgroupOfEquivOfLe hUS) y)
        (congrArg Subtype.val h)) }
  have hm : (⊤ : Subgroup S).map model.projection = ⊤ :=
    map_top_of_surjective _ model.surjective
  have hnorm : (⊤ : Subgroup S) ≤ normalizer (K.subgroupOf S : Set S) := by
    intro g _
    rw [← subgroupOf_normalizer_eq (hK.trans hUS)]
    exact hn g.property
  rcases n.irreducible hm (K.subgroupOf S) (subgroupOf_mono S hK) hnorm with h | h
  · left
    have hh := congrArg (Subgroup.map S.subtype) h
    simpa only [map_subgroupOf_eq_of_le (hK.trans hUS), Subgroup.map_bot] using hh
  · right
    have hh := congrArg (Subgroup.map S.subtype) h
    simpa only [map_subgroupOf_eq_of_le (hK.trans hUS), map_subgroupOf_eq_of_le hUS] using hh

private theorem path_color (p : Higher.SourcePath (alpha R))
    {i : ℕ} (hi : Even i) (hle : i ≤ 14) : color R (p.walk.getVert i) = false :=
  (PathCentrality.RegularPaths.walk_vertex_color p.start_color p.walk
    (by rw [p.length_eq]; exact hle)).mpr hi

private theorem middle_moving [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R)) :
    Vcirc R (p.walk.getVert 6) ≤ hatV R (p.walk.getVert 6) (alpha R) := by
  have hcrit : CriticalPair R (p.walk.getVert 0) (p.walk.getVert 8)
      (geometry.exists_critical _ (path_color p (by decide) (by decide))) := by
    refine ⟨?_, (p.critical 0 (by decide) (by decide)).2⟩
    rw [(geometry.distance_constant _ (path_color p (by decide) (by decide))).trans earlier.distance]
    exact p.dist (by decide) (by decide)
  have hmove := Escape.Propagation.RadiusFour.Forward.Reversal.critical_endpoint_moving
    source common.large_distance (path_color p (by decide) (by decide)) hcrit (s := p.walk.getVert 6)
  have hbefore : Escape.Before (p.walk.getVert 0) (p.walk.getVert 8)
      (p.walk.getVert 6) 2 := by
    constructor
    · exact p.dist (by decide) (by decide)
    · rw [p.dist (i := 0) (j := 6) (by decide) (by decide),
        p.dist (i := 0) (j := 8) (by decide) (by decide)]
  obtain ⟨g, hg, he⟩ := p.turns 6 (by decide) (by decide) (by decide)
  have ht := Escape.Propagation.Rigidity.moving_of_local_act common.large_distance
    (p.walk.getVert 6) (p.walk.getVert 8) (path_color p (by decide) (by decide))
    (hmove hbefore) g hg
  rw [he, p.center_eq] at ht
  exact Early.moving_le_hatV source earlier (path_color p (by decide) (by decide)) ht

/-- The first seed commutator has order four and lies in the irreducible
natural group U_a of order eight. It cannot be invariant under G_a.
The sole additional premise is the literal product (4.5.1)(iv), whose
producer is `qt-c01-ms93-core-factors-early-layers`. -/
theorem first_displacement_not_normalized [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hprod : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)))
    : ¬ stabilizer R (alpha R) ≤ normalizer
      (⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8),
        Z R (p.walk.getVert 8)⁆ : Subgroup (FreeAmalgam R)) := by
  intro hn
  have hc := path_color p (i := 6) (by decide) (by decide)
  have hd := path_color p (i := 8) (by decide) (by decide)
  have hcs : Adjacent R (p.walk.getVert 6) (p.walk.getVert 5) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp
      (p.dist (i := 5) (j := 6) (by decide) (by decide))))
  have hdt : Adjacent R (p.walk.getVert 8) (p.walk.getVert 7) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (SimpleGraph.dist_eq_one_iff_adj.mp
      (p.dist (i := 7) (j := 8) (by decide) (by decide))))
  have has : (cosetGraph R).dist (alpha R) (p.walk.getVert 5) = 1 := by
    simpa only [p.center_eq] using p.dist (i := 4) (j := 5) (by decide) (by decide)
  have hcentral : Z R (p.walk.getVert 8) ≤ centralizer (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) :=
    commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes _ hd)
  have heq := commutator_eq_of_product_centralizing_factor hprod.symm hcentral
  have hcard : Nat.card (⁅Z R (p.walk.getVert 8),
      hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)⁆ : Subgroup (FreeAmalgam R)) = 4 := by
    rw [← heq]
    exact Early.First.Layer.edge_displacement_card common earlier hd hdt
  have hle := Early.First.Layer.hatW_displacement_le_H source earlier hc hcs
    p.two_step_distances.1.le p.two_step_distances.2.1.le has
  rw [commutator_comm] at hn
  have hHU : H R (p.walk.getVert 6) ≤ U R (alpha R) :=
    Early.H_le_neighbor_U common earlier hc
      (by rw [SimpleGraph.dist_comm]; exact p.two_step_distances.1)
      (middle_moving common earlier p)
  rcases natural_subgroup_dichotomy common _ (hle.trans hHU) hn with h | h
  · rw [h, card_bot] at hcard
    omega
  · rw [h, DistanceEight.U_card R common.natural] at hcard
    omega

/-- Faithfulness for the first actual orbit quotient in (4.5.4)(iii).
The only additional source input is (4.5.1)(iv). This applies to any of the
recorded quotient actions and requires no small-displacement or model premise. -/
theorem first_factor_faithful [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hprod : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)))
    (s : OrbitModule source p (p.walk.getVert 8)) :
    letI := s.normal; Function.Injective s.action :=
  s.faithful_of_not_normalized_commutator earlier
    (first_displacement_not_normalized common earlier p hprod)

/-- Assembly on both literal orbit factors. The two remaining source arguments
are exposed as ambient group statements: moving generation at both seeds,
and noninvariance of the delta commutator. Their discharge remains with this
module's assembly owner; this conditional result is not (4.5.4)(iii) alone. -/
theorem orbit_dynamics_of_generation_and_delta_commutator [Finite M]
    (common : CommonFacts R source geometry) (earlier : Earlier R geometry)
    {p : Higher.SourcePath (alpha R)} (δ : DeltaChoice p)
    (hprod : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) =
        (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)))
    (hgen : ∀ v, v = p.walk.getVert 8 ∨ v = δ.vertex →
      ⁅orbitFactor p v, stabilizer R (alpha R)⁆ ⊔
        hatV R (alpha R) (p.walk.getVert 6) = orbitFactor p v)
    (hdelta : ¬ stabilizer R (alpha R) ≤ normalizer
      (⁅hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8), Z R δ.vertex⁆ :
        Subgroup (FreeAmalgam R))) :
    ∀ v, v = p.walk.getVert 8 ∨ v = δ.vertex →
      ∀ s : OrbitModule source p v, letI := s.normal
        Function.Injective s.action ∧ commutatorAction s.action.range (OrbitSpace p v) = ⊤ := by
  intro v hv s
  let := s.normal
  refine ⟨?_, s.full_of_generation (hgen v hv)⟩
  rcases hv with rfl | rfl
  · exact first_factor_faithful common earlier p hprod s
  · exact s.faithful_of_not_normalized_commutator earlier hdelta

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.Quotients.SecondLayer.Recognition
