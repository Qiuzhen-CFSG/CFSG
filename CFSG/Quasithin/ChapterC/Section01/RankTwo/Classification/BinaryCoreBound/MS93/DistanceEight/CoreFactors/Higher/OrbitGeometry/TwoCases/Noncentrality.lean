module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.Noncentrality.Sections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Intersections.Basic

/-!
# The noncentral seed commutator in MS93 (4.5.5)

Put a=alpha, c=a+2, d=a+4 and e=a+6 on the supplied source path. If
[hat W_c,hat V_a^(6)] were contained in Z_a, the source Q-product and
[hat W_c,Q_c] ≤ Z_c would imply [hat W_c,Q_a] ≤ hat V_c. The turn at c
puts Z_a in hat V_c. Faithfulness of the actual doubled-dual quotient
hat W_c/hat V_c then forces Q_a ≤ Q_c. But Q_a would centralize Z_c,
hence its G_a orbit span hat V_a, forcing H_a=1. The earlier critical
configuration already proves H_a nontrivial.

The literal products and identities from (4.5.1)--(4.5.3) remain explicit,
with producer qt-c01-ms93-core-factors-early-layers. The marked quotient
witness belongs to qt-c01-ms93-higher-marked-quotients. No conclusion from
(4.5.5), core-center or fixed-factor calculation is assumed. The two
applications remove the noncentrality premise from the existing consumers;
the independent pair geometry remains explicit. Final source assembly
belongs to qt-c01-ms93-higher-conjugate-pairs.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.898--899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.Noncentrality
open NormalizerTransfer PathCentrality
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

private theorem span_le {G : Type*} [Group G] {A P N : Subgroup G}
    (hA : A ≤ N) (hN : P ≤ normalizer N) : conjugatesIn A P ≤ N := by
  apply iSup_le
  intro g
  exact (map_mono hA).trans
    (mem_normalizer_iff_map_conj_eq.mp (hN (P.inv_mem g.property))).le

/-- The preceding nontrivial H excludes containment of two neighboring kernels.
Containment would make Q_a centralize the orbit span hat V_a and hence Vcirc_a. -/
theorem Q_not_le_next_Q [Finite M]
    (source : LocalSource L R) (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a c : Vertex R}
    (ha : color R a = false) (hc : color R c = false)
    (hca : (cosetGraph R).dist c a = 2)
    (hVa : hatV R a c = Vcirc R a ⊔ Z R a) : ¬ Q R a ≤ Q R c := by
  intro hQ
  let P := stabilizer R a
  let D := commutatorPreimage P (Q R a) ⊥
  have hN : P ≤ normalizer (⊥ : Subgroup (FreeAmalgam R)) := le_normalizer_of_normal
  have hZlocal : Z R c ≤ P :=
    (Z_le_localZSpan R c a).trans
      ((hatV_le_radius R hca.le).trans
        ((geometry.V_le_Q (by rw [earlier.distance]; decide) a ha).trans (fun _ hx => hx.1)))
  have hZ : Z R c ≤ D := le_commutatorPreimage hZlocal
    ((commutator_mono le_rfl hQ).trans (geometry.centralizes c hc).le)
  have hn : P ≤ normalizer D := commutatorPreimage_normalized P (Q R a) ⊥ P
    hN P.le_normalizer (Q_normalized R a) hN
  have hV : hatV R a c ≤ D := by
    rw [hatV_eq_conjugatesIn]
    exact span_le hZ hn
  apply Early.H_ne_bot source common earlier ha
  apply le_bot_iff.mp
  change ⁅Vcirc R a, Q R a⁆ ≤ ⊥
  exact (commutator_mono ((le_sup_left.trans hVa.ge).trans hV) le_rfl).trans
    (commutator_commutatorPreimage_le P (Q R a) ⊥ hN)


/-- The opening assertion in MS93 (4.5.5). The contrary assumption and the
proved Q-product make Q_a centralize hat W_c / hat V_c. Its faithful marked
action would give Q_a ≤ Q_c, contradicting the earlier nontrivial H_a.
The five early conclusions and the actual (4.5.4)(iii) section remain explicit. -/
theorem seed_commutator_not_le_Z [Finite M]
    (source : LocalSource L R) (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (hVd : hatV R (p.walk.getVert 8) (p.walk.getVert 10) =
      Vcirc R (p.walk.getVert 8) ⊔ Z R (p.walk.getVert 8))
    (hleft : (hatW R (p.walk.getVert 2) (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 6) : Set (FreeAmalgam R)) = (Q R (p.walk.getVert 5) : Set (FreeAmalgam R)))
    (hright : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) = (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)))
    (hW : ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (p.walk.getVert 6)⁆ ≤ Z R (p.walk.getVert 6))
    (sectionModel : SeedSection (source := source) (common := common)
      (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) :
    ¬ ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)⁆ ≤ Z R (alpha R) := by
  intro hcentral
  let a := alpha R
  let c := p.walk.getVert 6
  let d := p.walk.getVert 8
  let e := p.walk.getVert 10
  let N := hatV R c d
  let A := hatW R c d e
  let T := hatSix R a c d e
  let K := Q R a ⊓ Q R c ⊓ Q R d
  let P := stabilizer R c
  have hc : color R c = false :=
    (RegularPaths.walk_vertex_color p.start_color p.walk
      (by rw [p.length_eq]; decide)).mpr (by decide)
  have hP : Q R a ≤ P := Q_le_stabilizer_of_dist_two R a c rfl
    (by rw [SimpleGraph.dist_comm]; exact p.two_step_distances.1)
  have hZc : Z R c ≤ N := Early.Z_le_hatV hc
    (p.dist (i := 6) (j := 8) (by decide) (by decide))
  have hZa : Z R a ≤ N := by
    obtain ⟨g, hg, ht⟩ := p.turns 6 (by decide) (by decide) (by decide)
    have ht' : act R g d = a := by simpa only [p.center_eq] using ht
    have hh : rightConjugate (Z R d) g ≤ N := by
      change rightConjugate (Z R d) g ≤ hatV R c d
      rw [hatV_eq_conjugatesIn]
      exact le_iSup (fun k : stabilizer R c => rightConjugate (Z R d) k) ⟨g, hg⟩
    simpa only [rightConjugate, ← Z_act, ht'] using hh
  let D := commutatorPreimage P A N
  have hTD : T ≤ D := le_commutatorPreimage ((p.hatSix_le_Q earlier).trans hP)
    (by rw [commutator_comm]; exact hcentral.trans hZa)
  have hKD : K ≤ D := le_commutatorPreimage ((inf_le_left.trans inf_le_left).trans hP)
    (by
      rw [commutator_comm]
      exact (commutator_mono le_rfl (inf_le_left.trans inf_le_right)).trans (hW.trans hZc))
  have hQD : Q R a ≤ D := by
    intro x hx
    have hx' : x ∈ (Q R a : Set (FreeAmalgam R)) := hx
    rw [SourcePath.Q_product p earlier hVa hVd hleft hright] at hx'
    obtain ⟨t, ht, k, hk, rfl⟩ := hx'
    exact D.mul_mem (hTD ht) (hKD hk)
  have hQcomm : ⁅Q R a, A⁆ ≤ N := (commutator_mono hQD le_rfl).trans
    (commutator_commutatorPreimage_le P A N (hatV_normalized R c d))
  exact Q_not_le_next_Q source common earlier rfl hc p.two_step_distances.1 hVa
    (sectionModel.le_Q_of_commutator hP hQcomm)


/-- Apply the proved noncentrality to the literal pair-bound consumer.
Only the independent conjugate-pair bound and the allowed source witnesses remain. -/
theorem commutator_layers_of_pair_bounds [Finite M]
    (source : LocalSource L R) (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (hVd : hatV R (p.walk.getVert 8) (p.walk.getVert 10) =
      Vcirc R (p.walk.getVert 8) ⊔ Z R (p.walk.getVert 8))
    (hleft : (hatW R (p.walk.getVert 2) (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 6) : Set (FreeAmalgam R)) = (Q R (p.walk.getVert 5) : Set (FreeAmalgam R)))
    (hright : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) = (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)))
    (hW : ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (p.walk.getVert 6)⁆ ≤ Z R (p.walk.getVert 6))
    (seedModel : SeedSection (source := source) (common := common)
      (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10))
    (sectionModel : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (hpairs : ∀ g : stabilizer R (alpha R),
      ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
        rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) g⁆ ≤
          hatV R (alpha R) (p.walk.getVert 6)) :
    ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10), Q R (alpha R)⁆ ⊔
      Z R (alpha R) = hatV R (alpha R) (p.walk.getVert 6) ∧
    ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)⁆ ⊔
      Z R (alpha R) = hatV R (alpha R) (p.walk.getVert 6) :=
  SourcePath.commutator_layers_of_pair_bounds source common earlier p hVa hVd hleft hright hW sectionModel hpairs
    (seed_commutator_not_le_Z source common earlier p hVa hVd hleft hright hW seedModel)

/-- Apply the proved noncentrality to the existing two-Z-case assembly.
This discharges its opening assertion while leaving its independent geometry explicit. -/
theorem commutator_layers_of_Z_geometry [Finite M]
    (source : LocalSource L R) (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (hVd : hatV R (p.walk.getVert 8) (p.walk.getVert 10) =
      Vcirc R (p.walk.getVert 8) ⊔ Z R (p.walk.getVert 8))
    (hleft : (hatW R (p.walk.getVert 2) (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 6) : Set (FreeAmalgam R)) = (Q R (p.walk.getVert 5) : Set (FreeAmalgam R)))
    (hright : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) = (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)))
    (hW : ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (p.walk.getVert 6)⁆ ≤ Z R (p.walk.getVert 6))
    (seedModel : SeedSection (source := source) (common := common)
      (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10))
    (sectionModel : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (facts : ZCaseGeometry p) :
    ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10), Q R (alpha R)⁆ ⊔
      Z R (alpha R) = hatV R (alpha R) (p.walk.getVert 6) ∧
    ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)⁆ ⊔
      Z R (alpha R) = hatV R (alpha R) (p.walk.getVert 6) :=
  TwoCases.commutator_layers_of_Z_geometry source common earlier p hVa hVd hleft hright hW sectionModel facts
    (seed_commutator_not_le_Z source common earlier p hVa hVd hleft hright hW seedModel)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.Noncentrality
