module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.Decomposition

/-!
# From conjugate-pair bounds to the Q commutator in MS93 (4.5.5)

The source Q product leaves a factor in Q_a ∩ Q_(a+2) ∩ Q_(a+4).
The preceding bound [hat W_(a+2),Q_(a+2)] ≤ Z_(a+2) controls its
commutator with the generating seed. The conjugate-pair estimate controls
the other factor, by the already proved derived-group bound. Normality
inside G_a extends this estimate from the seed to the whole third layer.

The final consumer supplies this Q bound to Higher's checked saturation
argument. The conjugate-pair and noncentrality calculations at the bottom
of p.899 remain explicit, so this is not yet the full source theorem.
The preceding-source inputs belong to qt-c01-ms93-core-factors-early-layers;
the marked dual section belongs to qt-c01-ms93-higher-marked-quotients.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.896--899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry
open NormalizerTransfer PathCentrality
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

private theorem span_le {G : Type*} [Group G] {A P N : Subgroup G}
    (hA : A ≤ N) (hN : P ≤ normalizer N) : conjugatesIn A P ≤ N := by
  apply iSup_le
  intro g
  exact (map_mono hA).trans
    (mem_normalizer_iff_map_conj_eq.mp (hN (P.inv_mem g.property))).le

private theorem Q_commutator_le_of_product {a c d e : Vertex R}
    {K : Subgroup (FreeAmalgam R)}
    (hS : hatSix R a c d e ≤ Q R a) (hK : K ≤ Q R a ⊓ Q R c)
    (hprod : (Q R a : Set (FreeAmalgam R)) =
      (hatSix R a c d e : Set (FreeAmalgam R)) * (K : Set (FreeAmalgam R)))
    (hW : ⁅hatW R c d e, Q R c⁆ ≤ Z R c)
    (hderived : ⁅hatSix R a c d e, hatSix R a c d e⁆ ≤ hatV R a c) :
    ⁅hatSix R a c d e, Q R a⁆ ≤ hatV R a c := by
  let P := stabilizer R a
  let N := hatV R a c
  let S := hatSix R a c d e
  let W := hatW R c d e
  have hQP : Q R a ≤ P := fun _ hx => hx.1
  have hPN : P ≤ normalizer N := hatV_normalized R a c
  have hseed : W ≤ S := hatW_seed_le_hatSix a c d e
  have hZcN : Z R c ≤ N := Z_le_localZSpan R c a
  let C := commutatorPreimage P W N
  have hSC : S ≤ C := le_commutatorPreimage (hS.trans hQP)
    ((commutator_mono le_rfl hseed).trans hderived)
  have hKC : K ≤ C := by
    apply le_commutatorPreimage ((hK.trans inf_le_left).trans hQP)
    rw [commutator_comm]
    exact (commutator_mono le_rfl (hK.trans inf_le_right)).trans (hW.trans hZcN)
  have hQC : Q R a ≤ C := by
    intro x hx
    have hx' : x ∈ (Q R a : Set (FreeAmalgam R)) := hx
    rw [hprod] at hx'
    obtain ⟨s, hs, k, hk, rfl⟩ := hx'
    exact C.mul_mem (hSC hs) (hKC hk)
  have hQW : ⁅Q R a, W⁆ ≤ N :=
    (commutator_mono hQC le_rfl).trans (commutator_commutatorPreimage_le P W N hPN)
  let D := commutatorPreimage P (Q R a) N
  have hWD : W ≤ D := le_commutatorPreimage (hseed.trans (hS.trans hQP))
    (by rwa [commutator_comm])
  have hPD : P ≤ normalizer D :=
    commutatorPreimage_normalized P (Q R a) N P hPN P.le_normalizer (Q_normalized R a) hPN
  exact (commutator_mono (span_le hWD hPD) le_rfl).trans
    (commutator_commutatorPreimage_le P (Q R a) N hPN)

/-- The second local bound required by Higher.commutator_layers_of_local_bounds.
The literal earlier products supply the Q decomposition; the conjugate-pair
bound supplies the derived bound. The triple intersection is retained. -/
theorem SourcePath.Q_commutator_le_of_conjugate_bounds [Finite M]
    {a : Vertex R} (p : Higher.SourcePath a) (earlier : Earlier R geometry)
    (hVa : hatV R a (p.walk.getVert 6) = Vcirc R a ⊔ Z R a)
    (hVd : hatV R (p.walk.getVert 8) (p.walk.getVert 10) =
      Vcirc R (p.walk.getVert 8) ⊔ Z R (p.walk.getVert 8))
    (hleft : (hatW R (p.walk.getVert 2) a (p.walk.getVert 6) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 6) : Set (FreeAmalgam R)) = (Q R (p.walk.getVert 5) : Set (FreeAmalgam R)))
    (hright : (hatW R a (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) = (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)))
    (hW : ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (p.walk.getVert 6)⁆ ≤ Z R (p.walk.getVert 6))
    (hpairs : ∀ g : stabilizer R a,
      ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
        rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) g⁆ ≤
          hatV R a (p.walk.getVert 6)) :
    ⁅hatSix R a (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10), Q R a⁆ ≤
      hatV R a (p.walk.getVert 6) := by
  have hS := p.hatSix_le_Q earlier
  have hderived := hatSix_derived_le_of_conjugate_bounds
    ((hatW_seed_le_hatSix a _ _ _).trans (hS.trans (fun _ hx => hx.1))) hpairs
  exact Q_commutator_le_of_product hS inf_le_left
    (SourcePath.Q_product p earlier hVa hVd hleft hright) hW hderived

/-- A consumer of the proved Q-bound in the actual (4.5.5) assembly.
Only the marked dual section, the two local geometric calculations, and
literal preceding-source outputs remain explicit. -/
theorem SourcePath.commutator_layers_of_pair_bounds [Finite M]
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
    (sectionModel : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (hpairs : ∀ g : stabilizer R (alpha R),
      ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
        rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) g⁆ ≤
          hatV R (alpha R) (p.walk.getVert 6))
    (hnon : ¬ ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)⁆ ≤ Z R (alpha R)) :
    ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10), Q R (alpha R)⁆ ⊔
      Z R (alpha R) = hatV R (alpha R) (p.walk.getVert 6) ∧
    ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)⁆ ⊔
      Z R (alpha R) = hatV R (alpha R) (p.walk.getVert 6) :=
  commutator_layers_of_local_bounds source common earlier p.two_step_distances.1.le
    p.two_step_distances.2.1.le p.two_step_distances.2.2.le sectionModel hpairs
    (SourcePath.Q_commutator_le_of_conjugate_bounds p earlier hVa hVd hleft hright hW hpairs) hnon

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry
