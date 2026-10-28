module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Sections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Ball

/-!
# Assembly of the higher commutator layers

The local bounds for pairs of conjugate generators place the derived
subgroup in hat V. A nonzero image modulo Z then fills the marked dual
section. Since hat Six lies in Q, monotonicity gives the same equality for
its commutator with Q. These are the two equalities of MS93 (4.5.5).

The marked-section witness and the local bounds remain explicit inputs.
They must be supplied by (4.5.4) and the two path cases at the bottom of
printed p.899 before this becomes the source theorem. In particular this
conditional assembly does not establish the core-center or fixed-factor
equalities of (4.5).
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher
open NormalizerTransfer PathCentrality
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- The published nested span lies in Q, by its radius-six bound and b=8. -/
theorem hatSix_le_Q (earlier : Earlier R geometry)
    {a c d e : Vertex R} (ha : color R a = false)
    (hca : (cosetGraph R).dist c a ≤ 2) (hdc : (cosetGraph R).dist d c ≤ 2)
    (hed : (cosetGraph R).dist e d ≤ 2) : hatSix R a c d e ≤ Q R a :=
  (hatSix_le_radius R hca hdc hed).trans
    (Escape.Propagation.RadiusFour.VBall_le_Q a ha 6 (by rw [earlier.distance]; omega))

/-- The actual seed generating the third layer is a subgroup of that layer. -/
theorem hatW_seed_le_hatSix (a c d e : Vertex R) :
    hatW R c d e ≤ hatSix R a c d e := by
  intro x hx
  apply (le_iSup (fun g : stabilizer R a => rightConjugate (hatW R c d e) g) 1)
  refine ⟨x, hx, ?_⟩
  simp

/-- Conditional (4.5.5), discharging the saturation and passage from local
conjugate bounds to the whole derived subgroup. The remaining hypotheses
are the marked section of (4.5.4)(v) and local calculations on p.899. -/
theorem commutator_layers_of_local_bounds
    (source : LocalSource L R) (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {c d e : Vertex R}
    (hca : (cosetGraph R).dist c (alpha R) ≤ 2)
    (hdc : (cosetGraph R).dist d c ≤ 2) (hed : (cosetGraph R).dist e d ≤ 2)
    (sectionModel : MarkedDualSection source common (hatV R (alpha R) c) (Z R (alpha R)))
    (hpairs : ∀ g : stabilizer R (alpha R),
      ⁅hatW R c d e, rightConjugate (hatW R c d e) g⁆ ≤ hatV R (alpha R) c)
    (hQcomm : ⁅hatSix R (alpha R) c d e, Q R (alpha R)⁆ ≤ hatV R (alpha R) c)
    (hnon : ¬ ⁅hatW R c d e, hatSix R (alpha R) c d e⁆ ≤ Z R (alpha R)) :
    ⁅hatSix R (alpha R) c d e, Q R (alpha R)⁆ ⊔ Z R (alpha R) = hatV R (alpha R) c ∧
      ⁅hatSix R (alpha R) c d e, hatSix R (alpha R) c d e⁆ ⊔ Z R (alpha R) =
        hatV R (alpha R) c := by
  let S := hatSix R (alpha R) c d e
  have hSQ : S ≤ Q R (alpha R) := hatSix_le_Q earlier rfl hca hdc hed
  have hseed : hatW R c d e ≤ S := hatW_seed_le_hatSix _ _ _ _
  have hderived : ⁅S, S⁆ ≤ hatV R (alpha R) c :=
    hatSix_derived_le_of_conjugate_bounds
      (hseed.trans (hSQ.trans (fun _ hx => hx.1))) hpairs
  have hnormalized : Mbar R ≤ normalizer (⁅S, S⁆ : Subgroup (FreeAmalgam R)) := by
    rw [← stabilizer_m_base, ← alpha]
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hatSix_normalized R (alpha R) c d e hg)]
  have hnonzero : ¬ ⁅S, S⁆ ≤ Z R (alpha R) := fun h =>
    hnon ((commutator_mono hseed le_rfl).trans h)
  have heq := sectionModel.sup_eq_of_not_le hderived hnormalized hnonzero
  refine ⟨le_antisymm (sup_le hQcomm sectionModel.lower_le) ?_, heq⟩
  exact heq.ge.trans (sup_le_sup (commutator_mono le_rfl hSQ) le_rfl)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher
