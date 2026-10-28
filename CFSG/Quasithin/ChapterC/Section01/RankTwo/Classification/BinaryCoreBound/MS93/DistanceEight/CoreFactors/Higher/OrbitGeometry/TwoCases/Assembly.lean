module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.Noncentrality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry

/-!+# The two local calculations and their MS93 (4.5.5) application

For the supplied path, put a=alpha, c=a+2, d=a+4 and e=a+6. The
constructed Z-case geometry bounds the commutator of hat W_c with each
of its actual G_a-conjugates by hat V_a. Faithfulness of the very same
marked section at c excludes [hat W_c,hat V_a^(6)] ≤ Z_a. The resulting
two local calculations discharge both geometric premises of LocalBounds,
giving the Q-commutator and derived-group equalities modulo Z_a.

The neighboring section is pulled back using one k with a^k=c. Its
reuse in the noncentrality proof transports c,d,e simultaneously by k⁻¹;
no second section witness or independence of forward choices is assumed.
Both pair sections here are the doubled-dual sections of (4.5.4)(iii),
with the same CommonFacts marking. The moving quotient of (4.5.4)(iv),
whose correct natural orientation is false, is not needed.

Only literal preceding-source premises remain: |H_a|=4 from (4.5.1)(v),
the two Q-products from (4.5.1)(iv), the first-layer identities from
(4.5.3)(i), the forward bound from (4.5.3)(ii), and the seed bound from
(4.5.3)(iii). Their producer is qt-c01-ms93-core-factors-early-layers.
The actual marked sections (4.5.4)(iii),(v) belong to
qt-c01-ms93-higher-marked-quotients. Their final discharge remains with
qt-c01-ms93-higher-orbit-geometry and the higher-layer assembly; neither
Z-case geometry nor opening noncentrality remains an input here.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.898--899,
especially the two cases at the bottom of p.899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases
open NormalizerTransfer PathCentrality
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

private def seedSectionOfPullback
    {source : LocalSource L R} {common : CommonFacts R source geometry}
    {c d e : Vertex R} (k : FreeAmalgam R) (hk : act R k (alpha R) = c)
    (s : MarkedPairSection source common
      (rightConjugate (hatW R c d e) k⁻¹)
      (rightConjugate (hatV R c d) k⁻¹) true) :
    Noncentrality.SeedSection (source := source) (common := common) c d e := by
  have hback : act R k⁻¹ c = alpha R := by
    rw [← hk, ← act_mul, mul_inv_cancel, act_one]
  exact {
    transport := k⁻¹
    at_base := hback
    model := by simpa only [rightConjugate_hatW, rightConjugate_hatV, hback] using s
  }

/-- The two local calculations in the source proof of (4.5.5). The same
actual doubled-dual section at c supplies both the neighboring action and
the faithful-action contradiction; neither conclusion is assumed. -/
theorem local_calculations [Finite M]
    (source : LocalSource L R) (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (firstSection : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (secondSection : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true)
    (k : FreeAmalgam R) (hk : act R k (alpha R) = p.walk.getVert 6)
    (neighborSection : MarkedPairSection source common
      (rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) k⁻¹)
      (rightConjugate (hatV R (p.walk.getVert 6) (p.walk.getVert 8)) k⁻¹) true)
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hVd : hatV R (p.walk.getVert 8) (p.walk.getVert 10) =
      Vcirc R (p.walk.getVert 8) ⊔ Z R (p.walk.getVert 8))
    (hH : Nat.card (H R (alpha R)) = 4)
    (hforward : ⁅hatV R (p.walk.getVert 6) (p.walk.getVert 8),
      Q R (p.walk.getVert 8)⁆ ≤ Z R (p.walk.getVert 8))
    (hleft : (hatW R (p.walk.getVert 2) (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 6) : Set (FreeAmalgam R)) = (Q R (p.walk.getVert 5) : Set (FreeAmalgam R)))
    (hright : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) = (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)))
    (hW : ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (p.walk.getVert 6)⁆ ≤ Z R (p.walk.getVert 6)) :
    (∀ g : stabilizer R (alpha R),
      ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
        rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) g⁆ ≤
          hatV R (alpha R) (p.walk.getVert 6)) ∧
    ¬ ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)⁆ ≤
        Z R (alpha R) := by
  refine ⟨ZGeometry.pair_bounds_of_marked_sections source common earlier p
    firstSection secondSection k hk neighborSection hVa hVc hVd hH hforward hW, ?_⟩
  exact Noncentrality.seed_commutator_not_le_Z source common earlier p hVa hVd
    hleft hright hW (seedSectionOfPullback k hk neighborSection)

/-- Apply both proved local calculations to the literal LocalBounds consumer.
This proves both equalities in (4.5.5) from the allowed preceding clauses
and actual marked sections, with no additional geometric premise. -/
theorem commutator_layers [Finite M]
    (source : LocalSource L R) (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (firstSection : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (secondSection : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true)
    (k : FreeAmalgam R) (hk : act R k (alpha R) = p.walk.getVert 6)
    (neighborSection : MarkedPairSection source common
      (rightConjugate (hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)) k⁻¹)
      (rightConjugate (hatV R (p.walk.getVert 6) (p.walk.getVert 8)) k⁻¹) true)
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hVd : hatV R (p.walk.getVert 8) (p.walk.getVert 10) =
      Vcirc R (p.walk.getVert 8) ⊔ Z R (p.walk.getVert 8))
    (hH : Nat.card (H R (alpha R)) = 4)
    (hforward : ⁅hatV R (p.walk.getVert 6) (p.walk.getVert 8),
      Q R (p.walk.getVert 8)⁆ ≤ Z R (p.walk.getVert 8))
    (hleft : (hatW R (p.walk.getVert 2) (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 6) : Set (FreeAmalgam R)) = (Q R (p.walk.getVert 5) : Set (FreeAmalgam R)))
    (hright : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) : Set (FreeAmalgam R)) *
      (Q R (p.walk.getVert 8) : Set (FreeAmalgam R)) = (Q R (p.walk.getVert 7) : Set (FreeAmalgam R)))
    (hW : ⁅hatW R (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      Q R (p.walk.getVert 6)⁆ ≤ Z R (p.walk.getVert 6)) :
    ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10), Q R (alpha R)⁆ ⊔
      Z R (alpha R) = hatV R (alpha R) (p.walk.getVert 6) ∧
    ⁅hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10),
      hatSix R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) (p.walk.getVert 10)⁆ ⊔
      Z R (alpha R) = hatV R (alpha R) (p.walk.getVert 6) := by
  obtain ⟨hpairs, hnon⟩ := local_calculations source common earlier p
    firstSection secondSection k hk neighborSection hVa hVc hVd hH hforward hleft hright hW
  exact SourcePath.commutator_layers_of_pair_bounds source common earlier p
    hVa hVd hleft hright hW firstSection hpairs hnon

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases
