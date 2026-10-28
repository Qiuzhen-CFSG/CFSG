module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.Normalizer

/-!+# Corrected source contracts for MS93 (4.5.2)--(4.5.3)

The actor is the relative normalizer from printed p.881. The join in the
generation clause is explicitly a subgroup join before coercion to a set.
The reflected normality clause retains the vertices of the same supplied
path. These contracts are separate from the preserved legacy OrbitFacts.

The normalizer family is constructed in Generation. The full orbit record
also requires the three conclusions of (4.5.3); its declaration alone does
not assert those conclusions or supply a constructor from Earlier.

Source: Meierfrankenfeld--Stellmacher (1993), printed pp.881, 897--898.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source
variable {M : Type*} [Group M] (R : Subgroup M)

/-- The two clauses of (4.5.2), including the same-path reflected instance. -/
structure SourceNormalizerFacts {a : Vertex R} (p : SourcePath R a) where
  Z_le_pair : Z R a ≤ relativeNormalizer R (p.walk.getVert 6) (p.walk.getVert 5)
  Z_normal_pair : ((Z R a).subgroupOf
    (relativeNormalizer R (p.walk.getVert 6) (p.walk.getVert 5))).Normal
  local_generation :
    (((relativeNormalizer R a (p.walk.getVert 3) ⊔ Z R (p.walk.getVert 12) :
      Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) * (C R a : Set (FreeAmalgam R))) =
        (stabilizer R a : Set (FreeAmalgam R))
  reflected_Z_le_pair : Z R (p.walk.getVert 8) ≤
    relativeNormalizer R (p.walk.getVert 6) (p.walk.getVert 7)
  reflected_Z_normal_pair : ((Z R (p.walk.getVert 8)).subgroupOf
    (relativeNormalizer R (p.walk.getVert 6) (p.walk.getVert 7))).Normal

/-- The complete corrected source output. Its hat-layer fields remain
separate proof obligations until the (4.5.3) calculation is supplied. -/
structure SourceOrbitFacts {a : Vertex R} (p : SourcePath R a)
    extends SourceNormalizerFacts R p where
  hatV_eq : hatV R a (p.walk.getVert 6) = Vcirc R a ⊔ Z R a
  hatV_product : (hatV R a (p.walk.getVert 6) : Set (FreeAmalgam R)) =
    (Vcirc R a : Set (FreeAmalgam R)) * (Z R a : Set (FreeAmalgam R))
  hatV_commutator : ⁅hatV R a (p.walk.getVert 6), Q R (p.walk.getVert 6)⁆ ≤
    Z R (p.walk.getVert 6)
  hatW_commutator : ⁅hatW R a (p.walk.getVert 6) (p.walk.getVert 8), Q R a⁆ ≤ Z R a

/-- The first identity of (4.5.3) at the six defined forward hat layers.
The reversed identity follows from the turn at the same vertex. This is
a source obligation, not an added hypothesis of the final assembly. -/
structure HatIdentitiesOnPath {a : Vertex R} (p : SourcePath R a) where
  forward : ∀ i : ℕ, Even i → 2 ≤ i → i ≤ 12 →
    hatV R (p.walk.getVert i) (p.walk.getVert (i + 2)) =
      Vcirc R (p.walk.getVert i) ⊔ Z R (p.walk.getVert i)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source
