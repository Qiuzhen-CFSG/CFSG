module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.Reduction
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Interfaces
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Endpoints
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.OrbitCalculation.FusionCount
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.OrbitCalculation.ClassMatching

/-!
# The third core orbit and the nine-point middle fusion count

The third core orbit is proved from the original centralizer hypotheses
and the two actual endpoint intersections. The split endpoint normalizer
supplies a class-preserving matching between the involutions of A and Q
outside E. The explicit fusion union gives six fused involutions there;
the three nonidentity elements of A ∩ E give the total of nine.

The final application discharges both the orbit and class-matching inputs.
The local sixteen and the independent normalizer-image conclusions remain
explicit, with their final source assembly owned by the middle-normalizer
producer. No ambient recognition or D-system is assumed.
Source: Aschbacher, “A 2-local characterization of M12”, Lemmas 2.3, 2.6,
and 3.1, printed pp.33–37,
https://authors.library.caltech.edu/records/m3wrn-5w840/files/ASCijm03.pdf.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration
variable {G : Type*} [Group G] [Finite G] {z g y : G}

/-- The third orbit under the original arbitrary-group inputs. The extra
branch and splitting assumptions are unnecessary once the actual local
intersection data and their overlap are supplied. -/
theorem thirdCoreOrbit_of_source (h : Hypotheses z)
    (local_intersections : ∀ r : G, r * z * r⁻¹ ∈ coreInG z → r * z * r⁻¹ ≠ z →
      IntersectionData z r)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (hyQ : y * z * y⁻¹ ∈ coreInG z) (hy : y * z * y⁻¹ ≠ z)
    (hinter : coreIntersection z g ⊓ coreIntersection z y = zpowers z) :
    ThirdCoreOrbit z g y :=
  OrbitCalculation.thirdCoreOrbit h (local_intersections g hgQ hg)
    (local_intersections y hyQ hy) hinter

/-- The marked nine-point fusion count, with the local class matching proved
from the actual endpoint splitting. The local sixteen and fusion union are
the independent inputs of this counting result. -/
theorem OrbitCalculation.middleFusion_card_of_point_split (h : Hypotheses z)
    (d : IntersectionData z g) (dy : IntersectionData z y)
    (hinter : coreIntersection z g ⊓ coreIntersection z y = zpowers z)
    (m : MiddleLocalData z)
    (point_split : ∃ K : Subgroup (normalizer (coreIntersection z g : Set G)),
      IsComplement' ((coreIntersection z g).subgroupOf
        (normalizer (coreIntersection z g : Set G))) K)
    (fusion_union : ∀ x : G, (x ∈ coreInG z ∧ IsConj z x) ↔
      (x ∈ coreIntersection z g ∨ x ∈ coreIntersection z y) ∧ x ≠ 1) :
    Nat.card (MiddleFusion z m.A) = 9 :=
  OrbitCalculation.middleFusion_card_of_matching h d dy hinter m
    (OrbitCalculation.middleClassMatching_of_point_split h d m point_split) fusion_union

/-- Apply the proved orbit and counting arguments to the actual middle data.
The class matching and normalizer-image conclusions remain explicit inputs
whose source producers are independent of this implication. -/
theorem middle_of_matching_and_normalizer (h : Hypotheses z)
    (d : IntersectionData z g) (dy : IntersectionData z y)
    (hinter : coreIntersection z g ⊓ coreIntersection z y = zpowers z)
    (m : MiddleLocalData z) (matching : OrbitCalculation.MiddleClassMatching z g m.A)
    (hsixty : Nat.card (normalizer (m.A : Set G) ⧸
      m.A.subgroupOf (normalizer (m.A : Set G))) ≠ 60)
    (hquot : Nat.card (normalizer (m.A : Set G) ⧸
      m.A.subgroupOf (normalizer (m.A : Set G))) = 36 → Nonempty
      ((normalizer (m.A : Set G) ⧸ m.A.subgroupOf (normalizer (m.A : Set G))) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    Nonempty (MiddleData z g y) := by
  have hfusion := fusion_union_of_third_orbit h d dy m
    (OrbitCalculation.thirdCoreOrbit h d dy hinter)
    (m.missing_of_quotient_card_ne_sixty h hsixty)
  have hc := m.normalizer_quotient_card h
  rw [OrbitCalculation.middleFusion_card_of_matching h d dy hinter m matching hfusion] at hc
  exact middle_of_fusion_and_quotient m hfusion (hquot hc)

/-- Apply the completed orbit and counting calculations to the middle-normalizer
consumer. Only the separately produced local sixteen and normalizer-image
conclusions remain to be supplied by the source assembly. -/
theorem middle_of_point_split_and_normalizer (h : Hypotheses z)
    (d : IntersectionData z g) (dy : IntersectionData z y)
    (hinter : coreIntersection z g ⊓ coreIntersection z y = zpowers z)
    (m : MiddleLocalData z)
    (point_split : ∃ K : Subgroup (normalizer (coreIntersection z g : Set G)),
      IsComplement' ((coreIntersection z g).subgroupOf
        (normalizer (coreIntersection z g : Set G))) K)
    (hsixty : Nat.card (normalizer (m.A : Set G) ⧸
      m.A.subgroupOf (normalizer (m.A : Set G))) ≠ 60)
    (hquot : Nat.card (normalizer (m.A : Set G) ⧸
      m.A.subgroupOf (normalizer (m.A : Set G))) = 36 → Nonempty
      ((normalizer (m.A : Set G) ⧸ m.A.subgroupOf (normalizer (m.A : Set G))) ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))) :
    Nonempty (MiddleData z g y) :=
  middle_of_matching_and_normalizer h d dy hinter m
    (OrbitCalculation.middleClassMatching_of_point_split h d m point_split) hsixty hquot

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration
end
