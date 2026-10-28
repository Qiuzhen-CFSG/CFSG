module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Interfaces
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Endpoints
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.Reduction
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.Construction
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.NormalizerImage
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NonnormalRecognition.Geometry.Configuration.Middle.OrbitCalculation

/-!
# The source 3.1 middle normalizer and exact core fusion union

The split point normalizer constructs the elementary sixteen and its intrinsic
Sylow geometry. Fusion control and the exclusion of a quotient of order sixty
give an involution outside the class of z. The third core orbit then yields the
exact endpoint fusion union. The marked nine-point count forces the normalizer
quotient to have order thirty-six, where the finite action calculation identifies
the literal quotient with S3 × S3.

`middle_of_source` discharges all three mathematical producers under the original
inputs and the explicit endpoint-complement premise. The enclosing configuration
assembly retains the construction of that complement and of the second endpoint.
The earlier conditional assembly interface is preserved.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), Lemma 3.1, printed pp.36–37,
https://authors.library.caltech.edu/records/m3wrn-5w840/files/ASCijm03.pdf.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration
variable {G : Type*} [Group G] [Finite G] {z g y : G}

/-- Apply the independent local, orbit and normalizer producers. Each premise
remains an obligation of the source-theorem assembly in this module. -/
theorem middle_of_local_producers (h : Hypotheses z)
    (d : IntersectionData z g) (dy : IntersectionData z y)
    (local_data : Nonempty (MiddleLocalData z))
    (horbits : ThirdCoreOrbit z g y)
    (normalizer_results : ∀ m : MiddleLocalData z,
      (Nat.card (normalizer (m.A : Set G) ⧸
        m.A.subgroupOf (normalizer (m.A : Set G))) ≠ 60) ∧
      (Nat.card (normalizer (m.A : Set G) ⧸
        m.A.subgroupOf (normalizer (m.A : Set G))) = 36 → Nonempty
        ((normalizer (m.A : Set G) ⧸ m.A.subgroupOf (normalizer (m.A : Set G))) ≃*
          (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))))
    (count : ∀ m : MiddleLocalData z,
      (∀ x : G, (x ∈ coreInG z ∧ IsConj z x) ↔
        (x ∈ coreIntersection z g ∨ x ∈ coreIntersection z y) ∧ x ≠ 1) →
      Nat.card (MiddleFusion z m.A) = 9) : Nonempty (MiddleData z g y) := by
  obtain ⟨m⟩ := local_data
  obtain ⟨hsixty, hquot⟩ := normalizer_results m
  have hmissing := m.missing_of_quotient_card_ne_sixty h hsixty
  have hfusion := fusion_union_of_third_orbit h d dy m horbits hmissing
  have hc := m.normalizer_quotient_card h
  rw [count m hfusion] at hc
  exact middle_of_fusion_and_quotient m hfusion (hquot hc)

/-- Construct the published middle data for the two actual endpoints. The local
sixteen, third core orbit, finite normalizer calculations and nine-point fusion
count are all proved; only the endpoint complement remains an explicit input. -/
theorem middle_of_point_split (h : Hypotheses z)
    (d : IntersectionData z g) (dy : IntersectionData z y)
    (hinter : coreIntersection z g ⊓ coreIntersection z y = zpowers z)
    (point_split : ∃ K : Subgroup (normalizer (coreIntersection z g : Set G)),
      IsComplement' ((coreIntersection z g).subgroupOf
        (normalizer (coreIntersection z g : Set G))) K) :
    Nonempty (MiddleData z g y) := by
  apply middle_of_local_producers h d dy
    (middle_local_data_of_point_split h d point_split)
    (OrbitCalculation.thirdCoreOrbit h d dy hinter)
    (fun m => m.normalizer_results h)
  intro m hfusion
  exact OrbitCalculation.middleFusion_card_of_point_split h d dy hinter m point_split hfusion

/-- The middle-normalizer producer with the original source-branch inputs. The
nonnormality and nonsaturation hypotheses belong to the earlier endpoint and
splitting arguments; once those outputs are supplied, the preceding theorem
constructs every field of `MiddleData` without further premises. -/
theorem middle_of_source (h : Hypotheses z) (_hn : QuaternionSubgroupsNonnormal z)
    (local_intersections : ∀ r : G, r * z * r⁻¹ ∈ coreInG z → r * z * r⁻¹ ≠ z →
      IntersectionData z r)
    (hgQ : g * z * g⁻¹ ∈ coreInG z) (hg : g * z * g⁻¹ ≠ z)
    (_hs : ¬ FusionSaturated z g)
    (hyQ : y * z * y⁻¹ ∈ coreInG z) (hy : y * z * y⁻¹ ≠ z)
    (hinter : coreIntersection z g ⊓ coreIntersection z y = zpowers z)
    (point_split : ∃ K : Subgroup (normalizer (coreIntersection z g : Set G)),
      IsComplement' ((coreIntersection z g).subgroupOf
        (normalizer (coreIntersection z g : Set G))) K) :
    Nonempty (MiddleData z g y) :=
  middle_of_point_split h (local_intersections g hgQ hg)
    (local_intersections y hyQ hy) hinter point_split

end CFSG.Quasithin.Extraspecial32.NonnormalRecognition.Configuration

end
