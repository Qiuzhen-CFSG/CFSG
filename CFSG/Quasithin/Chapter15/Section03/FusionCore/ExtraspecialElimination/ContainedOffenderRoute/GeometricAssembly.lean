module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.EndpointConstruction
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.Inputs
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.Local
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.Consequences
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Constructing and placing offenders at compatible endpoints

The endpoints are literal conjugates of the local group, its two spans, and
its central line. `GeometricFamily` lists the earlier local and F.9 facts
needed on one finite family: the two section actions, 15.3.49(c), the
15.3.47 normalizer test, the F.9.13 edge and commutator bounds, the F.9.16
rank selection, and simultaneous F.9.17 reversal. In particular edge-core
data are available at every endpoint, including the endpoint subsequently
selected by symmetry. This is a conditional interface for those earlier
theorems; its inhabitance is not asserted here.

Cross-centralization and the proper action kernel are deductions. The rank
comparison constructs ordinary quadratic offenders, from which B.1.4(4)
selects a contained best offender. After reduction to H = LT and the strict
span, the same family constructs a strong endpoint, then a contained strong
best offender and its compatible conjugate in O₂(Y₀*T*). Neither selection
asserts that the whole endpoint is best.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.13–17,
printed pp.322–324; B.1.4(4), p.68; 15.3.49(f)–(h),(n), pp.1143–1144.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute

open Subgroup Representation.BinaryOffender ComponentReduction
open FactorGeneration FactorGeneration.ConjugatePlacement Geometry.Symmetry
open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- All four objects use the same actual conjugating element. -/
def spanEndpoint (H V ZS Z : Subgroup G) (g : G) : Endpoint G :=
  ⟨H.map (MulAut.conj g).toMonoidHom,
    localSpan (ZS.map (MulAut.conj g).toMonoidHom) (H.map (MulAut.conj g).toMonoidHom),
    localSpan (V.map (MulAut.conj g).toMonoidHom) (H.map (MulAut.conj g).toMonoidHom),
    Z.map (MulAut.conj g).toMonoidHom⟩

theorem spanEndpoint_eq_conjugate (H V ZS Z : Subgroup G) (g : G) :
    spanEndpoint H V ZS Z g =
      (Endpoint.mk H (localSpan ZS H) (localSpan V H) Z).conjugate g := by
  simp only [spanEndpoint, Endpoint.conjugate, map_conjugateSpanBy, localSpan]

instance spanEndpoint_elementary_small (H V ZS Z : Subgroup G) (g : G)
    [IsElementaryAbelian 2 (localSpan ZS H)] :
    IsElementaryAbelian 2 (spanEndpoint H V ZS Z g).U := by
  rw [spanEndpoint_eq_conjugate]
  exact IsElementaryAbelian.map _

instance spanEndpoint_elementary_large (H V ZS Z : Subgroup G) (g : G)
    [IsElementaryAbelian 2 (localSpan V H)] :
    IsElementaryAbelian 2 (spanEndpoint H V ZS Z g).V := by
  rw [spanEndpoint_eq_conjugate]
  exact IsElementaryAbelian.map _

/-- Exact local/geometry premises, before any offender is chosen. The
source owner must construct these from the earlier F.9 hypotheses. -/
structure GeometricFamily (ι : Type*) (Y T H V ZS Z : Subgroup G)
    [IsElementaryAbelian 2 (localSpan ZS H)]
    [IsElementaryAbelian 2 (localSpan V H)] where
  representative : ι → G
  opposite : ∀ i, SectionAction (spanEndpoint H V ZS Z (representative i)).K
    (spanEndpoint H V ZS Z (representative i)).U
    (spanEndpoint H V ZS Z (representative i)).Z
  centered : localSpan ZS H ≤
    (center (omegaOneAmbient (localTwoCore H))).map (omegaOneAmbient (localTwoCore H)).subtype
  opposite_centered : ∀ i, (spanEndpoint H V ZS Z (representative i)).U ≤
    (center (omegaOneAmbient (localTwoCore (spanEndpoint H V ZS Z (representative i)).K))).map
      (omegaOneAmbient (localTwoCore (spanEndpoint H V ZS Z (representative i)).K)).subtype
  normalizer_test : Geometry.ConjugateNormalizerTest V ZS
  reverse_le : ∀ i, localSpan V H ≤ (spanEndpoint H V ZS Z (representative i)).K
  commutator : ∀ i, ⁅localSpan V H, (spanEndpoint H V ZS Z (representative i)).V⁆ ≤
    localSpan V H ⊓ (spanEndpoint H V ZS Z (representative i)).V
  neighbor : ι → Vertex Y T H
  neighbor_type : ∀ i, (neighbor i).type = false
  incident : ∀ i, CosetGeometry.Incident (family Y T H) (base Y T H true) (neighbor i)
  edge_core : ∀ i, (spanEndpoint H V ZS Z (representative i)).V ≤
    (edgeGroup Y T H (base Y T H true) (neighbor i)).pCoreIn 2
  noncentral : ∀ i, ¬ ⁅(spanEndpoint H V ZS Z (representative i)).U, V⁆ ≤
    (spanEndpoint H V ZS Z (representative i)).Z
  selected : ∃ i,
    0 < Nat.log 2 ((sectionCentralizer (spanEndpoint H V ZS Z (representative i)).U
      (localSpan ZS H) Z).relIndex (spanEndpoint H V ZS Z (representative i)).U) ∧
    Nat.log 2 ((sectionCentralizer (localSpan ZS H)
      (spanEndpoint H V ZS Z (representative i)).U
      (spanEndpoint H V ZS Z (representative i)).Z).relIndex (localSpan ZS H)) ≤
    Nat.log 2 ((sectionCentralizer (spanEndpoint H V ZS Z (representative i)).U
      (localSpan ZS H) Z).relIndex (spanEndpoint H V ZS Z (representative i)).U)
  reversal : ∀ i,
    0 < Nat.log 2 ((sectionCentralizer (spanEndpoint H V ZS Z (representative i)).U
      (localSpan ZS H) Z).relIndex (spanEndpoint H V ZS Z (representative i)).U) →
    ∃ j, Reversal ⟨H, localSpan ZS H, localSpan V H, Z⟩
      (spanEndpoint H V ZS Z (representative i)) (spanEndpoint H V ZS Z (representative j))

namespace GeometricFamily
variable {ι : Type*} {Y T H V ZS Z : Subgroup G}
    [IsElementaryAbelian 2 (localSpan ZS H)] [IsElementaryAbelian 2 (localSpan V H)]
    (f : GeometricFamily ι Y T H V ZS Z)

abbrev endpoint (i : ι) : Endpoint G := spanEndpoint H V ZS Z (f.representative i)

include f

theorem small_le_large (hZS : ZS ≤ V) (i : ι) : (f.endpoint i).U ≤ (f.endpoint i).V :=
  conjugateSpanBy_mono (map_mono hZS) le_rfl

theorem endpoint_le (i : ι) : (f.endpoint i).V ≤ H := by
  have h := (f.edge_core i).trans ((pCoreIn_le 2 _).trans inf_le_left)
  simpa only [base, CosetGeometry.stabilizer_base, family, ↓reduceIte] using h

theorem small_commutator (hZS : ZS ≤ V) (i : ι) :
    ⁅localSpan ZS H, (f.endpoint i).V⁆ ≤ (f.endpoint i).V :=
  (commutator_mono (conjugateSpanBy_mono hZS le_rfl) le_rfl).trans
    ((f.commutator i).trans inf_le_right)

/-- Clause (f) is proved from the omega-center and normalizer facts. -/
theorem cross (action : SectionAction H (localSpan ZS H) Z) (i : ι) :
    sectionCentralizer (f.endpoint i).V (localSpan ZS H) Z ≤
        centralizer (localSpan V H : Set G) ∧
      sectionCentralizer (localSpan V H) (f.endpoint i).U (f.endpoint i).Z ≤
        centralizer ((f.endpoint i).V : Set G) := by
  let : IsElementaryAbelian 2 (localSpan
      (ZS.map (MulAut.conj (f.representative i)).toMonoidHom) (f.endpoint i).K) :=
    spanEndpoint_elementary_small H V ZS Z (f.representative i)
  let : IsElementaryAbelian 2 (localSpan
      (V.map (MulAut.conj (f.representative i)).toMonoidHom) (f.endpoint i).K) :=
    spanEndpoint_elementary_large H V ZS Z (f.representative i)
  exact Geometry.crossCentralizations V ZS Z H (f.endpoint i).K (f.representative i)
    action (f.opposite i) (f.endpoint_le i) (f.reverse_le i)
    f.centered (f.opposite_centered i) (f.commutator i) f.normalizer_test

/-- The same endpoints also satisfy the literal quotient-centralizer
equality and the strict kernel clause (g). -/
theorem centralizer_and_kernel (action : SectionAction H (localSpan ZS H) Z)
    (hZS : ZS ≤ V) (i : ι) :
    sectionCentralizer (localSpan V H) (f.endpoint i).U (f.endpoint i).Z =
        localSpan V H ⊓ centralizer ((f.endpoint i).U : Set G) ∧
      sectionCentralizer (f.endpoint i).U (localSpan ZS H) Z < (f.endpoint i).U :=
  Geometry.centralizer_equality_and_proper_kernel V ZS H (f.endpoint i).U
    (f.endpoint i).V Z (f.endpoint i).Z (f.small_le_large hZS i)
    (((f.small_le_large hZS i).trans (f.endpoint_le i)).trans action.normalizes_layer)
    (f.cross action i).2 (f.cross action i).1 (f.noncentral i)

/-- First construct an ordinary offender; then choose its best subgroup
and transport that subgroup along the endpoint's actual edge. -/
theorem exists_placed_best [Finite G]
    (action : SectionAction H (localSpan ZS H) Z) (Y0 : Subgroup G)
    (hZS : ZS ≤ V) (hHZ : H ≤ centralizer (Z : Set G))
    (hedge : H ⊓ (Y ⊔ T) = Y0 ⊔ T) :
    ∃ i, ∃ c : ContainedBest H (localSpan ZS H) Z (f.endpoint i).V action,
      ∃ h : H, (h : G)⁻¹ • f.neighbor i = base Y T H false ∧
        starImage H (c.conjugate h⁻¹).carrier ≤
          (starImage H Y0 ⊔ starImage H T).pCoreIn 2 := by
  obtain ⟨i, hi⟩ := f.selected
  have hn := ((conjugateSpanBy_mono hZS le_rfl).trans (f.reverse_le i)).trans
    (f.opposite i).normalizes_layer
  obtain ⟨_, _, _, hoff, _, hquad⟩ := Geometry.selected_rank_and_quadratic_offenders
    V ZS Z H (f.endpoint i).U (f.endpoint i).V (f.endpoint i).Z action hZS
    (f.small_le_large hZS i) (f.endpoint_le i) hHZ hn (f.cross action i).2
    (f.small_commutator hZS i) hi
  obtain ⟨c⟩ := exists_containedBest H (localSpan ZS H) Z (f.endpoint i).V action hoff hquad
  obtain ⟨h, he, _, hc⟩ := exists_placed_of_edgeCore Y Y0 T H (f.endpoint i).V
    (f.neighbor i) (f.neighbor_type i) (f.incident i) hedge (f.edge_core i)
  exact ⟨i, c, h, he, (c.conjugate h⁻¹).starImage_le hc⟩

/-- The edge marking is available at whichever endpoint symmetry selects.
The new best subgroup need not belong to the first offender's span. -/
theorem exists_placed_strong [Finite G] [Finite ι]
    (action : SectionAction H (localSpan ZS H) Z) (Y0 L : Subgroup G)
    (hZS : ZS ≤ V) (hHZ : H ≤ centralizer (Z : Set G))
    (hedge : H ⊓ (Y ⊔ T) = Y0 ⊔ T)
    (hgen : H = L ⊔ T) (hn : H ≤ normalizer (L : Set G)) (hT : IsPGroup 2 T)
    (hL : (L.subgroupOf H).IsCComponent)
    (hq : Theory.GroupTheory.IsQuasisimple (starImage H L))
    (hTV : T ≤ normalizer (V : Set G)) (hVH : localSpan V H ≤ H)
    (hproper : localSpan ZS H ⊔ V < localSpan V H) :
    ∃ i, IsStrongOffender action.representation (starImage H (f.endpoint i).V) ∧
      ∃ c : ContainedBest H (localSpan ZS H) Z (f.endpoint i).V action,
        IsStrongOffender action.representation (starImage H c.carrier) ∧
        ∃ h : H, (h : G)⁻¹ • f.neighbor i = base Y T H false ∧
          starImage H (c.conjugate h⁻¹).carrier ≤
            (starImage H Y0 ⊔ starImage H T).pCoreIn 2 ∧
          IsStrongOffender action.representation (starImage H (c.conjugate h⁻¹).carrier) := by
  obtain ⟨i, hi, c, hc⟩ := exists_strong_endpoint H L T V ZS Z f.endpoint action f.opposite
    hZS hHZ (f.small_le_large hZS) f.endpoint_le f.reverse_le
    (fun i => (f.cross action i).2) (f.small_commutator hZS) f.selected f.reversal
    hgen hn hT hL hq hTV hVH hproper
  obtain ⟨h, he, _, hcore⟩ := exists_placed_of_edgeCore Y Y0 T H (f.endpoint i).V
    (f.neighbor i) (f.neighbor_type i) (f.incident i) hedge (f.edge_core i)
  exact ⟨i, hi, c, hc, h, he, (c.conjugate h⁻¹).starImage_le hcore,
    c.conjugate_strong h⁻¹ hc⟩

end GeometricFamily
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute
