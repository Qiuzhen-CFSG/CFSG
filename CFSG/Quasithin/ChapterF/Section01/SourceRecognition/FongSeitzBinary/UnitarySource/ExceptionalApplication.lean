module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FiveMixedRigidity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.FiveApplication

/-!
# The exceptional U₅ positive relations on the original quotient

The matrix field has order sixteen and its involution is the fourth-power
map, so the fixed-field parameter is four. Constructing the required scalar
and using the actual rank-one torus in B ∩ N determines the full unknown
Hermitian correction. The original five-equation premise is absent.
The ordered-root identification then gives U-generation and applies
five_originalS_collected to the literal Q.q-image of the same original S.
The rank-one variant derives the C-root torus action from the B--D
crossing, retaining only the three independent A, B and D action premises.

The same source owner still constructs the root charts, their preceding
crossings and the rank-one torus action from the original (6A)(c) module
realizations. Full Weyl laws and markings also remain. No model or field
identification for the original quotient is asserted here.
Source: Fong--Seitz II (8.20), (8.24)--(8.35), pp.205--210;
DGS Theorem D, printed p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {E : Type*} [Field E] [CharP E 2]
variable (Q : SourceQuotient L S) (J : HermitianForm 5 E)
variable (r : PositiveMaps ((generated L S) ⧸ Q.D) (Multiplicative E)
  (FivePositive.Parameter J) (Multiplicative E) (FivePositive.Parameter J))
variable (T : FivePositive.Parameter J → E → FivePositive.Parameter J)
variable (hD : Function.Injective r.D)
variable (hfst : ∀ (p : FivePositive.Parameter J) (a : E), (T p a).val.1=a*p.val.1)
variable (hAD : ∀ a d, Commute (r.A a) (r.D d))
variable (hCD : ∀ c d, Commute (r.C c) (r.D d))
variable (hBC : ∀ p c, Commute (r.B p) (r.C c))
variable (hCA : ∀ a c, r.C (Multiplicative.ofAdd c)*r.A (Multiplicative.ofAdd a) =
  r.A (Multiplicative.ofAdd a)*r.D (FivePositive.traceParameter J a c)*r.C (Multiplicative.ofAdd c))
variable (hBD : ∀ p q, r.B p*r.D q = r.D q*
  r.C (Multiplicative.ofAdd (q.val.1*J.conj p.val.1))*r.B p)
variable (hBA : ∀ a p, r.B p*r.A (Multiplicative.ofAdd a) =
  r.A (Multiplicative.ofAdd a)*r.D (T p a)*
    r.C (Multiplicative.ofAdd (a*J.conj p.val.2))*r.B p)
variable (hcard : Nat.card E=16) (hconj : ∀ x : E, J.conj x=x^4)
variable (torus : Eˣ →* ↥(Q.tits.B ⊓ Q.tits.N))
variable (hA : ∀ (t : Eˣ) a,
  (torus t : (generated L S) ⧸ Q.D)*r.A (Multiplicative.ofAdd a)*(torus t)⁻¹ =
    r.A (Multiplicative.ofAdd ((t:E)^2*a)))
variable (hB : ∀ (t : Eˣ) p,
  (torus t : (generated L S) ⧸ Q.D)*r.B (FivePositive.normParameter J (t:E) p)*(torus t)⁻¹ =
    r.B p)
variable (hC : ∀ (t : Eˣ) c,
  (torus t : (generated L S) ⧸ Q.D)*r.C (Multiplicative.ofAdd c)*(torus t)⁻¹ =
    r.C (Multiplicative.ofAdd ((t:E)/(J.conj (t:E))*c)))
variable (hDt : ∀ (t : Eˣ) p,
  (torus t : (generated L S) ⧸ Q.D)*r.D p*(torus t)⁻¹ =
    r.D (FivePositive.normParameter J (t:E) p))

include hD hfst hAD hCD hBC hCA hBD hBA hcard hconj hA hB hC hDt in
/-- The full positive relations at q=4 use the source torus and contain no
assumed exceptional coefficient equations or selected scalar. -/
theorem five_relations_field_sixteen : FivePositive.Relations J r := by
  obtain ⟨θ,hθ⟩ := FiveMixedRigidity.exists_exceptional_scalar hcard
  have hθne : θ ≠ 0 := by
    intro he
    rw [he] at hθ
    simp at hθ
  let u : Eˣ := Units.mk0 θ hθne
  exact FiveMixedRigidity.relations_of_exceptional_torus J r T hD hfst hAD hCD hBC hCA hBD hBA
    θ hθ ((hconj θ).trans hθ) (MulAut.conj (torus u : (generated L S) ⧸ Q.D))
    (hA u) (hB u) (hC u) (hDt u)

include hD hfst hAD hCD hBC hCA hBD hBA hcard hconj hA hB hC hDt in
/-- Apply the recovered exceptional coefficient and actual ordered-root
generation to the original S image under the unchanged quotient map. -/
theorem five_originalS_collected_field_sixteen
    (h : HypothesisF11 L S) (split : SplitData Q.tits) (b : Bool)
    (hroots : orderedRoots Q split b (rotationOrder Q) =
      [r.A.range,r.D.range,r.C.range,r.B.range])
    (x : (generated L S) ⧸ Q.D) (hx : x ∈ (S.subgroupOf (generated L S)).map Q.q) :
    ∃ a d c p, x=r.word a d c p :=
  UnitaryPresentation.five_originalS_collected h Q split J r
    (five_relations_field_sixteen Q J r T hD hfst hAD hCD hBC hCA hBD hBA
      hcard hconj torus hA hB hC hDt)
    (positive_generated_eq_unipotent Q split r b hroots).ge x hx

include hD hfst hAD hCD hBC hCA hBD hBA hcard hconj hA hB hDt in
/-- The same exceptional relations with the C-root torus action proved
from the existing crossing, rather than supplied as another source premise. -/
theorem five_relations_field_sixteen_from_rankOne_torus :
    FivePositive.Relations J r := by
  obtain ⟨θ,hθ⟩ := FiveMixedRigidity.exists_exceptional_scalar hcard
  have hθne : θ ≠ 0 := by
    intro he
    rw [he] at hθ
    simp at hθ
  let u : Eˣ := Units.mk0 θ hθne
  exact FiveMixedRigidity.relations_of_exceptional_rankOne_torus
    J r T hD hfst hAD hCD hBC hCA hBD hBA θ hθ ((hconj θ).trans hθ)
    (MulAut.conj (torus u : (generated L S) ⧸ Q.D)) (hA u) (hB u) (hDt u)

include hD hfst hAD hCD hBC hCA hBD hBA hcard hconj hA hB hDt in
/-- The original Sylow-image collector with both the exceptional equations
and the formerly separate C-root torus action discharged. -/
theorem five_originalS_collected_field_sixteen_from_rankOne_torus
    (h : HypothesisF11 L S) (split : SplitData Q.tits) (b : Bool)
    (hroots : orderedRoots Q split b (rotationOrder Q) =
      [r.A.range,r.D.range,r.C.range,r.B.range])
    (x : (generated L S) ⧸ Q.D) (hx : x ∈ (S.subgroupOf (generated L S)).map Q.q) :
    ∃ a d c p, x=r.word a d c p :=
  UnitaryPresentation.five_originalS_collected h Q split J r
    (five_relations_field_sixteen_from_rankOne_torus Q J r T
      hD hfst hAD hCD hBC hCA hBD hBA hcard hconj torus hA hB hDt)
    (positive_generated_eq_unipotent Q split r b hroots).ge x hx

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
