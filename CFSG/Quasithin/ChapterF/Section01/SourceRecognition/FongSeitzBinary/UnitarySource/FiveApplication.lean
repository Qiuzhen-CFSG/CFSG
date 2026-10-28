module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FiveCoefficients
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FiveCenter
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FiveExceptional
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.SourceCollection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RootCoordinates.SourceProducts

/-!
# The U₅ coefficient calculations on the original split quotient

The quotient is literally (generated L S)/Q.D, with its original Q.q map.
Identification of the four ranges with the ordered split roots proves
U-generation. The ordinary Cartan action then determines the unknown
Hermitian correction and discharges both premises of five_originalS_collected.
The acting elements lie in the actual B intersect N throughout.

Two further applications retain the exceptional branch: the central
parameter crossing follows from the nonabelian Hermitian law, and solving
(8.35) gives the five selected unit-parameter crossings. The latter uses
conjugated correction coordinates explicitly; the producer must derive the
five equations in these coordinates before it can apply the result.

These are source-reconstruction steps, not recognition of the original
quotient. Construction of the charts, the other crossing laws, their ordered
placements and torus actors, and derivation of the exceptional system from
Fong--Seitz I §§4,6 and II §8C remain with the same source owner. Full Weyl
laws, whole-group generation and the endpoint markings also remain.
Source: Fong--Seitz II pp.207--210, (8.24)--(8.35); DGS Theorem D, p.224.
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
variable (Q : SourceQuotient L S) (split : SplitData Q.tits)

theorem positive_generated_eq_unipotent
    {RA RD RC RB : Type*} [Group RA] [Group RD] [Group RC] [Group RB]
    (r : PositiveMaps ((generated L S) ⧸ Q.D) RA RD RC RB) (b : Bool)
    (hroots : orderedRoots Q split b (rotationOrder Q) =
      [r.A.range,r.D.range,r.C.range,r.B.range]) : r.generated = split.U := by
  have hmem (K : Subgroup ((generated L S) ⧸ Q.D))
      (hK : K ∈ [r.A.range,r.D.range,r.C.range,r.B.range]) : K ≤ r.generated := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hK
    rcases hK with rfl | rfl | rfl | rfl <;> rintro z ⟨a,rfl⟩
    · exact subset_closure (Or.inl (Or.inl (Or.inl ⟨a,rfl⟩)))
    · exact subset_closure (Or.inl (Or.inl (Or.inr ⟨a,rfl⟩)))
    · exact subset_closure (Or.inl (Or.inr ⟨a,rfl⟩))
    · exact subset_closure (Or.inr ⟨a,rfl⟩)
  have hle (K : Subgroup ((generated L S) ⧸ Q.D))
      (hK : K ∈ [r.A.range,r.D.range,r.C.range,r.B.range]) : K ≤ split.U := by
    rw [← hroots] at hK
    have he := orderedRoots_le Q split b (rotationOrder Q) le_rfl K hK
    simpa only [alternatingWord_longest, longest_inv, rootIntersection_longest] using he
  apply le_antisymm
  · apply (closure_le _).2
    rintro z (((ha | hd) | hc) | hb)
    · exact hle r.A.range (by simp) ha
    · exact hle r.D.range (by simp) hd
    · exact hle r.C.range (by simp) hc
    · exact hle r.B.range (by simp) hb
  · intro z hz
    have hp : z ∈ Set.range (rootProduct (orderedRoots Q split b (rotationOrder Q))) := by
      rw [rootProduct_range, unipotent_ordered_product]
      exact hz
    obtain ⟨p,rfl⟩ := hp
    exact rootProduct_mem _ r.generated (fun K hK => hmem K (hroots ▸ hK)) p

variable (J : HermitianForm 5 E)
variable (r : PositiveMaps ((generated L S) ⧸ Q.D) (Multiplicative E)
  (FivePositive.Parameter J) (Multiplicative E) (FivePositive.Parameter J))
variable (T : FivePositive.Parameter J → E → FivePositive.Parameter J)

theorem five_originalS_collected_of_torus
    (h : HypothesisF11 L S) (b : Bool)
    (hroots : orderedRoots Q split b (rotationOrder Q) =
      [r.A.range,r.D.range,r.C.range,r.B.range])
    (hD : Function.Injective r.D)
    (hfst : ∀ (p : FivePositive.Parameter J) (a : E), (T p a).val.1 = a*p.val.1)
    (hAD : ∀ a d, Commute (r.A a) (r.D d))
    (hCD : ∀ c d, Commute (r.C c) (r.D d))
    (hBC : ∀ p c, Commute (r.B p) (r.C c))
    (hCA : ∀ a c, r.C (Multiplicative.ofAdd c)*r.A (Multiplicative.ofAdd a) =
      r.A (Multiplicative.ofAdd a)*r.D (FivePositive.traceParameter J a c)*
        r.C (Multiplicative.ofAdd c))
    (hBD : ∀ p q, r.B p*r.D q = r.D q*
      r.C (Multiplicative.ofAdd (q.val.1*J.conj p.val.1))*r.B p)
    (hBA : ∀ a p, r.B p*r.A (Multiplicative.ofAdd a) =
      r.A (Multiplicative.ofAdd a)*r.D (T p a)*
        r.C (Multiplicative.ofAdd (a*J.conj p.val.2))*r.B p)
    (θ : E) (hθ : θ+J.conj θ ≠ 0)
    (torus : E → ↥(Q.tits.B ⊓ Q.tits.N))
    (hA : ∀ t ∈ ({θ,J.conj θ,θ+J.conj θ} : Set E), ∀ a,
      (torus t : (generated L S) ⧸ Q.D)*r.A (Multiplicative.ofAdd a)*(torus t)⁻¹ =
        r.A (Multiplicative.ofAdd (t*a)))
    (hB : ∀ t ∈ ({θ,J.conj θ,θ+J.conj θ} : Set E), ∀ p,
      (torus t : (generated L S) ⧸ Q.D)*r.B p*(torus t)⁻¹ = r.B p)
    (hC : ∀ t ∈ ({θ,J.conj θ,θ+J.conj θ} : Set E), ∀ c,
      (torus t : (generated L S) ⧸ Q.D)*r.C (Multiplicative.ofAdd c)*(torus t)⁻¹ =
        r.C (Multiplicative.ofAdd (t*c)))
    (hDt : ∀ t ∈ ({θ,J.conj θ,θ+J.conj θ} : Set E), ∀ p,
      (torus t : (generated L S) ⧸ Q.D)*r.D p*(torus t)⁻¹ =
        r.D (FivePositive.normParameter J t p))
    (x : (generated L S) ⧸ Q.D)
    (hx : x ∈ (S.subgroupOf (generated L S)).map Q.q) :
    ∃ a d c p, x = r.word a d c p := by
  have heq := FiveCoefficients.relations_of_torus J r T hAD hCD hCA hBA hD hfst
    hBC hBD θ hθ (fun t => MulAut.conj (torus t : (generated L S) ⧸ Q.D)) hA hB hC hDt
  exact UnitaryPresentation.five_originalS_collected h Q split J r heq
    (positive_generated_eq_unipotent Q split r b hroots).ge x hx

theorem five_original_center_crossing
    (hne : ∃ t : E, J.conj t ≠ t)
    (hD : Function.Injective r.D)
    (hfst : ∀ (p : FivePositive.Parameter J) (a : E), (T p a).val.1=a*p.val.1)
    (hCD : ∀ c d, Commute (r.C c) (r.D d))
    (hBC : ∀ p c, Commute (r.B p) (r.C c))
    (hBD : ∀ p q, r.B p*r.D q = r.D q*
      r.C (Multiplicative.ofAdd (q.val.1*J.conj p.val.1))*r.B p)
    (hBA : ∀ a p, r.B p*r.A (Multiplicative.ofAdd a) =
      r.A (Multiplicative.ofAdd a)*r.D (T p a)*
        r.C (Multiplicative.ofAdd (a*J.conj p.val.2))*r.B p)
    (p : FivePositive.Parameter J) (hp : p.val.1=0) (a : E) :
    r.B p*r.A (Multiplicative.ofAdd a) =
      r.A (Multiplicative.ofAdd a)*r.D (FivePositive.normParameter J a p)*
        r.C (Multiplicative.ofAdd (a*J.conj p.val.2))*r.B p := by
  obtain ⟨κ,hκ⟩ := Theory.SpecificGroups.UnitaryFive.LineCore.exists_trace_one J hne
  rw [hBA, FiveCenter.correction_on_center J r T κ hκ hD hfst hCD hBC hBD hBA p hp a]

theorem five_exceptional_unit_crossings
    (hfst : ∀ (p : FivePositive.Parameter J) (a : E), (T p a).val.1=a*p.val.1)
    (hBA : ∀ a p, r.B p*r.A (Multiplicative.ofAdd a) =
      r.A (Multiplicative.ofAdd a)*r.D (T p a)*
        r.C (Multiplicative.ofAdd (a*J.conj p.val.2))*r.B p)
    (ω θ : E) (hω : ω^2=ω+1) (hθ : θ^2=θ+ω) (hbarθ : J.conj θ=θ+1)
    (p : Fin 5 → FivePositive.Parameter J) (hp : ∀ i, (p i).val.2=θ)
    (h0 : J.conj (T (p 0) 1).val.2+J.conj (T (p 1) 1).val.2+
      ω*J.conj (T (p 3) 1).val.2=(ω*θ)^4)
    (h1 : J.conj (T (p 0) 1).val.2+ω^2*J.conj (T (p 1) 1).val.2+
      J.conj (T (p 2) 1).val.2=(ω*θ)^3+1)
    (h2 : J.conj (T (p 0) 1).val.2+J.conj (T (p 3) 1).val.2+
      ω^2*J.conj (T (p 4) 1).val.2=(ω*θ)^2+ω)
    (h3 : J.conj (T (p 0) 1).val.2+ω^2*J.conj (T (p 1) 1).val.2+
      ω^2*J.conj (T (p 4) 1).val.2=θ^4)
    (h4 : J.conj (T (p 0) 1).val.2+ω^2*J.conj (T (p 2) 1).val.2+
      J.conj (T (p 4) 1).val.2=ω^2*θ^4) (i : Fin 5) :
    r.B (p i)*r.A (Multiplicative.ofAdd (1:E)) =
      r.A (Multiplicative.ofAdd (1:E))*r.D (p i)*
        r.C (Multiplicative.ofAdd (J.conj θ))*r.B (p i) := by
  have hx := FiveExceptional.system_solution ω θ hω hθ
    (fun j => J.conj (T (p j) 1).val.2) h0 h1 h2 h3 h4 i
  have hc : (T (p i) 1).val.2=θ := by
    have he := congrArg J.conj hx
    simpa only [J.conj_involutive (T (p i) 1).val.2, map_add, map_one,
      hbarθ, add_assoc, CharTwo.add_self_eq_zero, add_zero] using he
  have ht : T (p i) 1=p i := by
    apply Subtype.ext
    exact Prod.ext (by simpa only [one_mul] using hfst (p i) 1) (hc.trans (hp i).symm)
  rw [hBA,ht,hp,one_mul]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
