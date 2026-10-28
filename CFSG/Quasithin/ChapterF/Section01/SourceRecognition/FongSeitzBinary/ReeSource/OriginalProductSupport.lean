module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.ProductSupport
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalFrattiniRadical

/-!
# Original endpoint application of the two-root support obstruction

The marked equivalence carries Φ(O₂(P₂)) to the actual Frattini radical
on the source octagon. For an element whose image lies in
U₂^(s₁s₂) U₁^(s₂s₁s₂), the source product theorem forces square one and
places its image in Ω₁(U₂^(s₁s₂)) U₁^(s₂s₁s₂). The same assertion is
proved for [O₂(P₂),O₂(P₂)] using its inclusion in the Frattini subgroup,
without identifying those two subgroups.

Original local characteristic two supplies self-centralization. The
natural panel markings supply the adjacent-root commutation and exponent
two; common-field recognition supplies the numerical bound. Its earlier
odd-linear-degree premise remains explicit. All Suzuki parameters are
included. The generated-carrier variants retain the literal Q.q formula,
and the original ambient group need not be finite.

Source: Fong--Seitz I (1973), proof of (6H), printed p.52, the two-root
order-four obstruction preceding (6.4). These are actual original source
applications of that obstruction. The conjugated mixed-commutator placement,
remaining (6.4) argument, binary derived effectivity, positive-parameter
(6.1), both later nonzero-commutator cases, pairing/odd-degree discharge,
remaining (6H), Section 10 equations and final full-model marked comparison
remain in the same source-construction task.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits)
  (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (hcore : Q.tits.B.normalCore = ⊥)

include h hm hn ν hC μ hB hcore in
/-- The full two-root obstruction on the original endpoint Frattini core.
The original characteristic-two hypothesis supplies self-centralization;
actual panel markings supply commutation, exponent two and the common size. -/
theorem original_frattini_product_support
    (a : frattini (pCore 2 (parabolic L S 1)))
    (ha : endpointMap Q e 1 a.val.val ∈
      (rootAt Q split 1 (Q.simple 0*Q.simple 1) : Set (X ⧸ Q.D)) *
        (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) : Set (X ⧸ Q.D))) :
    a^2 = 1 ∧ endpointMap Q e 1 a.val.val ∈
      (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) : Set (X ⧸ Q.D)) *
        (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) : Set (X ⧸ Q.D)) := by
  let hVi := marked_suzuki_remainder_le_kernel Q split 1 m μ hB
  let b := originalPhiRadicalEquiv Q e split 1 hVi a
  have hb : endpointMap Q e 1 a.val.val ∈ (frattiniRadicalSection Q split 1 hVi).numerator :=
    b.property
  obtain ⟨hs,hp⟩ := source_frattini_product_support_of_odd_degree Q split
    (parabolic_core_selfCentralizing Q e h 1) hm n hn m ν T hC μ hB hcore _ hb ha
  refine ⟨?_,hp⟩
  apply (originalPhiRadicalEquiv Q e split 1 hVi).injective
  rw [map_pow,map_one]
  exact Subtype.ext hs

include h hm hn ν hC μ hB hcore in
/-- The identical support statement holds in the original derived two-core;
no equality between its derived and Frattini subgroups is assumed. -/
theorem original_derived_product_support
    (a : commutator (pCore 2 (parabolic L S 1)))
    (ha : endpointMap Q e 1 a.val.val ∈
      (rootAt Q split 1 (Q.simple 0*Q.simple 1) : Set (X ⧸ Q.D)) *
        (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) : Set (X ⧸ Q.D))) :
    a^2 = 1 ∧ endpointMap Q e 1 a.val.val ∈
      (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) : Set (X ⧸ Q.D)) *
        (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) : Set (X ⧸ Q.D)) := by
  let : Finite (pCore 2 (parabolic L S 1)) :=
    Finite.of_equiv (simpleRemainder Q split 1)
      (originalRadicalEquiv Q e split 1 (marked_suzuki_remainder_le_kernel Q split 1 m μ hB)).symm.toEquiv
  let : Fact (IsPGroup 2 (pCore 2 (parabolic L S 1))) := ⟨pCore_isPGroup⟩
  let b : frattini (pCore 2 (parabolic L S 1)) :=
    ⟨a.val,commutator_le_frattini_of_isPGroup (p := 2) a.property⟩
  obtain ⟨hs,hp⟩ := original_frattini_product_support Q e split h hm n hn m ν T hC μ hB hcore b ha
  refine ⟨Subtype.ext ?_,hp⟩
  exact congrArg (fun x : frattini (pCore 2 (parabolic L S 1)) => x.val) hs

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (h : HypothesisF11 L S) (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (hcore : Q.tits.B.normalCore = ⊥)

include h hm hn ν hC μ hB hcore in
/-- The two-root support estimate at the literal original quotient map. -/
theorem original_frattini_product_support_quotient
    (a : frattini (pCore 2 (parabolic L S 1)))
    (ha : Q.q ⟨a.val.val,parabolic_le_generated 1 a.val.val.property⟩ ∈
      (rootAt Q split 1 (Q.simple 0*Q.simple 1) : Set ((generated L S) ⧸ Q.D)) *
        (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) : Set ((generated L S) ⧸ Q.D))) :
    a^2 = 1 ∧ Q.q ⟨a.val.val,parabolic_le_generated 1 a.val.val.property⟩ ∈
      (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) : Set ((generated L S) ⧸ Q.D)) *
        (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) : Set ((generated L S) ⧸ Q.D)) := by
  have he := originalMarkedIso_right_apply Q a.val.val
  change MarkedLocal.endpointMap Q (originalMarkedIso Q) 1 a.val.val = _ at he
  rw [←he] at ha ⊢
  exact original_frattini_product_support Q (originalMarkedIso Q) split h hm n hn m ν T hC μ hB hcore a ha

include h hm hn ν hC μ hB hcore in
/-- The original derived-core version also retains the same literal quotient map. -/
theorem original_derived_product_support_quotient
    (a : commutator (pCore 2 (parabolic L S 1)))
    (ha : Q.q ⟨a.val.val,parabolic_le_generated 1 a.val.val.property⟩ ∈
      (rootAt Q split 1 (Q.simple 0*Q.simple 1) : Set ((generated L S) ⧸ Q.D)) *
        (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) : Set ((generated L S) ⧸ Q.D))) :
    a^2 = 1 ∧ Q.q ⟨a.val.val,parabolic_le_generated 1 a.val.val.property⟩ ∈
      (omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)) : Set ((generated L S) ⧸ Q.D)) *
        (rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1) : Set ((generated L S) ⧸ Q.D)) := by
  have he := originalMarkedIso_right_apply Q a.val.val
  change MarkedLocal.endpointMap Q (originalMarkedIso Q) 1 a.val.val = _ at he
  rw [←he] at ha ⊢
  exact original_derived_product_support Q (originalMarkedIso Q) split h hm n hn m ν T hC μ hB hcore a ha

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
