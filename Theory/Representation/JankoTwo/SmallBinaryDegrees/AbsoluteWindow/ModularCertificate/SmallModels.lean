module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.Models
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.G2FourModule.Embedding.InnerRealization.Presentation
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.Certificates
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.Data
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.RankOne
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.SixCertificate
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.FourteenCertificate

/-!
# Assembly of the four small characteristic-two Hall--Janko actions

The degree-six and degree-fourteen numerical certificates each construct two
inequivalent simple actions of the literal degree-100 carrier. Their four-way
assembly uses dimensions to distinguish the two degrees. Both numerical
certificates are proved in the imported modules: their checked rank-one orbit
identities give irreducibility, and their nonbinary traces distinguish each
Frobenius pair. Presentation injectivity is the sole remaining hypothesis.

Source: the ATLAS J2G1-f4r6aB0 and J2G1-f4r14aB0 generators, and J2G1-P2.
Data, attribution, and witness conventions are in SmallModels/source/README.md.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate
open Sporadic.LeechRelated.J2 G2FourModule.Embedding.InnerRealization SmallModels
universe v

theorem smallModelsExist_of_parameterCertificates
    (hp : Function.Injective Presentation.toCarrier)
    (hsix : ParameterCertificate.{v} SixData.A SixData.B SixData.traceWord SixData.traceCode)
    (hfourteen : ParameterCertificate.{v}
      FourteenData.A FourteenData.B FourteenData.traceWord FourteenData.traceCode) :
    SmallModelsExist.{v} := by
  intro F _ _ _
  obtain ⟨ρ₆, σ₆, hρ₆, hσ₆, hne₆⟩ := exists_pair_of_certificate hp _ _ _ _
    SixData.traceCode_nonbinary hsix F
  obtain ⟨ρ₁₄, σ₁₄, hρ₁₄, hσ₁₄, hne₁₄⟩ := exists_pair_of_certificate hp _ _ _ _
    FourteenData.traceCode_nonbinary hfourteen F
  let ρ : ∀ i, Representation F Carrier (Fin (smallDegree i) → F) :=
    Fin.cases ρ₆ (Fin.cases σ₆ (Fin.cases ρ₁₄ (Fin.cases σ₁₄ (fun i => Fin.elim0 i))))
  refine ⟨ρ, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hρ₆
    · exact hσ₆
    · exact hρ₁₄
    · exact hσ₁₄
  · intro i j hij
    constructor
    intro e
    have hd := e.toLinearEquiv.finrank_eq
    fin_cases i <;> fin_cases j
    all_goals first
      | exact hij rfl
      | exact hne₆.false e
      | exact hne₆.false e.symm
      | exact hne₁₄.false e
      | exact hne₁₄.false e.symm
      | norm_num [smallDegree] at hd

/-- Four pairwise inequivalent irreducible actions of the literal Hall--Janko
carrier, of dimensions 6, 6, 14 and 14, over every algebraically closed field of
characteristic two. The matrix certificates are discharged; only exactness of
the marked presentation remains as the independent group-theoretic input. -/
theorem smallModelsExist_of_presentation_injective
    (hp : Function.Injective Presentation.toCarrier) : SmallModelsExist.{v} :=
  smallModelsExist_of_parameterCertificates hp
    six_parameterCertificate fourteen_parameterCertificate

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate
