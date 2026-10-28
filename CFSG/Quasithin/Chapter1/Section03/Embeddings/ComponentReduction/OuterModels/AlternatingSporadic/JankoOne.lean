module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne.InvolutionOrbit
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne.GeneratorImages
public import Theory.GroupTheory.Covering

/-!
# Triviality of the J₁ outer group and its two outer restrictions

The certified involution-orbit closure and generator-image calculation discharge
both finite premises of `Reduction`. After conjugating an automorphism to fix
`b`, the calculation realizes its image of `a` by an element centralizing `b`.
Since `a` and `b` generate the actual matrix model, every automorphism is inner.

Triviality of the actual quotient `Aut/Inn` gives both the cyclic-normal
odd-quotient condition and the abelian-outer condition. `MulAut.outerCongr`
transports these conclusions along the supplied equivalence with the actual
matrix model. The second contract retains only the supplied quasisimplicity
hypothesis and adds no simplicity assumption.

The conditional assembly lemmas are retained, and the unconditional exports
supply both finite certificates.
Source: Aschbacher–Smith, Theorem C on printed p.33 and the proofs on pp.504,
510; GLS3, Table 5.3f (`Out(J₁) = 1`).
-/

namespace Janko1.OuterCertificate

/-- Every automorphism of the actual J₁ matrix model is inner. -/
public theorem aut_inner (f : MulAut Model) : ∃ g : Model, MulAut.conj g = f :=
  aut_inner_of_matrix_certificates orbitClosed generatorImageRigid f

/-- The actual outer automorphism group of the J₁ matrix model is trivial. -/
public theorem outer_subsingleton : Subsingleton (MulAut.Outer Model) :=
  outer_subsingleton_of_matrix_certificates orbitClosed generatorImageRigid

end Janko1.OuterCertificate

namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
open Theory.GroupTheory Janko1.OuterCertificate

private theorem janko_one_outer_subsingleton_of_mulEquiv
    (hc : OrbitClosed) (hr : GeneratorImageRigid)
    {G : Type*} [Group G] (e : G ≃* Janko1.Model) : Subsingleton (MulAut.Outer G) := by
  let := outer_subsingleton_of_matrix_certificates hc hr
  exact (MulAut.outerCongr e).injective.subsingleton

/-- The simple-model contract, conditional on the two finite checks. -/
public theorem janko_one_outer_cyclicNormalOddQuotient_of_matrix_certificates
    (hc : OrbitClosed) (hr : GeneratorImageRigid)
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    (e : S ≃* Janko1.Model) : HasCyclicNormalOddQuotient (MulAut.Outer S) := by
  let := janko_one_outer_subsingleton_of_mulEquiv hc hr e
  exact hasCyclicNormalOddQuotient_of_isCyclic

/-- The quasisimple-model contract, without any added simplicity assumption. -/
public theorem janko_one_outer_isMulCommutative_of_matrix_certificates
    (hc : OrbitClosed) (hr : GeneratorImageRigid)
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (e : Q ≃* Janko1.Model) : IsMulCommutative (MulAut.Outer Q) := by
  let := janko_one_outer_subsingleton_of_mulEquiv hc hr e
  exact isMulCommutative_iff.mpr (fun _ _ => Subsingleton.elim _ _)

/-- The J₁ case of the cyclic-normal odd-quotient restriction on outer groups. -/
public theorem janko_one_outer_cyclicNormalOddQuotient
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    (e : S ≃* Janko1.Model) : HasCyclicNormalOddQuotient (MulAut.Outer S) :=
  janko_one_outer_cyclicNormalOddQuotient_of_matrix_certificates
    orbitClosed generatorImageRigid e

/-- The J₁ abelian-outer restriction, with only the supplied quasisimplicity hypothesis. -/
public theorem janko_one_outer_isMulCommutative
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (e : Q ≃* Janko1.Model) : IsMulCommutative (MulAut.Outer Q) :=
  janko_one_outer_isMulCommutative_of_matrix_certificates
    orbitClosed generatorImageRigid e

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
