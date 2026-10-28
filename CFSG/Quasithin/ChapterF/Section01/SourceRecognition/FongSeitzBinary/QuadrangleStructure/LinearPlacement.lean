module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.LinearPlacement
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.ProfileActors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.FourApplication

public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.RootActors

/-!
# The original linear actor in the U4 tensor consumer

The actual original actor quotient constructs the FULL linear root
actor. An inner Sylow adjustment pins its upper-unipotent matrices to
the canonical simple root of the same SourceQuotient. Every matrix
retains an original actor representative under the literal Q.q and its
original quotient value, modified only by the displayed conjugation.

This discharges the actor and simple-root-placement premise of
FourApplication.four_originalS_collected_of_realization. Once the unitary
owner constructs the tensor realization for this actor and proves its
equivariance, that existing theorem gives every positive word for the
full original S image. The realization and equivariance remain explicit;
no module realization or full unitary recognition is asserted here.
The earlier source quotient, full overlap, both endpoint markings and
section 2/5 inputs are preserved, including fields two and four.

Source: DGS (11.7), pp.174--175; Fong--Seitz I (6A)(b), pp.37--38,
and II (8B), pp.201--202.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Matrix (SpecialLinearGroup)
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open Representation.OrthogonalFourMinus
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G F : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The original actor quotient supplies the full actor and simple-root
placement used by FourApplication. The original quotient equation is
retained after the inner Sylow adjustment. Tensor realization and its
actual equivariance remain the independent unitary-source obligations. -/
theorem original_linear_actor_for_tensor (h : HypothesisF11 L S)
    (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (i : Fin 2) (s : RootReflection Q split i)
    (hV : simpleRemainder Q split i ≤ localKernel Q i)
    (A : Subgroup (parabolic L S i)) [A.Normal]
    (hSA : S.subgroupOf (parabolic L S i) ≤ A)
    (f : A →* SL(2,F)) (hf : Function.Surjective f)
    (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf A) :
    ∃ l : SL(2,F) →* ((generated L S) ⧸ Q.D),
      Function.Injective l ∧ l.range = rootActor Q split i ∧
      (l.comp (SpecialLinearGroup.upperUnipotentHom F)).range = simpleRoot Q split i ∧
      (∃ g : SL(2,F), ∀ a : SL(2,F), ∃ z : A,
        Q.q ⟨z.val,parabolic_le_generated i z.val.property⟩ = l a ∧
        f z = (MulAut.conj g) a) ∧
      ∀ (σ : F ≃+* F) (hσ : Function.Involutive σ)
        (v : Multiplicative (FourTensor.Core F σ hσ) ≃* simpleRemainder Q split i),
        (∀ (a : SL(2,F)) (p : FourTensor.Core F σ hσ),
          l a * (v (Multiplicative.ofAdd p) : (generated L S) ⧸ Q.D) * (l a)⁻¹ =
            v (Multiplicative.ofAdd (hermitianAction (FourTensor.conjugation F σ) hσ a p))) →
        ∀ x : (generated L S) ⧸ Q.D, x ∈ (S.subgroupOf (generated L S)).map Q.q →
          ∃ a d c b, x = (FourTensor.roots F σ hσ l
            (UnitarySource.tensorEmbedding Q split σ hσ i v)).word a d c b := by
  obtain ⟨μ,hμ⟩ := original_linear_rankOne h Q split i s hV A hSA f hf hk
  obtain ⟨g,l,hinj,hr,hroot,he⟩ :=
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure.exists_linear_root_embedding
      Q split i hV μ
  refine ⟨l,hinj,hr,hroot,⟨g,?_⟩,?_⟩
  · intro a
    obtain ⟨z,hz,hfz⟩ := hμ (μ.symm ((MulAut.conj g) a))
    exact ⟨z,hz.trans (he a).symm,hfz.symm.trans (μ.apply_symm_apply _)⟩
  · intro σ hσ v hequiv x hx
    exact UnitarySource.four_originalS_collected_of_realization Q split σ hσ l h i v hroot hequiv x hx

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
