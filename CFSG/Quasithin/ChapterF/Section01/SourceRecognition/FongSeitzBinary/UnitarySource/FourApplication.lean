module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FourTensor
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.FieldComparison
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.SourceCollection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RootCoordinates.SourceProducts

/-!
# Applying the Hermitian tensor calculation to the original split quotient

On the SAME original quotient Q, realize the complementary simple-root
subgroup as the Hermitian tensor module for the root-generated SL2 actor.
The module calculation constructs all four positive root maps and proves
their exact polynomial relations. The split-root factorization then proves
that they generate the literal Q.q-image of S, and the existing unitary
collector applies with both of its former premises discharged.

This is an intermediate application: construction and compatible labeling
of the actor and its module realization from Fong--Seitz I Sections 4,6
and II (8B) remain with qt-dgs85-unitary-source-recognition, as do the U5
branch, full torus/Weyl laws and endpoint placements. No assertion here
identifies an arbitrary original parabolic with a rank-one model.
Source: Fong--Seitz II pp.201--202, (8.7)--(8.9); DGS Theorem D, p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open Representation.OrthogonalFourMinus
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource

variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {E : Type*} [Field E] [CharP E 2]
variable (Q : SourceQuotient L S) (split : SplitData Q.tits)
variable (σ : E ≃+* E) (hσ : Function.Involutive σ)
variable (l : SpecialLinearGroup (Fin 2) E →* ((generated L S) ⧸ Q.D))
variable (v : Multiplicative (FourTensor.Core E σ hσ) →* ((generated L S) ⧸ Q.D))

omit [CharP E 2] in
/-- The actual simple root and actual complementary section generate U;
no root-generation hypothesis is required once these images are identified. -/
theorem four_generated_eq_unipotent (i : Fin 2)
    (hA : (FourTensor.roots E σ hσ l v).A.range = simpleRoot Q split i)
    (hV : v.range = simpleRemainder Q split i) :
    (FourTensor.roots E σ hσ l v).generated = split.U := by
  rw [FourTensor.generated_eq, hA, hV]
  apply le_antisymm
  · exact sup_le (simpleRoot_le Q split i) inf_le_left
  · intro x hx
    have hm : x ∈ (simpleRoot Q split i : Set ((generated L S) ⧸ Q.D)) *
        (simpleRemainder Q split i : Set ((generated L S) ⧸ Q.D)) := by
      rw [simpleRoot_mul_remainder]
      exact hx
    obtain ⟨a,ha,b,hb,rfl⟩ := hm
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)

omit [CharP E 2] in
/-- Generation is on the literal original S image under Q.q. -/
theorem four_generated_eq_originalS (h : HypothesisF11 L S) (i : Fin 2)
    (hA : (FourTensor.roots E σ hσ l v).A.range = simpleRoot Q split i)
    (hV : v.range = simpleRemainder Q split i) :
    (FourTensor.roots E σ hσ l v).generated = (S.subgroupOf (generated L S)).map Q.q := by
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  exact four_generated_eq_unipotent Q split σ hσ l v i hA hV

/-- Literal application of four_originalS_collected: tensor equivariance
proves the mixed equations and actual section placement proves generation. -/
theorem four_originalS_collected_of_tensor (h : HypothesisF11 L S) (i : Fin 2)
    (hA : (FourTensor.roots E σ hσ l v).A.range = simpleRoot Q split i)
    (hV : v.range = simpleRemainder Q split i)
    (hequiv : ∀ (g : SpecialLinearGroup (Fin 2) E) (p : FourTensor.Core E σ hσ),
      l g * v (Multiplicative.ofAdd p) * (l g)⁻¹ =
        v (Multiplicative.ofAdd (hermitianAction (FourTensor.conjugation E σ) hσ g p)))
    (x : (generated L S) ⧸ Q.D) (hx : x ∈ (S.subgroupOf (generated L S)).map Q.q) :
    ∃ a d c b, x = (FourTensor.roots E σ hσ l v).word a d c b := by
  exact UnitaryPresentation.four_originalS_collected h Q split σ hσ
    (FourTensor.roots E σ hσ l v) (FourTensor.relations E σ hσ l v hequiv)
    (four_generated_eq_unipotent Q split σ hσ l v i hA hV).ge x hx

/-- The field comparison takes place in a quotient of the actual
complementary subgroup, retaining the original Q and the relative kernel.
The two action calculations are still to be constructed from the source;
their field compatibility is a conclusion of this theorem. -/
theorem four_same_core_common_field [Finite E]
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (i : Fin 2) (Z : Subgroup (simpleRemainder Q split i)) [Z.Normal]
    [IsMulCommutative ((simpleRemainder Q split i) ⧸ Z)]
    (ι κ : F →+* E) (τ₁ τ₂ ρ : F ≃+* F) (θ x y : E)
    (u : E →+ Additive ((simpleRemainder Q split i) ⧸ Z))
    (hu : Function.Injective u)
    (δ : E → F → Additive ((simpleRemainder Q split i) ⧸ Z))
    (hnatural : ∀ a b, δ a b = u (a*κ b))
    (htensor : ∀ a₁ a₂ b,
      -δ (ι a₁+ι a₂*θ) b =
        u (ι (τ₂ (τ₁.symm b)) *
          (ι (τ₂ (ρ a₁))*x+ι (τ₂ (ρ a₂))*y))) :
    x = 1 ∧ y = θ ∧ ρ.trans τ₂ = RingEquiv.refl F ∧
      ∃ η : E ≃+* E,
        (∀ b, η (ι b) = κ b) ∧
        (∀ a b, δ (η a) b = (u.comp η.toAddMonoidHom) (a*ι b)) ∧
        ∀ (σ₀ : E ≃+* E) a, η (σ₀ a) = σ₀ (η a) :=
  exists_common_field_labels ι κ τ₁ τ₂ ρ θ x y u hu δ hnatural htensor

omit [CharP E 2] in
/-- Embed the tensor module by its realization in the literal complement. -/
@[expose] def tensorEmbedding (i : Fin 2)
    (e : Multiplicative (FourTensor.Core E σ hσ) ≃* simpleRemainder Q split i) :
    Multiplicative (FourTensor.Core E σ hσ) →* ((generated L S) ⧸ Q.D) :=
  (simpleRemainder Q split i).subtype.comp e.toMonoidHom

omit [CharP E 2] in
theorem tensorEmbedding_range (i : Fin 2)
    (e : Multiplicative (FourTensor.Core E σ hσ) ≃* simpleRemainder Q split i) :
    (tensorEmbedding Q split σ hσ i e).range = simpleRemainder Q split i := by
  ext z
  constructor
  · rintro ⟨X,rfl⟩
    exact (e X).property
  · intro hz
    obtain ⟨X,hX⟩ := e.surjective ⟨z,hz⟩
    exact ⟨X,congrArg Subtype.val hX⟩

/-- Actual module realization supplies its range automatically. The missing
source input is precisely the rank-one actor and this equivariant module
realization, not the polynomial equations or positive generation. -/
theorem four_originalS_collected_of_realization (h : HypothesisF11 L S) (i : Fin 2)
    (e : Multiplicative (FourTensor.Core E σ hσ) ≃* simpleRemainder Q split i)
    (hA : (l.comp (SpecialLinearGroup.upperUnipotentHom E)).range = simpleRoot Q split i)
    (hequiv : ∀ (g : SpecialLinearGroup (Fin 2) E) (p : FourTensor.Core E σ hσ),
      l g * (e (Multiplicative.ofAdd p) : (generated L S) ⧸ Q.D) * (l g)⁻¹ =
        e (Multiplicative.ofAdd (hermitianAction (FourTensor.conjugation E σ) hσ g p)))
    (x : (generated L S) ⧸ Q.D) (hx : x ∈ (S.subgroupOf (generated L S)).map Q.q) :
    ∃ a d c b, x = (FourTensor.roots E σ hσ l (tensorEmbedding Q split σ hσ i e)).word a d c b :=
  four_originalS_collected_of_tensor Q split σ hσ l (tensorEmbedding Q split σ hσ i e)
    h i hA (tensorEmbedding_range Q split σ hσ i e) hequiv x hx

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
