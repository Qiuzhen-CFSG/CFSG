module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.UnitaryFourConsumers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryAllFields

/-!
# Combining the two unitary source branches

The quadratic row constructs its complete presentation from the original
profile. The other row retains the exact earlier (6A)(c) profile and generic
SU₃ cover. Its source-recognition theorem is an explicit independent premise,
owned by `qt-dgs85-unitary-five-source-recognition`; it is not proved here.
Once supplied, both rows feed the same reduced-alternative consumer, which
restores the original whole Borel and both endpoints in Chapter 12.

`Row` records a selected source profile, not an exhaustiveness theorem.
The marked quotient, splitness, rotation order, profiles, cover and selection
remain with their existing source producers. No FiveData or equation package
is substituted for the missing U₅ source theorem. Its required output retains
one quotient equivalence inducing all three maps, in either orientation and
at every positive binary degree, including degrees one and two.

Sources: Fong--Seitz I (6A)(b,c), pp.37--38; II (8B,C), pp.197--210;
DGS (1985), Theorem D and (15.2), pp.224--228.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource.Combined
open DGS85.OriginalExtension SuzukiContainment
open UnitaryPresentation
universe u v w z

/-- Precisely the earlier-profile and covering inputs to the all-fields
unitary (6A)(c) theorem. No source-coordinate or model-comparison conclusion
is part of this input. -/
structure FiveProfile {G : Type u} {X : Type v} [Group G] [Group X]
    (L : Fin 2 → Subgroup G) (S : Subgroup G) {P : Fin 2 → Subgroup X}
    (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (K : Type w) (E : Type z) [Field K] [Field E]
    (n : ℕ) (i j : Fin 2) where
  form : HermitianForm 3 E
  linear_card : Nat.card K = (2^n)^2
  unitary_card : Nat.card E = (2^n)^2
  fixed_card : Nat.card {x : E // form.conj x = x} = 2^n
  matrix : form.form = !![0,0,1;0,1,0;1,0,0]
  conjugation : ∀ x, form.conj x = x^(2^n)
  linear_remainder : simpleRemainder Q split i ≤ localKernel Q i
  unitary_remainder : simpleRemainder Q split j ≤ localKernel Q j
  linear_reflection : RootReflection Q split i
  unitary_reflection : RootReflection Q split j
  linear_actor : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K)
  linear_surjective : Function.Surjective linear_actor
  linear_kernel : linear_actor.ker = (pCore 2 (parabolic L S i)).subgroupOf
    ((S ⊔ L i).subgroupOf (parabolic L S i))
  unitary_panel : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup form
  cover : form.specialSubgroup →* rankOne Q split j
  cover_surjective : Function.Surjective cover
  cover_square : ∀ a, unitary_panel (RootLocalCover.projection Q split j (cover a)) =
    form.specialToProjective a
  linear_index : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1
  unitary_index : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1
  linear_sylow_elementary :
    letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) i
    IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S)
  unitary_derived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2)
  unitary_frattini : frattini ((parabolic L S j).pCoreIn 2) =
    center ((parabolic L S j).pCoreIn 2)

variable {G : Type u} {X : Type v} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

/-- The independent U₅ producer must supply the full marked comparison on
this very quotient. All three maps use the same equivalence. -/
structure FiveComparison (Q : MarkedQuotient P)
    (e : Iso (reducedAmalgam L S) Q.standardAmalgam) (n : ℕ) (line : Bool) where
  model : GreenBook.UnitaryFive.Model (2^n)
  quotient : (X ⧸ Q.D) ≃* model.Carrier
  comparison : Iso (reducedAmalgam L S) (UnitaryFiveNative.amalgam model line)
  left_square : ∀ x : parabolic L (reducedSylow L S) 0,
    (comparison.left x : model.Carrier) = quotient (e.left x : X ⧸ Q.D)
  middle_square : ∀ b : commonBorel L (reducedSylow L S),
    (comparison.middle b : model.Carrier) = quotient (e.middle b : X ⧸ Q.D)
  right_square : ∀ x : parabolic L (reducedSylow L S) 1,
    (comparison.right x : model.Carrier) = quotient (e.right x : X ⧸ Q.D)

/-- The outstanding source theorem, as a proposition rather than an axiom.
Its source inputs are the exact profile/cover boundary of (6A)(c).
The final assembly owner must construct a proof of this proposition. -/
def FiveSourceTheorem (Q : MarkedQuotient P)
    (e : Iso (reducedAmalgam L S) Q.standardAmalgam) (split : SplitData Q.tits) : Prop :=
  HypothesisF11 L S → rotationOrder Q = 4 →
    ∀ (K : Type w) (E : Type z) [Field K] [Finite K] [CharP K 2]
      [Field E] [Finite E] [CharP E 2] (n : ℕ), 0 < n → ∀ line : Bool,
      FiveProfile L (reducedSylow L S) Q split K E n
        (if line then 1 else 0) (if line then 0 else 1) →
      Nonempty (FiveComparison Q e n line)

/-- Selected earlier profiles for the two unitary rows. This does not assert
that arbitrary source configurations lie in either row. -/
inductive Row (L : Fin 2 → Subgroup G) (S : Subgroup G)
    (Q : MarkedQuotient P) (split : SplitData Q.tits) : Prop
  | four (F : Type w) (k : Type z) [Field F] [Finite F] [CharP F 2]
      [Field k] [Finite k] [CharP k 2] (n : ℕ) (hn : 0 < n)
      (hk : Nat.card k = 2^n) (point : Bool)
      (profile : DGS85.Assembly.UnitaryFourSource.Profile L (reducedSylow L S) F k point)
  | five (K : Type w) (E : Type z) [Field K] [Finite K] [CharP K 2]
      [Field E] [Finite E] [CharP E 2] (n : ℕ) (hn : 0 < n) (line : Bool)
      (profile : FiveProfile L (reducedSylow L S) Q split K E n
        (if line then 1 else 0) (if line then 0 else 1))

variable {L₀ R₀ : Subgroup G}

/-- Conditional combined assembly. The U₄ branch constructs its equations;
the U₅ branch invokes the separate source theorem at its actual profile.
Both comparisons retain the full reduced overlap for original restoration. -/
theorem reduced_alternative_of_five_source
    (h : HypothesisF11 ![L₀,R₀] S) (Q : MarkedQuotient P)
    (e : Iso (reducedAmalgam ![L₀,R₀] S) Q.standardAmalgam)
    (split : SplitData Q.tits) (hrot : rotationOrder Q = 4)
    (hfive : FiveSourceTheorem.{u,v,w,z} Q e split)
    (row : Row.{u,v,w,z} ![L₀,R₀] S Q split) :
    Chapter6.Source.RankOneGeneric.Global.OriginalExtension.ReducedAlternatives L₀ R₀ S := by
  cases row with
  | four F k n hn hk point profile =>
    let : NeZero n := ⟨Nat.ne_of_gt hn⟩
    exact DGS85.Assembly.UnitaryFourSource.reduced_alternative h Q e split hrot point profile n hk
  | five K E n hn line profile =>
    obtain ⟨c⟩ := hfive h hrot K E n hn line profile
    exact .unitaryFive (2^n) (Nat.prime_two.isPrimePow.pow (Nat.ne_of_gt hn))
      (even_two.pow_of_ne_zero (Nat.ne_of_gt hn)) c.model line ⟨c.comparison⟩

/-- Literal source representatives for the required U₅ output. This
specialization merely exposes the producer's map equations, not its proof. -/
theorem five_literal_squares (h : HypothesisF11 L S)
    (Q : SourceQuotient L (reducedSylow L S)) (n : ℕ) (line : Bool)
    (c : FiveComparison Q (DGS85.Assembly.UnitaryFourSource.literalMark h Q) n line) :
    (∀ x : parabolic L (reducedSylow L S) 0,
      (c.comparison.left x : c.model.Carrier) =
        c.quotient (Q.q ⟨x,parabolic_le_generated 0 x.property⟩)) ∧
    (∀ b : commonBorel L (reducedSylow L S),
      (c.comparison.middle b : c.model.Carrier) =
        c.quotient (Q.q ⟨b,parabolic_le_generated 0 (commonBorel_le_parabolic 0 b.property)⟩)) ∧
    (∀ x : parabolic L (reducedSylow L S) 1,
      (c.comparison.right x : c.model.Carrier) =
        c.quotient (Q.q ⟨x,parabolic_le_generated 1 x.property⟩)) := by
  refine ⟨?_,?_,?_⟩
  · intro x
    rw [c.left_square]
    exact congrArg c.quotient (originalMarkedIso_left_apply Q x)
  · intro b
    rw [c.middle_square]
    exact congrArg c.quotient
      (originalMarkedIso_middle_apply Q ((intersectionToReduced h).symm.middle b))
  · intro x
    rw [c.right_square]
    exact congrArg c.quotient (originalMarkedIso_right_apply Q x)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource.Combined
