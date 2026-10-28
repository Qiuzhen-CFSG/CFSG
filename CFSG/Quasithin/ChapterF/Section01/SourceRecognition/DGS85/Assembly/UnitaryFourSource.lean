module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.TensorComparisonApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.ProfileRegularity
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.ReducedComparisons

/-!
# The reduced quadratic-profile U₄ row for original restoration

The Chapter 11 quadratic profile on S₀ = O₂(B) supplies two elementary
Sylow quotients. These prove the simple-remainder kernel containments before
constructing the complete U₄ presentation. Its model comparison marks both
reduced endpoints and the whole reduced Borel by one quotient equivalence.
The native orientation is retained, including fixed fields two and four.

The profile, marked quotient, split data and rotation order four are earlier
source inputs. The following consumer restores the ORIGINAL pair; an
isomorphism of the reduced pair alone does not identify the original S with S₀.
Source: DGS, Groups and Graphs (1985), (11.5)--(11.7), pp.173--175,
Theorem D and (15.2), pp.224--228; Fong--Seitz II (8B), pp.201--202.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.UnitaryFourSource
open FongSeitzBinary FongSeitzBinary.UnitarySource FongSeitzBinary.UnitaryPresentation
open OriginalExtension SuzukiContainment

/-- Earlier quadratic-profile data on the actual pair. The large-field actor
acts at the endpoint opposite the small-field point actor. No model comparison
or presentation equation is a field of this structure. -/
structure Profile {G : Type*} [Group G] (L : Fin 2 → Subgroup G) (S : Subgroup G)
    (F k : Type*) [Field F] [Field k] (point : Bool) where
  largeActor : (S ⊔ L (if point then 1 else 0)).subgroupOf
    (parabolic L S (if point then 1 else 0)) →* SL(2,F)
  smallActor : (S ⊔ L (if point then 0 else 1)).subgroupOf
    (parabolic L S (if point then 0 else 1)) →* SL(2,k)
  large_surjective : Function.Surjective largeActor
  small_surjective : Function.Surjective smallActor
  large_kernel : largeActor.ker =
    (pCore 2 (parabolic L S (if point then 1 else 0))).subgroupOf
      ((S ⊔ L (if point then 1 else 0)).subgroupOf (parabolic L S (if point then 1 else 0)))
  small_kernel : smallActor.ker =
    (pCore 2 (parabolic L S (if point then 0 else 1))).subgroupOf
      ((S ⊔ L (if point then 0 else 1)).subgroupOf (parabolic L S (if point then 0 else 1)))
  fields : Nat.card F = Nat.card k ^ 2
  large_index : (commonBorel L S).relIndex (parabolic L S (if point then 1 else 0)) =
    Nat.card F + 1
  small_index : (commonBorel L S).relIndex (parabolic L S (if point then 0 else 1)) =
    Nat.card k + 1
  large_core_elementary : IsElementaryAbelian 2
    ((parabolic L S (if point then 1 else 0)).pCoreIn 2)
  large_sylow_elementary : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) (if point then 1 else 0)
    IsElementaryAbelian 2 (S ⧸
      ((parabolic L S (if point then 1 else 0)).pCoreIn 2).subgroupOf S)
  small_sylow_elementary : letI := QuadrangleStructure.original_core_normal_in_sylow (L := L) (S := S) (if point then 0 else 1)
    IsElementaryAbelian 2 (S ⧸
      ((parabolic L S (if point then 0 else 1)).pCoreIn 2).subgroupOf S)
  small_core_nonabelian :
    ⁅(parabolic L S (if point then 0 else 1)).pCoreIn 2,
      (parabolic L S (if point then 0 else 1)).pCoreIn 2⁆ ≠ ⊥

variable {G X F k : Type*} [Group G] [Group X]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (h : HypothesisF11 L S) (Q : MarkedQuotient P)
  (e : Iso (reducedAmalgam L S) Q.standardAmalgam)
  (split : SplitData Q.tits) (hrot : rotationOrder Q = 4)
  (point : Bool) (profile : Profile L (reducedSylow L S) F k point)
  (m : ℕ) [NeZero m] (hk : Nat.card k = 2^m)

/-- Construct all U₄ equations from the literal reduced profile, deriving
both kernel containments from its elementary Sylow quotients. -/
def modelData : FourData Q split (if point then 0 else 1)
    (GreenBook.LieModels.UnitaryFour.fieldConj m)
    (GreenBook.LieModels.UnitaryFour.fieldConj_involutive m (NeZero.pos m)) := by
  let mark := (intersectionToReduced h).trans e
  let hr := reduced_hypothesis h
  have hVi := (QuadrangleStructure.regularity_of_sylow_core Q mark hr split
    (if point then 1 else 0) profile.large_sylow_elementary).1
  have hVj := (QuadrangleStructure.regularity_of_sylow_core Q mark hr split
    (if point then 0 else 1) profile.small_sylow_elementary).1
  exact Classical.choice (marked_quadratic_unitaryFour_modelData Q mark hr split hrot
    (if point then 1 else 0) (if point then 0 else 1) (by cases point <;> decide)
    hVi hVj profile.largeActor profile.smallActor profile.large_surjective
    profile.small_surjective profile.large_kernel profile.small_kernel profile.fields
    profile.large_index profile.small_index profile.large_core_elementary
    profile.large_sylow_elementary profile.small_sylow_elementary
    profile.small_core_nonabelian m hk)

/-- The native reduced comparison needed by Chapter 15 restoration. -/
def reducedComparison : Iso (reducedAmalgam L S)
    (UnitaryFourNative.amalgam m (NeZero.pos m) point) :=
  fourReducedComparison Q e split hrot m (NeZero.pos m) point
    (modelData h Q e split hrot point profile m hk)

/-- The same ambient equivalence induces all three reduced group maps. -/
def quotientEquiv : (X ⧸ Q.D) ≃* GreenBook.LieModels.UnitaryFour.ProjectiveGroup m (NeZero.pos m) :=
  ((modelData h Q e split hrot point profile m hk).projectiveEquiv
    (GreenBook.LieModels.UnitaryFour.fieldConj m)
    (GreenBook.LieModels.UnitaryFour.fieldConj_involutive m (NeZero.pos m)) hrot).symm

theorem reducedComparison_left (x : parabolic L (reducedSylow L S) 0) :
    ((reducedComparison h Q e split hrot point profile m hk).left x :
      GreenBook.LieModels.UnitaryFour.ProjectiveGroup m (NeZero.pos m)) =
      quotientEquiv h Q e split hrot point profile m hk (e.left x : X ⧸ Q.D) := by
  cases point <;> rfl

theorem reducedComparison_right (x : parabolic L (reducedSylow L S) 1) :
    ((reducedComparison h Q e split hrot point profile m hk).right x :
      GreenBook.LieModels.UnitaryFour.ProjectiveGroup m (NeZero.pos m)) =
      quotientEquiv h Q e split hrot point profile m hk (e.right x : X ⧸ Q.D) := by
  cases point <;> rfl

/-- The middle formula retains every element of the reduced Borel, not only S₀. -/
theorem reducedComparison_borel (b : commonBorel L (reducedSylow L S)) :
    ((reducedComparison h Q e split hrot point profile m hk).middle b :
      GreenBook.LieModels.UnitaryFour.ProjectiveGroup m (NeZero.pos m)) =
      quotientEquiv h Q e split hrot point profile m hk (e.middle b : X ⧸ Q.D) := by
  cases point <;> rfl

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.UnitaryFourSource

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.UnitaryFourSource
open FongSeitzBinary FongSeitzBinary.UnitaryPresentation OriginalExtension SuzukiContainment
variable {G F k : Type*} [Group G]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} (h : HypothesisF11 L S)
  (Q : SourceQuotient L (reducedSylow L S))

/-- The literal generated-source quotient, retaining the whole reduced Borel. -/
def literalMark : Iso (reducedAmalgam L S) Q.standardAmalgam :=
  (intersectionToReduced h).symm.trans (originalMarkedIso Q)

variable (split : SplitData Q.tits) (hrot : rotationOrder Q = 4)
  (point : Bool) (profile : Profile L (reducedSylow L S) F k point)
  (m : ℕ) [NeZero m] (hk : Nat.card k = 2^m)

/-- At the generated-source specialization all three comparison maps evaluate
on the literal Q.q representatives, including the odd part of the overlap. -/
theorem literalComparison_squares :
    let e := literalMark h Q
    let c := reducedComparison h Q e split hrot point profile m hk
    let f := quotientEquiv h Q e split hrot point profile m hk
    (∀ x : parabolic L (reducedSylow L S) 0,
      (c.left x : GreenBook.LieModels.UnitaryFour.ProjectiveGroup m (NeZero.pos m)) =
        f (Q.q ⟨x,parabolic_le_generated 0 x.property⟩)) ∧
    (∀ b : commonBorel L (reducedSylow L S),
      (c.middle b : GreenBook.LieModels.UnitaryFour.ProjectiveGroup m (NeZero.pos m)) =
        f (Q.q ⟨b,parabolic_le_generated 0 (commonBorel_le_parabolic 0 b.property)⟩)) ∧
    (∀ x : parabolic L (reducedSylow L S) 1,
      (c.right x : GreenBook.LieModels.UnitaryFour.ProjectiveGroup m (NeZero.pos m)) =
        f (Q.q ⟨x,parabolic_le_generated 1 x.property⟩)) := by
  dsimp only
  refine ⟨?_,?_,?_⟩
  · intro x
    rw [reducedComparison_left]
    apply congrArg
    exact originalMarkedIso_left_apply Q x
  · intro b
    rw [reducedComparison_borel]
    apply congrArg
    exact originalMarkedIso_middle_apply Q ((intersectionToReduced h).symm.middle b)
  · intro x
    rw [reducedComparison_right]
    apply congrArg
    exact originalMarkedIso_right_apply Q x

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.UnitaryFourSource
