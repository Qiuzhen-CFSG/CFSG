module
public import CFSG.Quasithin.Chapter14.Section06.SourceClassificationInputs
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.RankTwoReconstruction

/-!+# The remaining model and module contracts in original 14.6.10(5)

The generated group retains the original first residual, second parabolic,
and preferred IStar intersection. Its first parabolic is recomputed inside
that generated group. The catalogue comparison must identify the actual
residual quotient, retaining the possible central cover in the A₆ row.

The module branches all concern the same original second-parabolic span.
These are independent proof contracts, not classification theorems.
Source: Aschbacher--Smith, original 14.6.10(5), printed pp.1029--1030.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The second parabolic uses the original H₂ and the chosen IStar intersection. -/
def sourceSecondParabolic (T : Sylow 2 G) (I H2 : Subgroup G) : Subgroup G :=
  (pResidual 2 H2).map H2.subtype ⊔ ((T : Subgroup G) ⊓ I)

/-- The literal generated choice, before recomputing its first parabolic. -/
noncomputable def sourceGeneratedParabolic (T : Sylow 2 G) (M Mc I H2 : Subgroup G) : Subgroup G :=
  ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
    (sourceResidual M Mc ⊓ I).subtype ⊔ ((T : Subgroup G) ⊓ I)) ⊔
      sourceSecondParabolic T I H2

/-- The actual residual component in the generated group. -/
noncomputable def sourceGeneratedComponent (T : Sylow 2 G) (M Mc I H2 : Subgroup G) : Subgroup G :=
  let I0 := sourceGeneratedParabolic T M Mc I H2
  (pResidual 2 I0).map I0.subtype

/-- The surviving actual quotient models. Only the A₆ row permits a
central cover; none of the rows asserts a whole-core module model. -/
def SourceParabolicRankThreeModels (C : Type*) [Group C] : Prop :=
  Nonempty ((C ⧸ pCore 2 C) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
  Nonempty ((C ⧸ centralPreimage (pCore 2 C)) ≃* alternatingGroup (Fin 6)) ∨
  Nonempty ((C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 7)) ∨
  Nonempty ((C ⧸ pCore 2 C) ≃* commutator (Atlas.G2.Model (ZMod 2)))

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- Catalogue intersection on the actual residual, with no preferred-choice
or module reconstruction assumption. -/
def SourceSecondParabolicModelInput : Prop :=
  ∀ (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G),
    I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M) →
    SourceParabolicRankThreeModels (sourceGeneratedComponent T M Mc I d.H2)

/-- A single module branch of 14.6.10(5). The original hypotheses and
preferred-centralizer condition remain unchanged. -/
def SourceSecondParabolicBranch (model : Subgroup G → Prop) : Prop :=
  ∀ (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G),
    I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M) →
    ((T : Subgroup G) ⊓ I = (T : Subgroup G) ⊓ centralizer ({d.u} : Set G) →
      I ≤ centralizer ({d.u} : Set G)) →
    model (sourceGeneratedComponent T M Mc I d.H2) →
    primeRank 2 (conjugateSpanBy (localModule T M) (sourceSecondParabolic T I d.H2)) = 3

end CFSG.Quasithin.Chapter14.Section06
