module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Inputs

/-!
# Independent seven-letter module obligations for original 14.6.10(5)

These contracts retain the original d and IStar choice and the literal
component O²(I₀). Reconstruction must identify the whole block, including
its possible exceptional four-space. In the ordinary case the vector is
fixed by the first parabolic, while its component centralizer escapes M
and Mc. These intermediate geometric facts feed the maximal-intersection
argument; no rank conclusion or preferred-centralizer consequence is stored
in that geometry.

Source: Aschbacher--Smith, original14.6.10(5), pp.1029--1030.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.Seven
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The recomputed first residual inside the literal generated group. -/
noncomputable def firstResidual (T : Sylow 2 G) (M Mc I H2 : Subgroup G) : Subgroup G :=
  let I0 := sourceGeneratedParabolic T M Mc I H2
  (pResidual 2 (sourceResidual M Mc ⊓ I0 : Subgroup G)).map
    (sourceResidual M Mc ⊓ I0).subtype

/-- The six-support vector in the seven-letter permutation core, expressed
in the original group. The partition and point markings must construct it. -/
structure OrdinaryGeometry (T : Sylow 2 G) (M Mc I H2 : Subgroup G) where
  vector : G
  mem_span : vector ∈ conjugateSpanBy (localModule T M) (sourceSecondParabolic T I H2)
  ne_one : vector ≠ 1
  first_fixed : firstResidual T M Mc I H2 ≤ centralizer ({vector} : Set G)
  sylow_fixed : (T : Subgroup G) ⊓ sourceGeneratedParabolic T M Mc I H2 ≤
    centralizer ({vector} : Set G)
  escapes_Mc : ¬ sourceGeneratedComponent T M Mc I H2 ⊓
    centralizer ({vector} : Set G) ≤ Mc
  escapes_M : ¬ sourceGeneratedComponent T M Mc I H2 ⊓
    centralizer ({vector} : Set G) ≤ M

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- Whole-core reconstruction on the literal generated A₇ component. -/
def ReconstructionInput : Prop :=
  ∀ (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G),
    I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M) →
    Nonempty ((sourceGeneratedComponent T M Mc I d.H2 ⧸
      pCore 2 (sourceGeneratedComponent T M Mc I d.H2)) ≃* alternatingGroup (Fin 7)) →
    ChapterC.IsAlternatingBlock (sourceGeneratedComponent T M Mc I d.H2) 7 ∨
      ChapterC.IsExceptionalA7Block (sourceGeneratedComponent T M Mc I d.H2)

/-- Ordinary permutation geometry on the same d, I and component.
The preferred-centralizer and maximal-intersection steps are proved separately. -/
def OrdinaryGeometryInput : Prop :=
  ∀ (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G),
    I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M) →
    ChapterC.IsAlternatingBlock (sourceGeneratedComponent T M Mc I d.H2) 7 →
      Nonempty (OrdinaryGeometry T M Mc I d.H2)

/-- The exceptional four-space calculation with its original point and line. -/
def ExceptionalRankInput : Prop :=
  SourceSecondParabolicBranch hG T hempty hM hunique hmany hcard e hab
    (fun C => ChapterC.IsExceptionalA7Block C)

end CFSG.Quasithin.Chapter14.Section06.Seven
