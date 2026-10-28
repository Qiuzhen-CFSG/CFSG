module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldAction
public import Theory.GroupTheory.ConjugateSpanOrder
public import Stellmacher.ElementaryAbelianMaxDefs

/-!
# The pending Sylow geometry of the involutory field fixed space

These interfaces separate 6.1.14(1--4) from its local-component application
in (5). The Sylow subgroup is chosen afresh: no normalization of the fixed
space by the original Sylow is assumed. The quotient uses the fixed space
inside its own normalizer. The closure is the literal conjugate span.

These are proof obligations, not asserted source theorems. Their producer
must arrange the field actor and prove every clause from the Chapter 6/12
source hypotheses. Source: Aschbacher--Smith, printed pp.670--671.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G]

/-- V_U in 6.1.14(4). -/
def fieldModuleClosure (B U : Subgroup G) : Subgroup G :=
  conjugateSpanBy B (normalizer (U : Set G))

/-- The module image in the literal normalizer quotient N_G(U)/U. -/
def fieldModuleClosureQuotient (B U : Subgroup G) :
    Subgroup (normalizer (U : Set G) ⧸ U.subgroupOf (normalizer (U : Set G))) :=
  ((fieldModuleClosure B U).subgroupOf (normalizer (U : Set G))).map
    (QuotientGroup.mk' (U.subgroupOf (normalizer (U : Set G))))

/-- The clauses of 6.1.14(1--4) used in the local-component argument,
at a suitably chosen ambient Sylow subgroup P. Normality and Sylow status
are relative to the specified local subgroups. -/
structure FieldFixedSpaceGeometry (L M B U : Subgroup G) (n : ℕ)
    (P : Sylow 2 G) : Prop where
  sylow_le : (P : Subgroup G) ≤ M
  module_le : B ≤ P
  normalizes_L : (P : Subgroup G) ≤ normalizer (L : Set G)
  normalizes_module : (P : Subgroup G) ≤ normalizer (B : Set G)
  parameter_even : Even n
  field_actor : ∃ t : normalizer (L : Set G), (t : G) ∈ P ∧
    (t : G) ∈ normalizer (B : Set G) ∧
    U = B ⊓ centralizer ({(t : G)} : Set G) ∧
    (P : Subgroup G) ⊓ centralizer (U : Set G) =
      ((P : Subgroup G) ⊓ centralizer (B : Set G)) ⊔ zpowers (t : G) ∧
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ n ∧
      ∃ (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
        (σ : F ≃+* F), σ ≠ 1 ∧ σ ^ 2 = 1 ∧
        ∀ l : L,
          e (QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom t l)) =
            Theory.PSL2.sl2FieldAut σ (e (QuotientGroup.mk' (pCore 2 L) l))
  centralizer_sylow : ∃ R : Sylow 2 (centralizer (U : Set G)),
    (R : Subgroup (centralizer (U : Set G))).map (centralizer (U : Set G)).subtype =
      (P : Subgroup G) ⊓ centralizer (U : Set G)
  normalizer_sylow : ∃ R : Sylow 2 (normalizer (U : Set G)),
    (R : Subgroup (normalizer (U : Set G))).map (normalizer (U : Set G)).subtype =
      (P : Subgroup G) ⊓ normalizer (U : Set G)
  thompson_control : normalizer (Stellmacher.elementaryAbelianMaxJ
    ((P : Subgroup G) ⊓ centralizer (U : Set G)) : Set G) ≤ M
  normalizer_even : normalizer (U : Set G) ∈ Chapter1.He G
  centralizer_even : centralizer (U : Set G) ∈ Chapter1.He G
  weak_zero : W B ((P : Subgroup G) ⊓ centralizer (U : Set G)) 0 ≤
    (P : Subgroup G) ⊓ centralizer (B : Set G)
  weak_one : 2 < n → W B ((P : Subgroup G) ⊓ centralizer (U : Set G)) 1 ≤
    (P : Subgroup G) ⊓ centralizer (B : Set G)
  closure_elementary : IsElementaryAbelian 2 (fieldModuleClosure B U)
  closure_reduced : IsPReduced 2 (fieldModuleClosureQuotient B U)
  core_commutator : ⁅(normalizer (U : Set G)).pCoreIn 2, fieldModuleClosure B U⁆ ≤ U

/-- The precise independent producer contract for 6.1.14(1--4). The field
actor is supplied in M; the witness P must be constructed, not assumed. -/
def FieldFixedSpaceGeometryFamily (L M B : Subgroup G) (n : ℕ) : Prop :=
  ∀ U : Subgroup G, U ≠ ⊥ → ChapterE.subgroupCorank B U = n →
    IsInvolutoryFieldFixedSpace L M B U n →
    ∃ P : Sylow 2 G, FieldFixedSpaceGeometry L M B U n P

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
