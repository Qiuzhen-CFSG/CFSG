module
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.Reorientation.Actors
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Basic
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.GroupTheory.CComponent.Basic
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!+# Complete earlier model conclusions for the transvection alternative

This file specifies the complete 13.8.5 conclusion used in 13.8.8(1).
It retains H=KT as a set product, a C-component inside H, the actual
H/O₂(H) group and module identifications, the L/O₂(L) alternatives,
and the two noncentral L₁-chief factors in the S₆ case. The five-dimensional
cover is the binary augmentation core on six letters. The seven-dimensional
permutation module's core is the natural S₇ module of dimension six.

`FullModelConclusions` is an earlier-theorem output specification, not a
claim to prove 13.8.5. The final alternatives theorem applies its explicit
13.8.5 implication to a constructed nonidentity transvection actor.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.5,
printed p.947, used in 13.8.8, printed p.949.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.Reorientation
open AsymmetricPair
variable {G : Type*} [Group G] {H U Z : Subgroup G}
  [IsElementaryAbelian 2 U] [(Z.subgroupOf U).Normal]

/-- The actual conjugation representation on the literal quotient. -/
def literalRepresentation (Q : CenterQuotientAction H U Z) :
    Representation (ZMod 2) H (Additive (U ⧸ Z.subgroupOf U)) where
  toFun h := (binaryLinear (Q.action h)).toLinearMap
  map_one' := by
    ext x
    change Q.action 1 x.toMul = x.toMul
    rw [map_one]
    rfl
  map_mul' a b := by
    ext x
    change Q.action (a * b) x.toMul = Q.action a (Q.action b x.toMul)
    rw [map_mul]
    rfl

/-- A genuine model of the H* action, using the canonical projection H→H*. -/
structure StarModuleModel (Q : CenterQuotientAction H U Z)
    {K E : Type*} [Group K] [AddCommGroup E] [Module (ZMod 2) E]
    (σ : Representation (ZMod 2) K E) where
  groupEquiv : Source.Hstar H ≃* K
  moduleEquiv : Additive (U ⧸ Z.subgroupOf U) ≃ₗ[ZMod 2] E
  intertwines : ∀ (h : H) (v : Additive (U ⧸ Z.subgroupOf U)),
    moduleEquiv (literalRepresentation Q h v) =
      σ (groupEquiv (QuotientGroup.mk' (pCore 2 H) h)) (moduleEquiv v)

/-- A complete invariant chief series with exactly two noncentral factors.
Trivial chief factors may occur and are not counted. -/
def TwoNoncentralChiefFactors {J E : Type*} [Group J] [AddCommGroup E]
    [Module (ZMod 2) E] (σ : Representation (ZMod 2) J E) : Prop :=
  ∃ n : ℕ, ∃ chain : Fin (n + 1) → Subrepresentation σ,
    chain 0 = ⊥ ∧ chain (Fin.last n) = ⊤ ∧
    (∀ i : Fin n, chain i.castSucc ⋖ chain i.succ) ∧
    Nat.card {i : Fin n // ∃ g : J, ∃ v,
      sectionRepresentation σ (chain i.castSucc) (chain i.succ) g v ≠ v} = 2

open scoped Pointwise

/-- All of 13.8.5(1)–(3), with the source group and module alternatives linked. -/
def FullModelConclusions (L L₁ T : Subgroup G) (hL₁ : L₁ ≤ H)
    (Q : CenterQuotientAction H U Z) : Prop :=
  (∃ K : Subgroup H, K.IsCComponent ∧
    (H : Set G) = (K.map H.subtype : Set G) * (T : Set G)) ∧
  ((Nonempty (StarModuleModel Q (BinaryPermutation.naturalRepresentation (Fin 6))) ∨
      Nonempty (StarModuleModel Q (BinaryPermutation.coreRepresentation (Fin 6)))) ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      TwoNoncentralChiefFactors ((literalRepresentation Q).comp (inclusion hL₁)) ∨
    (Nonempty (StarModuleModel Q (BinaryPermutation.coreRepresentation (Fin 7))) ∨
      (Nonempty (StarModuleModel Q linearFourRepresentation) ∧
        Nonempty (Source.Hstar H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)))) ∧
      SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.Reorientation
end
