module

public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.ActionTorus.Transport
public import CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction.ActionTorus.Actor

/-!
# Earlier source implications used by the action branch

Source: Aschbacher–Smith, E.2.11(4), E.2.13(7), E.2.14(7,9), printed
pp.224–228. These propositions specify universally quantified earlier-source
inputs; they are not axioms or proofs of those earlier results.

`E214RankClause` retains the strict quadratic-ratio hypothesis. Its consumer
must obtain that hypothesis on the literal restricted automizer. The torus
clause concerns a subgroup of the normal-core quotient, together with an
injective lift through its actual projection. This is the lift interpretation
of the source notation C_V(X*); it does not define an action of I* on V.
The input covers all subgroups of the stated order, as in the source, without
adding cyclicity. The action-image conclusion in 8.2.2(8) still requires the
independent odd-subgroup lifting and image comparison in `Transport`.

The universal producers remain qt-e-02, qt-e02-module-bounds and
qt-e02-ti-refinement. Final source assembly must discharge these inputs.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
open scoped IsMulCommutative
open Subgroup ChapterE Representation.BinaryOffender
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
variable {G : Type*} [Group G]

/-- The source TI property on the local maximal subgroup of H. -/
def LocalTI (H M V : Subgroup G) : Prop :=
  ∀ x ∈ M ⊓ H, V ⊓ V.map (MulAut.conj x).toMonoidHom = ⊥ ∨
    V.map (MulAut.conj x).toMonoidHom = V

/-- The normalizer equality of E.2.11(4), inside the actual selected I. -/
def E211NormalizerClause [Finite G] (K : GroupClass) : Prop :=
  ∀ (H T M V I : Subgroup G) (k : ℕ), HypothesisE28 K H T M V →
    Family H T M V I k → ∀ (i : I),
    V ⊔ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom = I →
    ∀ (S : Sylow 2 I),
    TwoConjugate.Hypotheses S (V.subgroupOf I) (M.subgroupOf I) i⁻¹ →
    TwoConjugate.A (V.subgroupOf I) (M.subgroupOf I) i⁻¹ =
      TwoConjugate.W (V.subgroupOf I) i⁻¹ ⊓ normalizer (V.subgroupOf I : Set I)

/-- E.2.13(7) for P/Z intrinsic to I. Characteristic two is required of H,
not of the unrelated ambient G. -/
def E213SectionClause [Finite G] (K : GroupClass) : Prop :=
  ∀ (H T M V I : Subgroup G) (k : ℕ), HypothesisE28 K H T M V →
    Family H T M V I k → HasCharacteristicTwo H → ∀ (i : I),
    V ⊔ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom = I →
    ∀ (S : Sylow 2 I)
      (h : TwoConjugate.Hypotheses S (V.subgroupOf I) (M.subgroupOf I) i⁻¹),
    letI := h.Z_normal
    centralizerModulo ⊤ (TwoConjugate.P (V.subgroupOf I) (M.subgroupOf I) i⁻¹)
      (TwoConjugate.Z (V.subgroupOf I) i⁻¹) ≤ pCore 2 I

/-- The actor-rank consequence of the universal E.2.14(7) implication.
The actor and the representation use the same ambient V throughout. -/
def E214RankClause [Finite G] (K : GroupClass) : Prop :=
  ∀ (H T M V I : Subgroup G) (k : ℕ) (h28 : HypothesisE28 K H T M V),
    letI := h28.elementary
    Family H T M V I k → HasCharacteristicTwo H → LocalTI H M V →
    ∀ (i : I), V ⊔ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom = I →
    V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ≠ ⊥ →
    1 < quadraticRatio ((automizerRepresentation V).comp (inducedAutomizer V I).subtype) →
    let A := V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype
    rank (inducedAutomizer V A) ≤ 2 * k → rank (inducedAutomizer V A) = 2 * k

/-- E.2.14(9) on quotient tori and their actual injective lifts. The model
hypothesis is a genuine group isomorphism; no abstract family tag is used. -/
def E214TorusClause [Finite G] (K : GroupClass) : Prop :=
  ∀ (H T M V I : Subgroup G) (k : ℕ), HypothesisE28 K H T M V →
    Family H T M V I k → HasCharacteristicTwo H → LocalTI H M V →
    ∀ (i : I), V ⊔ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom = I →
    V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom ≠ ⊥ →
    (Nonempty (Star M I ≃* PSL2 (BinaryGaloisField k)) ∨
      ∃ m : ℕ, 0 < m ∧ k = 2 * m + 1 ∧ Nonempty (Star M I ≃* SuzukiMatrixGroup m)) →
    1 < k → ∀ (Xstar : Subgroup (Star M I)), Xstar ≤ starImage M I M →
    Nat.card Xstar = 2 ^ k - 1 → ∀ (D : Subgroup ↥(M ⊓ I)),
    D.map (selectedStarMap M I) = Xstar →
    Function.Injective ((selectedStarMap M I).comp D.subtype) →
    V ⊓ centralizer (D.map (M ⊓ I).subtype : Set G) =
      V ⊓ V.map (MulAut.conj (i.val)⁻¹).toMonoidHom

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Construction
