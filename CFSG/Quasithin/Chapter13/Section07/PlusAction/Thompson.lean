module

public import CFSG.Quasithin.Chapter13.Section07.PlusAction.PrimitiveAlternatives
public import Theory.GroupTheory.ReducedNormal.RelativeDetection

/-!
# Thompson reduced witnesses inside the original plus kernel

For a nontrivial normal two-perfect subgroup K of the plus kernel,
C_K(U0)=O₂(K). Thompson A×B therefore provides a reduced elementary
subgroup of U0 with that same detecting centralizer. The construction
works in every actual overgroup X between KT and H, in particular the
source X=KL₁T. Thus X/C_X(W) has trivial two-core; this is a conclusion
of the original subgroup calculation, not an imposed faithful quotient.

The later irreducible choice and B.5.6 module exclusion are distinct.
Source: Aschbacher--Smith13.7.4(1), printed p.938.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07.PlusAction
open ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G]
    {D : ChapterF.Section09.Setup G}

/-- Thompson's theorem applied inside the actual intermediate actor X.
Its reduced quotient retains the literal X-centralizer of the witness. -/
theorem normal_kernel_reduced_witness
    (h : D.Hypothesis) (hE : IsElementaryAbelian 2 D.UH)
    {K X : Subgroup G} (hKC : K ≤ kernel D)
    (hKn : D.H ≤ normalizer (K : Set G))
    (hp : IsPPerfect 2 K) (hne : K ≠ ⊥)
    (hKX : K ≤ X) (hTX : (D.T : Subgroup G) ≤ X) (hXH : X ≤ D.H) :
    ∃ W : Subgroup X, W ≤ (fixedLayer D).subgroupOf X ∧ IsPReduced 2 W ∧
      K ⊓ centralizer (W.map X.subtype : Set G) = K.pCoreIn 2 ∧
      ⁅W.map X.subtype, K⁆ ≠ ⊥ := by
  let : IsElementaryAbelian 2 D.UH := hE
  have hn : (K.subgroupOf D.H).Normal := normal_subgroupOf_of_le_normalizer hKn
  have hstructure := subnormal_kernel_structure h hKC hn.isSubnormal hp hne
  have hQT : D.QH ≤ (D.T : Subgroup G) := by
    change D.H.pCoreIn 2 ≤ (D.T : Subgroup G)
    have ht := pCoreIn_le_sylow D.H (D.T.subtype h.T_le_H)
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le h.T_le_H] using ht
  have hUX : fixedLayer D ≤ X := (inf_le_left.trans h.UH_le_QH).trans (hQT.trans hTX)
  obtain ⟨W, hW, hr, hc⟩ := exists_relative_reduced_le_centralizer_eq_core
    X K (fixedLayer D) hKX hUX (hXH.trans hKn)
    (hXH.trans (fixedLayer_normalized (D := D))) (IsElementaryAbelian.of_le inf_le_left)
    (subnormal_fixedLayer_centralizer h hKC hn.isSubnormal)
  refine ⟨W, hW, hr, hc, ?_⟩
  intro hz
  have hKW : K ≤ centralizer (W.map X.subtype : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
  have hKcore : K ≤ K.pCoreIn 2 := (le_inf le_rfl hKW).trans hc.le
  exact hstructure.2.1 (commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp (hKcore.trans hstructure.2.2.2.2)))

end CFSG.Quasithin.Chapter13.Section07.PlusAction

namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion PlusAction
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- Apply the Thompson step to the actual source actor KL₁T. -/
theorem source_plus_thompson_witness
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    {K : Subgroup G}
    (hKC : K ≤ kernel (ConjugateIntersections.sourceSetup T L V V₃ V₁ H))
    (hKn : H ≤ normalizer (K : Set G)) (hp : IsPPerfect 2 K) (hne : K ≠ ⊥) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let X := K ⊔ (F.L₁ ⊔ (T : Subgroup G))
    ∃ W : Subgroup X, W ≤ (fixedLayer F).subgroupOf X ∧ IsPReduced 2 W ∧
      K ⊓ centralizer (W.map X.subtype : Set G) = K.pCoreIn 2 ∧
      ⁅W.map X.subtype, K⁆ ≠ ⊥ := by
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let : IsElementaryAbelian 2 V := NaturalAction.elementary d
  let : IsElementaryAbelian 2 V₃ := IsElementaryAbelian.of_le d.seed_le
  let : IsMulCommutative (conjugateSpanBy V₃ H) := hU
  exact normal_kernel_reduced_witness h (conjugateSpanBy_elementary_of_commutative V₃ H)
    hKC hKn hp hne le_sup_left (le_sup_right.trans le_sup_right)
    (sup_le (hKC.trans (kernel_le_H (D := F))) h.local_le)

/-- A nonfaithful original plus action constructs a nontrivial normal
residual and a reduced detecting witness inside its actual KL₁T actor.
No normal-subgroup or reduced-module witness is an additional input. -/
theorem source_plus_reduced_of_not_faithful
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    {A : Type*} [AddCommGroup A] [Module (ZMod 2) A]
    {σ : Representation (ZMod 2) (H ⧸ pCore 2 H) A}
    (s : Representation.BinaryConjugationSection H (Section08.Source.UH H V₃)
      ((Section08.Source.UH H V₃) ⊓ centralizer (H.pCoreIn 2 : Set G))
      (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hσ : ¬ Function.Injective σ) :
    let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let K := kernelResidual F
    let X := K ⊔ (F.L₁ ⊔ (T : Subgroup G))
    K ≠ ⊥ ∧ K ≤ (σ.comp (QuotientGroup.mk' (pCore 2 H))).ker.map H.subtype ∧
      H ≤ normalizer (K : Set G) ∧
      ∃ W : Subgroup X, W ≤ (fixedLayer F).subgroupOf X ∧ IsPReduced 2 W ∧
        K ⊓ centralizer (W.map X.subtype : Set G) = K.pCoreIn 2 ∧
        ⁅W.map X.subtype, K⁆ ≠ ⊥ := by
  dsimp only
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  have he := section_action_kernel (D := F) s
  have hCne : kernel F ≠ F.QH := he ▸ quotient_action_kernel_ne_core σ hσ
  have hKne := kernelResidual_ne_bot h hCne
  exact ⟨hKne, he.symm ▸ (kernelResidual_le (D := F)), (kernelResidual_normalized (D := F)),
    source_plus_thompson_witness d h hU (kernelResidual_le (D := F))
      (kernelResidual_normalized (D := F)) (kernelResidual_perfect (D := F)) hKne⟩

end CFSG.Quasithin.Chapter13.Section07
