module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Nonsplit.Perfect
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Nonsplit.CentralCover
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Nonsplit.ModuleObstruction
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Nonsplit.Linear
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Nonsplit.Witness
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Action
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Comparison.ModelFacts.ThreeCovers.CentralExtension

/-!
# Nonsplitting and B.4.8 fusion for the actual HS covering normalizer

Transfer makes M perfect. A complement to the literal central line in Qbar
would make M/[Q,M] a perfect central double cover of SL₃(2), hence SL₂(7).
The constructed two-central involution outside Q contradicts the unique
involution of that cover. The natural quotient then gives indecomposability.

The genuine universal B.4.8(2) is applied only after proving faithfulness,
dimension four, indecomposability, and compatibility of the supplied natural
central quotient. Its fixed-displacement conclusion feeds the literal
coset-fusion theorem and conjugacy into O₂(O²(C_K(u))).

This completes the conditional contract of qt-i22-hs-normalizer-nonsplit-fusion.
Model perfectness, odd index and the concrete witness come from
qt-i22-hs-normalizer-model-geometry. The core decomposition, Frattini order,
central disjointness, natural quotient and E≤R come from
qt-i22-hs-normalizer-abelian-section. The earlier residual-image equality is
owned by qt-i22-hs-centralizer-restriction. EarlierB48Two is the full universal
source input owned by qt-b-04-natural-extensions. The final normalizer/HS
assembly must discharge these independent premises; this is not an
unconditional proof of I.2.2(5).

Source: Aschbacher–Smith I.2.2(5), printed p.412 / PDF p.423, and B.4.8(2),
printed p.91 / PDF p.102, combined manuscript of 1 March 2004.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Nonsplit
open Sporadic.LeechRelated.HS.BlockNormalizer
open Theory.GroupTheory.DoubleCoverCentralizer
open CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions.ThreeCovers.CentralExtension
universe u
variable {K : Type u} [Group K] [Finite K]

theorem frattiniRepresentation_nonsplit [Group.IsPerfect K]
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2)
    (hperfect : Group.IsPerfect baseNormalizer) (hindex : ¬ 2 ∣ baseNormalizer.index)
    (hZE : Disjoint (localMap e).ker (E e))
    (Y : Subgroup (M e)) (hgen : ⁅Q e, Y⁆ ⊔ (localMap e).ker = Q e)
    (j : M e) (hj : j ^ 2 = 1) (hjQ : j ∉ Q e)
    (W : Subrepresentation (frattiniRepresentation e)) :
    ¬ IsCompl (frattiniRepresentation e).invariants W.toSubmodule := by
  let : Group.IsPerfect (M e) := M_isPerfect e hZ hperfect hindex
  have hkQ : (localMap e).ker ≤ Q e := by
    rw [localMap_ker]
    exact center_le_Q e hZ
  have hgen' : ⁅Q e, ⊤⁆ ⊔ (localMap e).ker = Q e := by
    apply le_antisymm (sup_le (commutator_le_left _ _) hkQ)
    exact hgen.ge.trans (sup_le_sup (commutator_mono le_rfl le_top) le_rfl)
  have hkcentral : (localMap e).ker ≤ center (M e) := by
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_center_iff.mp (show (x : K) ∈ center K by rwa [localMap_ker] at hx) y
  intro hW
  exact not_disjoint_commutator_center (Q e) (localMap e).ker hkcentral
    ((localMap_ker_card e).trans hZ) hgen' (normalizerQuotientEquiv e hZ) j hj hjQ
    (disjoint_commutator_kernel_of_complement e hZE W hW)

/-- The actual four-dimensional section has a one-dimensional fixed space,
because its specified natural quotient has dimension three. -/
theorem frattini_invariants_finrank
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (hE : Nat.card (E e) = 8)
    (hnatural : ActionEquiv (reducedAction (frattiniRepresentation e))
      (linearNatural BinaryField.two 3)) :
    Module.finrank (ZMod 2) (frattiniRepresentation e).invariants = 1 := by
  have hd := frattiniRepresentation_finrank e hZ hE
  have hN : Module.finrank (ZMod 2)
      (Additive (Qbar e) ⧸ (frattiniRepresentation e).invariants) = 3 := by
    exact hnatural.linearEquiv.finrank_eq.trans
      (by simp [BinaryField.two])
  have h := Submodule.finrank_quotient_add_finrank (frattiniRepresentation e).invariants
  omega

/-- Faithfulness, dimension and indecomposability are all proved for the
actual action before the universal earlier-source B.4.8(2) is applied. -/
theorem frattiniRepresentation_displacement [Group.IsPerfect K]
    (h48 : EarlierB48Two.{u,u})
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2)
    (hperfect : Group.IsPerfect baseNormalizer) (hindex : ¬ 2 ∣ baseNormalizer.index)
    (hZE : Disjoint (localMap e).ker (E e))
    (Y : Subgroup (M e)) (hgen : ⁅Q e, Y⁆ ⊔ (localMap e).ker = Q e)
    (hE : Nat.card (E e) = 8)
    (hnatural : ActionEquiv (reducedAction (frattiniRepresentation e))
      (linearNatural BinaryField.two 3))
    (j : M e) (hj : j ^ 2 = 1) (hjQ : j ∉ Q e) :
    IsIndecomposable (frattiniRepresentation e) ∧
    ∀ a : M e ⧸ Q e, orderOf a = 2 →
      ∀ v : Additive (Qbar e), frattiniRepresentation e a v = v →
        ∃ w : Additive (Qbar e), frattiniRepresentation e a w - w = v := by
  have hd := frattiniRepresentation_finrank e hZ hE
  have hline := frattini_invariants_finrank e hZ hE hnatural
  have hi := indecomposable_of_no_fixed_complement (frattiniRepresentation e) hline hnatural
    (frattiniRepresentation_nonsplit e hZ hperfect hindex hZE Y hgen j hj hjQ)
  obtain ⟨_, _, _, ht⟩ := h48 (M e ⧸ Q e) (Additive (Qbar e))
    (frattiniRepresentation e) (frattiniRepresentation_injective e hZ) hi hd hnatural
  exact ⟨hi, fun a ha v hv =>
    displacement_of_moved_eq_fixed (frattiniRepresentation e) a ha (ht a ha).1 v hv⟩

/-- The conditional HS normalizer theorem: model geometry and the abelian
section are explicit inputs, and all nonsplitting and fusion steps are discharged. -/
theorem nonsplit_and_fusion [Group.IsPerfect K]
    (h48 : EarlierB48Two.{u,u})
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2)
    (hperfect : Group.IsPerfect baseNormalizer) (hindex : ¬ 2 ∣ baseNormalizer.index)
    (u : K)
    (hXmap : (Theory.GroupTheory.centralizerTwoResidual u).map (modelMap e) =
      Theory.GroupTheory.centralizerTwoResidual (modelMap e u))
    (j₀ : baseNormalizer) (hj₀ : orderOf j₀ = 2)
    (hj₀c : TwoCentral (j₀ : Sporadic.LeechRelated.HS.Carrier))
    (hj₀R : (j₀ : Sporadic.LeechRelated.HS.Carrier) ∈ centralizerCore (modelMap e u))
    (hj₀Q : j₀ ∉ pCore 2 baseNormalizer)
    (hZE : Disjoint (localMap e).ker (E e))
    (Y : Subgroup (M e)) (hgen : ⁅Q e, Y⁆ ⊔ (localMap e).ker = Q e)
    (hE : Nat.card (E e) = 8)
    (hER : E e ≤ (centralizerCore u).subgroupOf (M e))
    (hnatural : ActionEquiv (reducedAction (frattiniRepresentation e))
      (linearNatural BinaryField.two 3)) :
    Group.IsPerfect (M e) ∧
    centralLine e = (frattiniRepresentation e).invariants ∧
    (∀ W : Subrepresentation (frattiniRepresentation e),
      ¬ IsCompl (centralLine e) W.toSubmodule) ∧
    IsIndecomposable (frattiniRepresentation e) ∧
    ∃ j : M e, (j : K) ∈ centralizerCore u ∧ orderOf j = 2 ∧
      localMap e j = j₀ ∧ orderOf (QuotientGroup.mk' (Q e) j) = 2 ∧
      orderOf (QuotientGroup.mk' (E e) j) = 2 ∧
      (∀ a : M e ⧸ Q e, orderOf a = 2 → ∃ m : M e,
        QuotientGroup.mk' (Q e) m * a * (QuotientGroup.mk' (Q e) m)⁻¹ =
          QuotientGroup.mk' (Q e) j) ∧
      (∀ v : Additive (Qbar e),
        frattiniRepresentation e (QuotientGroup.mk' (Q e) j) v = v →
        ∃ w : Additive (Qbar e),
          frattiniRepresentation e (QuotientGroup.mk' (Q e) j) w - w = v) ∧
      (∀ x : M e, x ^ 2 = 1 → x ∉ Q e →
        ∃ y ∈ centralizerCore u, IsConj (x : K) y) := by
  obtain ⟨j, hjR, hj2, hjlocal, hjQ, hjmodQ, hjmodE⟩ :=
    exists_core_involution e hZ u hXmap j₀ hj₀ hj₀c hj₀R hj₀Q
  have hjsquare : j ^ 2 = 1 := by simpa only [hj2] using pow_orderOf_eq_one j
  obtain ⟨hi, hf⟩ := frattiniRepresentation_displacement h48 e hZ hperfect hindex
    hZE Y hgen hE hnatural j hjsquare hjQ
  have hcentral := centralLine_eq_invariants e hZ hZE
    (frattini_invariants_finrank e hZ hE hnatural)
  have hn : ∀ W : Subrepresentation (frattiniRepresentation e),
      ¬ IsCompl (centralLine e) W.toSubmodule := by
    rw [hcentral]
    exact frattiniRepresentation_nonsplit e hZ hperfect hindex hZE Y hgen j hjsquare hjQ
  exact ⟨M_isPerfect e hZ hperfect hindex, hcentral, hn,
    hi, j, hjR, hj2, hjlocal, hjmodQ, hjmodE,
    fun a ha => quotient_involutions_conjugate e hZ a _ ha hjmodQ,
    hf _ hjmodQ,
    conjugate_into_core_of_displacement e hZ u j hjR hjmodQ hjmodE hER (hf _ hjmodQ)⟩
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Nonsplit
