module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.IntrinsicCore
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Recognition
public import Theory.SpecificGroups.G2.MultiplierTwoGroup

/-!
# The marked higher-field G₂ action with its kernel discharged

The actual marking K⁺ ≃ G₂(F) supplies three-rank two. The universal A.3.6
theorem, applied in the genuine local two-core quotient, then makes K/O₂(K)
quasisimple. The canonical G₂ universal kernel is a two-group, including
at |F| = 4. Consequently the literal action kernel C_K(W_K) is O₂(K).

The complete adequate B.5 alternatives recognize [W_K,K]/C_[W_K,K](K)
as the six-dimensional octonion quotient representation. Applying the
parabolic construction retains this intertwiner, conjugating its group
and linear coordinates together to align Tᵥ ∩ K with a standard Sylow
subgroup. Movement of z follows from Y_z and the invariance in 13.6.14.
The fixed kernel of the moved-space projection is retained throughout.

The universal A.3.6 and B.5 implications, U_v containment, elementary
abelian W_K and the R₂ consequence O₂(G⁺)=1 are genuine earlier-source
inputs. Their discharge remains with `qt-13-06-centralizer-reduction`
(A.3.6 is produced by `qt-a03-sqtk-structure`). The final G₂ exclusion
remains with `qt-13-06-higher-field-g2-parabolics`. There is no additional
intrinsic-quasisimplicity, multiplier, action-kernel or natural-marking premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the paragraph
preceding 13.6.14 and Lemma 13.6.19, printed pp.929–931; A.3.6, pp.43–45;
B.5.1 and B.5.6, pp.99 and 105; I.1.1–I.1.4, pp.407–408.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Assembly
open ComponentSelection Chapter1.Section02 ChapterB.QuasisimpleSource ChapterB.SourceInduction

universe u
variable {G : Type u} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
variable {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D], IsSQTK κ D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)

include hG hA36 in
/-- The literal relative action kernel is exactly O₂(K). The proof allows
the exceptional two-primary covering kernel over the field of order four. -/
theorem relativeKernel_eq_twoCore {F : Type*} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (mark : plusImage K L T z v hL hz K ≃* Atlas.G2.Model F) :
    (centralizer (WK K L T z v : Set G)).subgroupOf K = pCore 2 K := by
  let := IntrinsicCore.isQuasisimple K L T z v hL hz hG hA36 hF hv hK mark
  have hq : 2 < Nat.card F := by
    have hp : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
    omega
  let : Fact (2 < Nat.card F) := ⟨hq⟩
  exact KernelReduction.relativeKernel_eq_twoCore K L T z v hL hz hK hR mark
    (Atlas.G2.FiniteCover.universalKernel_isPGroup_of_card_pow hF hm)

include hG hA36 in
/-- Discharge the exact action-kernel premise of the published G₂ parabolic
construction, using the actual plus-to-model equivalence. -/
theorem relativeKernel_isPGroup {F : Type*} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (mark : plusImage K L T z v hL hz K ≃* Atlas.G2.Model F) :
    IsPGroup 2 ((centralizer (WK K L T z v : Set G)).subgroupOf K) := by
  rw [relativeKernel_eq_twoCore K L T z v hL hz hG hA36 hF hm hv hK hR mark]
  exact pCore_isPGroup

open scoped MatrixGroups

include hG hA36 in
/-- The higher-field source inputs produce the actual natural intertwiner and
a moving nonshort maximal parabolic. Both the module marking and the literal
action-kernel condition are discharged, including the field-four case. -/
theorem exists_moving_nonshort_parabolic
    [IsElementaryAbelian 2 (WK K L T z v)]
    (classification : AdequateClassificationInput.{u,u} κ)
    (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hU : Uv z v ≤ Tv T v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    {F : BinaryField} (hF : 1 < F.degree)
    (mark : plusImage K L T z v hL hz K ≃* Atlas.G2.Model F.Carrier) :
    ∃ (a : NaturalMarking K L T z v hL hz F) (i : Fin 2),
      let P := liftedParabolic K L T z v hL hz a.groupEquiv i
      P ≤ Gv v ∧ P ≤ K ∧ Tv T v ⊓ K ≤ P ∧ IsCoatom (P.subgroupOf K) ∧
        ¬ residualIn P ≤ centralizer ({z} : Set G) ∧
        ¬ ChapterC.IsShort (residualIn P) ∧
        Nonempty ((residualIn P ⧸ pCore 2 (residualIn P)) ≃* PSL(2,F.Carrier)) ∧
        Nonempty ((plusImage K L T z v hL hz (residualIn P) ⧸
          pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2,F.Carrier)) := by
  exact Recognition.exists_moving_nonshort_parabolic_of_source K L T z v hL hz
    classification hK hn hU (hG.involution_centralizer_sqtk hv) hR hF mark
    (relativeKernel_isPGroup K L T z v hL hz hG hA36 F.card_eq hF hv hK hR mark)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.Assembly
