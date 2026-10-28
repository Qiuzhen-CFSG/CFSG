module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.KernelReduction
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication.Intrinsic
public import Theory.AtlasPort.LinearGroups.G2.EvenThreeRank

/-!
# Intrinsic quasisimplicity for the actual G₂ plus image

The marked surjection K → K⁺ ≃ G₂(F) forces the three-rank of K to be at
least two: otherwise its Sylow three-subgroups are cyclic, as are those of
every quotient, whereas the concrete characteristic-two G₂ model contains
an elementary abelian nine. The ambient SQTK bound makes this rank exactly
two. The existing intrinsic classification reduction then applies the
universal A.3.6 contract to the image of K in (KTᵥ)/O₂(KTᵥ). The natural
and nilpotent alternatives have three-rank at most one, leaving an ordinary
component. The checked two-core quotient equivalence gives quasisimplicity
of K/O₂(K), without identifying it with the star quotient in Y_z.

The kernel application retains the literal W_K and plus map and the R₂
consequence O₂(G⁺)=1. The parabolic application additionally retains
Tᵥ-invariance and the actual natural-action marking. The universal multiplier
and natural marking remain explicit independent inputs. The universal A.3.6
input is produced by task `qt-a03-sqtk-structure`; its earlier-source discharge
remains with `qt-13-06-centralizer-reduction`, and the full marked-action
assembly remains with `qt-13-06-g2-marked-action-kernel`.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the paragraph
preceding 13.6.14 and Lemma 13.6.19, pp.929–931; A.3.6, pp.43–45;
Proposition 1.2.1(4), p.504. The concrete elementary nine is the existing
attributed ATLAS-based construction in `G2.EvenThreeRank`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.IntrinsicCore
open ComponentSelection
open Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))

private theorem two_le_three_rank {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : plusImage K L T z v hL hz K ≃* Atlas.G2.Model F) :
    2 ≤ primeRank 3 K := by
  by_contra hr
  have hr1 : primeRank 3 K ≤ 1 := by omega
  let P : Sylow 3 K := Classical.choice inferInstance
  have hmodel := P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hr1)
    (modelMap K L T z v hL hz e) (modelMap_surjective K L T z v hL hz e)
  have htwo := Atlas.G2.EvenThreeRank.two_le_primeRank (K := F)
  omega

variable {κ : GroupClass.{u}} (hG : IsSimpleQTKE κ G)
    (hA36 : ∀ (D : Type u) [Group D] [Finite D], IsSQTK κ D → pCore 2 D = ⊥ →
      ∀ B : Subgroup D, B.IsCComponent → A36Conclusion B)

include hG hA36 in
/-- The actual G₂ marking supplies the rank hypothesis needed by the intrinsic
A.3.6 reduction. Only the binary field order is needed for this deduction;
the higher-field restriction enters the covering and parabolic applications. -/
theorem isQuasisimple {F : Type*} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (e : plusImage K L T z v hL hz K ≃* Atlas.G2.Model F) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hl := two_le_three_rank K L T z v hL hz e
  have hu : primeRank 3 K ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hK.1.1) (inclusion_injective hK.1.1)).trans
      ((hG.involution_centralizer_sqtk hv).stronglyQuasithin 3 (by decide) (by decide))
  exact (SourceContainment.RankTwo.LocalApplication.source_intrinsic_quasisimple
    hG hA36 K L T z v hv hK (le_antisymm hu hl)).1

include hG hA36 in
/-- Discharge intrinsic quasisimplicity in the exact relative action-kernel
reduction. The source R₂ consequence and universal multiplier stay explicit. -/
theorem relativeKernel_isPGroup {F : Type*} [Field F] [Finite F] {m : ℕ}
    (hF : Nat.card F = 2 ^ m) (hm : 1 < m)
    (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (e : plusImage K L T z v hL hz K ≃* Atlas.G2.Model F)
    (hmult : IsPGroup 2 (Atlas.G2.FiniteCover.Kernel F)) :
    IsPGroup 2 ((centralizer (WK K L T z v : Set G)).subgroupOf K) := by
  let := isQuasisimple K L T z v hL hz hG hA36 hF hv hK e
  have hq : 2 < Nat.card F := by
    rw [hF]
    have hp : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
    omega
  let : Fact (2 < Nat.card F) := ⟨hq⟩
  exact KernelReduction.relativeKernel_isPGroup K L T z v hL hz hK hR e hmult

open ChapterB.QuasisimpleSource
open scoped MatrixGroups

include hG hA36 in
/-- Apply the completed intrinsic step to the original higher-field G₂ branch,
retaining the moved-quotient intertwiner and Tᵥ-invariance. No intrinsic
quasisimplicity or action-kernel bound is an extra premise. -/
theorem exists_moving_nonshort_parabolic
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hv : orderOf v = 2) (hK : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (B : BinaryField) (hB : 1 < B.degree)
    (a : NaturalMarking K L T z v hL hz B)
    (hn : Tv T v ≤ normalizer (K : Set G))
    (hmult : IsPGroup 2 (Atlas.G2.FiniteCover.Kernel B.Carrier)) :
    ∃ (a' : NaturalMarking K L T z v hL hz B) (i : Fin 2),
      let P := liftedParabolic K L T z v hL hz a'.groupEquiv i
      P ≤ Gv v ∧ P ≤ K ∧ Tv T v ⊓ K ≤ P ∧ IsCoatom (P.subgroupOf K) ∧
        ¬ residualIn P ≤ centralizer ({z} : Set G) ∧
        ¬ ChapterC.IsShort (residualIn P) ∧
        Nonempty ((residualIn P ⧸ pCore 2 (residualIn P)) ≃* PSL(2,B.Carrier)) ∧
        Nonempty ((plusImage K L T z v hL hz (residualIn P) ⧸
          pCore 2 (plusImage K L T z v hL hz (residualIn P))) ≃* PSL(2,B.Carrier)) := by
  let := isQuasisimple K L T z v hL hz hG hA36 B.card_eq hv hK a.groupEquiv
  exact KernelReduction.exists_moving_nonshort_parabolic_of_cover
    K L T z v hL hz hK hR B hB a hn hmult

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.IntrinsicCore
