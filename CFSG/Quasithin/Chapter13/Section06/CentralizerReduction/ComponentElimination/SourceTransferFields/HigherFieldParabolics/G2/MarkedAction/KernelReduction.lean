module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction
public import Theory.SpecificGroups.G2.MultiplierFourTwoGroup

/-!
# Lifting the literal G₂ action kernel through the intrinsic two-core

The source R₂ condition kills O₂(K) in the plus action. The resulting marked
map from K/O₂(K) is surjective, and its kernel pulls back to C_K(W_K).
If the intrinsic quotient is quasisimple, this precise map is a covering.
A two-group universal multiplier then makes C_K(W_K) exactly O₂(K).
This permits the exceptional central two-cover at q=4.

The field-four multiplier premise is discharged by the actual odd-primary
calculations. The general parabolic application retains the marked moved
quotient while replacing its action-kernel premise by these covering inputs.
Intrinsic quasisimplicity is still a source obligation: Y_z only states
quasisimplicity of K*/O₂(K*), which is a different quotient. The larger-field
multiplier calculation also remains explicit. These conditional deductions
are not a proof of the complete source branch.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the paragraph preceding 13.6.14 and 13.6.19, pp.929–931;
I.1.3–I.1.4 for the genuine covering kernels, pp.407–408.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.KernelReduction
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]
variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v)
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)

include hK hR in
/-- The source R₂ condition kills O₂(K) in the actual plus map. -/
theorem twoCore_le_componentMap_ker : pCore 2 K ≤ (componentMap K L T z v hL hz).ker := by
  have ht : pCore 2 (plusImage K L T z v hL hz K) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (plusImage_K_subnormal K L T z v hL hz hK), hR]
    exact (MonoidHom.ker_eq_bot_iff _).mpr
      (plusImage K L T z v hL hz K).subtype_injective
  have hn : ((pCore 2 K).map (componentMap K L T z v hL hz)).Normal :=
    Subgroup.Normal.map inferInstance _ (componentMap_surjective K L T z v hL hz)
  have hle : (pCore 2 K).map (componentMap K L T z v hL hz) ≤
      pCore 2 (plusImage K L T z v hL hz K) :=
    le_sSup ⟨hn, pCore_isPGroup.map _⟩
  exact (Subgroup.map_eq_bot_iff _).mp (bot_unique (hle.trans ht.le))

variable {F : Type*} [Field F]
variable (e : plusImage K L T z v hL hz K ≃* Atlas.G2.Model F)

/-- The marked map from the intrinsic two-core quotient. No identification
of this quotient with the star quotient is assumed. -/
def coreQuotientMap : (K ⧸ pCore 2 K) →* Atlas.G2.Model F :=
  QuotientGroup.lift _ (modelMap K L T z v hL hz e) (by
    intro k hk
    change e (componentMap K L T z v hL hz k) = 1
    rw [show componentMap K L T z v hL hz k = 1 from
      twoCore_le_componentMap_ker K L T z v hL hz hK hR hk, map_one])

theorem coreQuotientMap_surjective :
    Function.Surjective (coreQuotientMap K L T z v hL hz hK hR e) :=
  QuotientGroup.lift_surjective_of_surjective _ _
    (modelMap_surjective K L T z v hL hz e) _

/-- Pulling back its kernel recovers the literal relative action kernel. -/
theorem coreQuotientMap_ker_comap :
    (coreQuotientMap K L T z v hL hz hK hR e).ker.comap (QuotientGroup.mk' (pCore 2 K)) =
      (centralizer (WK K L T z v : Set G)).subgroupOf K := by
  rw [MonoidHom.comap_ker]
  exact modelMap_ker K L T z v hL hz e

variable [Finite F] [Fact (2 < Nat.card F)]
variable [IsQuasisimple (K ⧸ pCore 2 K)]

/-- Under intrinsic quasisimplicity, this precise map is a genuine covering. -/
def coreCover : Covering (K ⧸ pCore 2 K) (Atlas.G2.Model F) where
  toMonoidHom := coreQuotientMap K L T z v hL hz hK hR e
  surjective := coreQuotientMap_surjective K L T z v hL hz hK hR e

include hK hR e in
/-- Only the two-primary property of the universal kernel is needed. A
nontrivial double cover at q=4 is permitted. Intrinsic quasisimplicity is a
separate source obligation; Y_z gives quasisimplicity of a different quotient. -/
theorem relativeKernel_isPGroup
    (hmult : IsPGroup 2 (Atlas.G2.FiniteCover.Kernel F)) :
    IsPGroup 2 ((centralizer (WK K L T z v : Set G)).subgroupOf K) := by
  have hp : IsPGroup 2 (coreQuotientMap K L T z v hL hz hK hR e).ker :=
    (coreCover K L T z v hL hz hK hR e).ker_isPGroup_of_universal
      (Atlas.G2.FiniteCover.cover F) (Atlas.G2.FiniteCover.cover_isUniversal F) hmult
  rw [← coreQuotientMap_ker_comap K L T z v hL hz hK hR e]
  exact hp.comap_of_ker_isPGroup _ (by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup)

include hK hR e in
/-- With the actual universal two-primary bound, the relative kernel is exactly
O₂(K). This retains central two-covers inside the intrinsic two-core. -/
theorem relativeKernel_eq_twoCore
    (hmult : IsPGroup 2 (Atlas.G2.FiniteCover.Kernel F)) :
    (centralizer (WK K L T z v : Set G)).subgroupOf K = pCore 2 K := by
  have hp := relativeKernel_isPGroup K L T z v hL hz hK hR e hmult
  rw [← componentMap_ker K L T z v hL hz] at hp ⊢
  exact le_antisymm (le_sSup ⟨inferInstance, hp⟩)
    (twoCore_le_componentMap_ker K L T z v hL hz hK hR)

include hK hR e in
/-- Field transport discharges the multiplier premise for any coefficient
field of order four, retaining the original plus-to-model marking. -/
theorem relativeKernel_of_card_four (hF : Nat.card F = 4) :
    IsPGroup 2 ((centralizer (WK K L T z v : Set G)).subgroupOf K) :=
  relativeKernel_isPGroup K L T z v hL hz hK hR e
    (Atlas.G2.FiniteCover.MultiplierFourBound.universalKernel_isPGroup_of_card_four hF)

include hK hR in
/-- At q=4 the covering-kernel premise is completely discharged. The remaining
intrinsic-quasisimple premise concerns K/O₂(K), not the star quotient. -/
theorem relativeKernel_four
    (e₄ : plusImage K L T z v hL hz K ≃* Atlas.G2.FiniteCover.FourBase) :
    IsPGroup 2 ((centralizer (WK K L T z v : Set G)).subgroupOf K) :=
  relativeKernel_isPGroup K L T z v hL hz hK hR e₄ Atlas.G2.FiniteCover.MultiplierFourBound.kernel_isPGroup

open ChapterB.QuasisimpleSource
open scoped MatrixGroups

include hK hR in
/-- Consumer of the exact covering reduction: the original kernel premise in
the parabolic theorem is replaced by intrinsic quasisimplicity and the actual
universal multiplier, while retaining the moved-quotient intertwiner. -/
theorem exists_moving_nonshort_parabolic_of_cover
    [IsElementaryAbelian 2 (WK K L T z v)]
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
  have hq : 2 < Nat.card B.Carrier := by
    rw [B.card_eq]
    have hh : 2 ^ 2 ≤ 2 ^ B.degree := Nat.pow_le_pow_right (by decide) hB
    omega
  let : Fact (2 < Nat.card B.Carrier) := ⟨hq⟩
  exact exists_moving_nonshort_parabolic_of_marking hB a hK hn
    (relativeKernel_isPGroup K L T z v hL hz hK hR a.groupEquiv hmult)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.HigherFieldParabolics.G2.MarkedAction.KernelReduction
