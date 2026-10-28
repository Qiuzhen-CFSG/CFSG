module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.SourceCoreAction
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Core.Quotient
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.LinearThree.Input

/-!
# The actual pure-point MS core is too large to be abelian

Both original moved summands lie in the commutator core: the natural
four-space and the dual polar three-space. They are disjoint and have
product order 128. The genuine abelian binary MS theorem permits only
orders 8, 16 or 64, so the same actual core is nonabelian.
This uses neither a universal MS classification nor an ambient Sylow claim.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {B : DoubledBranch T L V 4}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

include S in
/-- The literal MS commutator core contains the original moved subgroup
of order 128. -/
theorem pure_msCore_card_ge_128
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0) :
    128 ≤ Nat.card (msQ (B.pointResidual w) (B.pointSylow w)) := by
  let W := componentOrbit V (T : Subgroup G)
  let X := B.pointResidual w
  let R := B.pointSylow w
  let J := X ⊔ R
  have hWR : W ≤ R := by
    intro x hx
    exact ⟨hWT hx, mem_centralizer_singleton_iff.mpr (W.le_centralizer hx w w.property).symm⟩
  have hJM : J ≤ normalizer (L : Set G) :=
    sup_le (B.pointResidual_le_normalizer w) (inf_le_left.trans hTM)
  have hWQ : W ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 W) (hWR.trans le_sup_right) (hNM.symm ▸ hJM)
  obtain ⟨hN, hD⟩ := S.pure_residual_commutators hNM w hw hp
  have hle : B.naturalSummand ⊔ S.pureDualHyperplane w hp ≤ msQ X R := by
    apply sup_le
    · rw [← hN]
      exact commutator_mono (B.naturalSummand_le.trans hWQ) le_rfl
    · rw [← hD]
      exact commutator_mono (B.dualSummand_le.trans hWQ) le_rfl
  have hc := card_le_of_le hle
  rw [S.pure_moving_card w hw hp] at hc
  exact hc

include S in
/-- The genuine abelian binary core theorem excludes the abelian branch
for this same pure-point source. -/
theorem pure_msCore_nonabelian
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0)
    (hms : SmallMSPair KnownSimple.IsKnownSimple (B.pointResidual w) (B.pointSylow w))
    (e : (B.pointResidual w ⧸ pCore 2 (B.pointResidual w)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ¬ IsMulCommutative (msQ (B.pointResidual w) (B.pointSylow w)) := by
  intro hc
  have hl := S.pure_msCore_card_ge_128 hNM hWT hTM w hw hp
  obtain ⟨d, hd, ⟨f⟩⟩ := hms.abelian_msQ_model e hc
  have hf : Nat.card (msQ (B.pointResidual w) (B.pointSylow w)) = 2 ^ d := by
    rw [Nat.card_congr f.toEquiv]
    change Nat.card (Fin d → ZMod 2) = _
    simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  rcases hd with rfl | rfl | rfl <;> norm_num at hf <;> omega

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
