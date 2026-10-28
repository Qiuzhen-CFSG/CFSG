module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Support.Normalizer
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed.Projection
public import Theory.SpecificGroups.AlternatingFiveBorelProjection.PermutationAction
/-!
# Noncentrality of the actual residual on an A₅ constituent

If K⁺ and Lᵥ⁺ commute, faithfulness of S₅ conjugation on A₅ makes Lᵥ⁺
act trivially on the marked natural constituent. Its equality with U_K then
contradicts the genuine commutator nonvanishing of 13.6.11. All maps are the
original plus quotient maps; no abstract alternate actor is used.
Source: Aschbacher–Smith, 13.6.15, printed p.930.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed
open ComponentSelection ChapterB.QuasisimpleSource SourceContainment SourceContainment.LinearThree
open SourceContainment.LinearThree.CentralAction.ModuleAlternatives
variable {G : Type*} [Group G]
theorem plus_commutator_ne_bot (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (I : Subrepresentation (componentRepresentation K L T z v hL hz))
    (e : ActionEquiv I.toRepresentation (alternatingNatural 5))
    (hm : I.toSubmodule = moved (wkRepresentation K L T z v hL hz) (plusImage K L T z v hL hz K))
    (r : Gplus K L T z v hL hz →* Equiv.Perm (Fin 5))
    (hr : ∀ c : plusImage K L T z v hL hz K, r c = (e.groupEquiv c).val)
    (he : ∀ g (w : I.toSubmodule), wkRepresentation K L T z v hL hz g w =
      (e.linearEquiv.symm (BinaryPermutation.naturalRepresentation (Fin 5) (r g) (e.linearEquiv w)) : Additive (WK K L T z v)))
    (hUK : ⁅UK K L T z v,Lv L v⁆ ≠ ⊥) :
    ⁅plusImage K L T z v hL hz K,plusImage K L T z v hL hz (Lv L v)⁆ ≠ ⊥ := by
  intro hc
  have ht : ∀ l, r (residualPlusMap K L T z v hL hz l)=1 := by
    intro l
    have hf (l : Lv L v) (c : plusImage K L T z v hL hz K) :
        ((1 : Lv L v →* plusImage K L T z v hL hz K) l : Gplus K L T z v hL hz)*c*
          (((1 : Lv L v →* plusImage K L T z v hL hz K) l : Gplus K L T z v hL hz))⁻¹ =
        residualPlusMap K L T z v hL hz l*c*(residualPlusMap K L T z v hL hz l)⁻¹ := by
      have hq : residualPlusMap K L T z v hL hz l ∈ plusImage K L T z v hL hz (Lv L v) := by
        rw [← residualPlusMap_range]; exact ⟨l,rfl⟩
      have hh := mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp hc) c.property) _ hq
      simp only [MonoidHom.one_apply, Subgroup.coe_one, one_mul, inv_one, mul_one]
      rw [hh,mul_assoc,mul_inv_cancel,mul_one]
    simpa using AlternatingFiveProjection.permutation_eq_projection _ e.groupEquiv r hr
      (residualPlusMap K L T z v hL hz) 1 hf l
  apply hUK
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro u hu
  apply mem_centralizer_iff.mpr
  intro l hl
  let w : Additive (WK K L T z v) := Additive.ofMul ⟨u,UK_le_WK K L T z v hL hz hu⟩
  have hw : w ∈ I.toSubmodule := by
    rw [hm,moved_eq_ukSubspace]; exact hu
  have hh := he (residualPlusMap K L T z v hL hz ⟨l,hl⟩) ⟨w,hw⟩
  rw [ht,map_one,Module.End.one_apply,e.linearEquiv.symm_apply_apply] at hh
  have hval := congrArg (fun x : Additive (WK K L T z v) => (x.toMul : G)) hh
  change l*u*l⁻¹=u at hval
  exact mul_inv_eq_iff_eq_mul.mp hval
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.Replacement.NaturalRecognition.AlternatingSeed
