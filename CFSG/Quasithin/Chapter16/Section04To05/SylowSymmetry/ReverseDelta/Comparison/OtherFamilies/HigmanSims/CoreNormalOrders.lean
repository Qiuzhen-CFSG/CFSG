module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.SpecificGroups.SymmetricTwoResidual
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.HigmanSims.CoreNormalOrders.KernelContainment


/-!
# Normal subgroup orders in the core HS residual

For the actual central involution representative, the full pair kernel lies
in the two-residual by `KernelContainment`. The known S₅ quotient therefore
identifies that residual with the preimage of A₅; its order is 3840. A
nonsolvable normal subgroup has nontrivial, hence full, image in A₅. Its
ambient quotient is a two-group, so two-perfectness forces it to fill the
residual.

The existing exhaustive inner-class theorem transports this calculation to
an arbitrary inner involutory automorphism. The source core-extension shape
selects the correct class by its order, excluding the product centralizer of
order 2880. The only carrier hypotheses retained are the simplicity and
perfectness supplied by the consumer's actual quasisimple quotient.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 16.1.5(10),
printed p.1172, and its use in the comparison in 16.4.11(2), printed p.1193.
This module supplies the core row of the HS exclusion; the product row and
final exclusion are assembled separately.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open HSInner
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralNormalizerThreePart.PairQuotient

namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
open HSCoreNormalOrders

private theorem normal_eq_top_of_simple_image {G D : Type*} [Group G] [Finite G]
    [Group D] [IsSimpleGroup D] (f : G →* D) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) (hG : IsPPerfect 2 G)
    (N : Subgroup G) [N.Normal] (hN : ¬ Group.IsSolvable N) : N = ⊤ := by
  have hn : (N.map f).Normal := (inferInstance : N.Normal).map f hf
  rcases hn.eq_bot_or_eq_top with h | h
  · have hle : N ≤ f.ker := (map_eq_bot_iff N).mp h
    let : Group.IsNilpotent N := (hk.to_le hle).isNilpotent
    exact (hN inferInstance).elim
  · have hsup : N ⊔ f.ker = ⊤ := by
      rw [← comap_map_eq, h, comap_top]
    exact hG N inferInstance (isPGroup_quotient_of_sup_eq_top N f.ker hk hsup)

private theorem local_residual_image :
    (pResidual 2 (localGroup 0)).map fiveHom = alternatingGroup (Fin 5) := by
  rw [map_pResidual_of_surjective 2 fiveHom fiveHom_surjective,
    Equiv.Perm.twoResidual_eq_alternating]


private theorem local_residual_eq :
    pResidual 2 (localGroup 0) = (alternatingGroup (Fin 5)).comap fiveHom := by
  rw [← local_residual_image]
  exact (comap_map_eq_self (by rw [fiveHom_kernel]; exact core_le_residual)).symm

private theorem local_residual_card : Nat.card (pResidual 2 (localGroup 0)) = 3840 := by
  have hc : Nat.card (localGroup 0) = 7680 := by
    rw [localGroup_zero_eq_centralizer]
    exact centralizer_card
  have hi : (pResidual 2 (localGroup 0)).index = 2 := by
    rw [local_residual_eq, index_comap_of_surjective _ fiveHom_surjective,
      alternatingGroup.index_eq_two]
  have hm := (pResidual 2 (localGroup 0)).card_mul_index
  rw [hi, hc] at hm
  omega

private theorem local_normal_eq_top (N : Subgroup (pResidual 2 (localGroup 0)))
    [N.Normal] (hN : ¬ Group.IsSolvable N) : N = ⊤ := by
  let R := pResidual 2 (localGroup 0)
  let f := fiveHom.subgroupMap R
  let : IsSimpleGroup (R.map fiveHom) := by
    change IsSimpleGroup ((pResidual 2 (localGroup 0)).map fiveHom)
    rw [local_residual_image]
    infer_instance
  have hk : f.ker = core.subgroupOf R := by
    ext x
    rw [MonoidHom.mem_ker, Subtype.ext_iff]
    change fiveHom x.val = 1 ↔ x.val ∈ core
    rw [← fiveHom_kernel]
    rfl
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    exact core_isPGroup.comap_subtype
  exact normal_eq_top_of_simple_image f (fiveHom.subgroupMap_surjective R) hp
    (isPPerfect_pResidual 2) N hN

private noncomputable def residualEquiv {C D : Type*} [Group C] [Group D]
    (e : C ≃* D) : pResidual 2 C ≃* pResidual 2 D :=
  (e.subgroupMap (pResidual 2 C)).trans (MulEquiv.subgroupCongr (map_pResidual 2 e))

private theorem core_fixed_equiv [IsSimpleGroup Carrier] [Group.IsPerfect Carrier]
    (a : MulAut Carrier) (ha : orderOf a = 2) (hi : ∃ x, a = MulAut.conj x)
    (hc : IsHSCoreExtension a.fixedSubgroup) :
    Nonempty (a.fixedSubgroup ≃* localGroup 0) := by
  rcases inner_fixed_representatives ClassCoverage.involution_alternative a ha hi with he | he
  · obtain ⟨e⟩ := he
    exact ⟨e.trans (MulEquiv.subgroupCongr localGroup_zero_eq_centralizer.symm)⟩
  · obtain ⟨e⟩ := he
    have hcard := coreExtension_card hc
    rw [Nat.card_congr e.toEquiv, ClassCoverage.product_card] at hcard
    norm_num at hcard

/-- In the core row of the actual inner HS involution table, every nonsolvable
normal subgroup of the two-residual has order divisible by 3840. The concrete
residual and kernel calculations are discharged, with no extra model premise. -/
theorem hs_core_residual_normal_card_dvd [IsSimpleGroup Carrier] [Group.IsPerfect Carrier]
    (a : MulAut Carrier) (ha : orderOf a = 2) (hi : ∃ x, a = MulAut.conj x)
    (hc : IsHSCoreExtension a.fixedSubgroup)
    (N : Subgroup (pResidual 2 a.fixedSubgroup)) (hn : N.Normal)
    (hns : ¬ Group.IsSolvable N) : 3840 ∣ Nat.card N := by
  obtain ⟨e⟩ := core_fixed_equiv a ha hi hc
  let er := residualEquiv e
  let M := N.map er.toMonoidHom
  let : M.Normal := hn.map er.toMonoidHom er.surjective
  let eN : N ≃* M := er.subgroupMap N
  have hM : ¬ Group.IsSolvable M := by
    intro hs
    let := hs
    exact hns (Group.isSolvable_of_surjective
      (f := eN.symm.toMonoidHom) eN.symm.surjective)
  have hm := local_normal_eq_top M hM
  rw [Nat.card_congr eN.toEquiv, hm,
    Nat.card_congr (topEquiv : (⊤ : Subgroup (pResidual 2 (localGroup 0))) ≃*
      pResidual 2 (localGroup 0)).toEquiv, local_residual_card]

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
