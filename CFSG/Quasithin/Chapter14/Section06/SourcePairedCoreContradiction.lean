module
public import CFSG.Quasithin.Chapter14.Section06.SourceF9
public import Theory.GroupTheory.CommutatorFixedSwap
/-!
# The final paired-core contradiction in the original rank-two source

For H = Mc, the actual F.9 hypothesis puts the original plane V inside
Q1 = O₂(Mc) and bounds [V,Q1] by Z = Ω₁Z(T). If Q1 is the product of
commuting disjoint factors interchanged by an element of T, that element
fixes Z pointwise. Hence each factor commutator with V vanishes.

Thus V lies in Ω₁Z(Q1). When this omega-center has order four, it equals V
and is normalized by Mc. The source equality N_G(V) = M contradicts the
original outside condition on Mc. All F.9 hypotheses and that outside
condition are constructed here from the original rank-two source data.
The paired geometry is supplied by the preceding A₅-block analysis.

Source: Aschbacher–Smith, proof of 14.6.9, assertions (m), (n) and the
following contradiction, printed p.1027 of refs/quasithin.pdf. The direct
product commutator argument replaces the appeal there to 14.5.15(1).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The literal paired-core geometry excludes the remaining characteristic-two branch. -/
theorem source_paired_core_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (R1 R2 : Subgroup G) (t : G)
    (hQ : Mc.pCoreIn 2 = R1 ⊔ R2)
    (hd : Disjoint R1 R2) (hc : R1 ≤ centralizer (R2 : Set G))
    (ht : t ∈ (T : Subgroup G))
    (hswap : R1.map (MulAut.conj t).toMonoidHom = R2)
    (hZ1 : Nat.card (omegaOneCenterAmbient (Mc.pCoreIn 2)) = 4) : False := by
  have hZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_,hne,hMc,_⟩ :=
    plane_ordering_and_overgroups hG T hempty hM hu hmany hcard hZ
  have hMcMax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hu ▸ Set.mem_singleton Mc).1
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [hMc]
    exact le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)
  have hMcOutside : Mc ∈ Chapter1.HOutside G (T : Set G) (M : Set G) :=
    ⟨⟨Chapter1.mem_H_of_isTwoLocal hMcMax.1,hTMc⟩,
      fun hh => hne (hMcMax.eq_of_le hM.1.1.1 hh).symm⟩
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,Mc⟩
  have h : D.Hypothesis :=
    source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab Mc hMcOutside
  have hVU : localModule T M ≤ D.UH := le_conjugateSpanBy _ _
  have hVQ : localModule T M ≤ Mc.pCoreIn 2 := hVU.trans h.UH_le_QH
  have hcomm : ⁅localModule T M, Mc.pCoreIn 2⁆ ≤ centralInvolutions T :=
    (commutator_mono hVU le_rfl).trans h.commutator_UH_QH_le_point
  have hcentral : localModule T M ≤ centralizer (Mc.pCoreIn 2 : Set G) := by
    rw [hQ] at hVQ hcomm ⊢
    exact centralizes_sup_of_commutator_le_fixed_swap _ _ R1 R2 t hVQ hcomm hd hc
      ((le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)) ht) hswap
  let : IsElementaryAbelian 2 (localModule T M) := h.elementary
  have hVOmega : localModule T M ≤ omegaOneCenterAmbient (Mc.pCoreIn 2) := by
    intro v hv
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨hVQ hv, elemPow_eq_one_of_isElementaryAbelian v hv, hcentral hv⟩
  have hVOmegaEq : localModule T M = omegaOneCenterAmbient (Mc.pCoreIn 2) :=
    eq_of_le_of_card_ge hVOmega (by rw [hcard,hZ1])
  have hMcV : Mc ≤ normalizer (localModule T M : Set G) := by
    rw [hVOmegaEq]
    exact (Mc.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))).trans
      (ChapterA.Section04.normalizer_le_normalizer_omegaCenter _)
  have hMV : M = normalizer (localModule T M : Set G) :=
    InitialSource.UniformControl.source_local_eq_normalizer hG T hM.1
  exact hMcOutside.2 (hMV ▸ hMcV)
end CFSG.Quasithin.Chapter14.Section06
