module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.IntrinsicCore
public import Stellmacher.Recognition.Parrott.CentralizerStructure
public import Theory.SpecificGroups.ReeTwo.ParabolicConcreteStructure
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FirstQuotient

/-!
# Intrinsic Parrott hypotheses from the original quintic core bound

The source plane determines an actual involution z generating Ω₁Z(T),
and its full centralizer is Mc. If the original H fills this centralizer
and its two-core has order at most 512, the original Sylow lower bound
forces the order-512 core and the faithful Sz(2)=C5:C4 quotient.
`IntrinsicCore` supplies class three and the Sylow-five fixed subgroup.
The proof uses the actual ambient core image and literal Sylow maps.

Only the known quotient model is compared with C5:C4; no isomorphism of H
with a first parabolic is used. Equality H=Mc and the core upper bound
remain explicit obligations of qt-e-quintic-first-parabolic. The subsequent
coordinate, actor and presentation construction consumes this result.

Source: Aschbacher--Smith 14.2.6 and 14.2.20--21, pp.982,988--989;
Parrott (1972), original centralizer hypotheses, p.672.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original central point has an involution generator whose full
centralizer is the selected maximal two-local Mc. No endpoint model is used. -/
theorem source_central_involution
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    : ∃ z : G, orderOf z = 2 ∧ zpowers z = centralInvolutions T ∧
      centralizer ({z} : Set G) = Mc := by
  let Z := centralInvolutions T
  have hZ := plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_,_,hMc,_⟩ := plane_ordering_and_overgroups hG T hempty hM hu hmany hcard hZ
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2
    (hZ ▸ (by decide : 2 ∣ 2))
  have hzG : orderOf (z : G) = 2 :=
    (orderOf_injective Z.subtype Z.subtype_injective z).trans hz
  have hzgen : zpowers (z : G) = Z := eq_of_le_of_card_ge (zpowers_le.mpr z.property) (by
    rw [Nat.card_zpowers,hzG]
    exact hZ.le)
  refine ⟨z,hzG,hzgen,?_⟩
  calc
    centralizer ({(z : G)} : Set G) = centralizer (zpowers (z : G) : Set G) := by
      rw [zpowers_eq_closure,centralizer_closure]
    _ = Mc := (congrArg (fun K : Subgroup G => centralizer (K : Set G)) hzgen).trans hMc.symm

/-- The exact intrinsic input for the existing Sylow-coordinate and actor
constructors, conditional only on filling the full centralizer and bounding
its two-core. The class, faithful quotient and five-fixed clauses are proved. -/
theorem source_intrinsic_of_core_bound
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hHMc : H = Mc) (hQupper : Nat.card (pCore 2 H) ≤ 512) :
    ∃ z : G, zpowers z = centralInvolutions T ∧
      Recognition.ParrottCentralizerHypotheses z := by
  obtain ⟨z,hz,hzgen,hC⟩ := source_central_involution hG T hempty hM hu hmany hcard e
  have hHC : H = centralizer ({z} : Set G) := hHMc.trans hC.symm
  clear hHMc
  subst H
  let C := centralizer ({z} : Set G)
  let Q := pCore 2 C
  obtain ⟨⟨eC⟩,hTcard,hQcard,_⟩ := source_core512_orders
    hG T hempty hM hu hmany hcard e C hH hi hQupper
  have hclass := (source_core512_core_class_and_exponent
    hG T hempty hM hu hmany hcard e C hH hi hQupper).1
  let q : Q ≃* C.pCoreIn 2 := equivMapOfInjective Q C.subtype C.subtype_injective
  let : Group.IsNilpotent Q := pCore_isPGroup.isNilpotent
  have hclassQ : 3 ≤ Group.nilpotencyClass Q := by
    have hc := Group.nilpotencyClass_le_of_surjective q.toMonoidHom q.surjective
    rw [hclass] at hc
    exact hc
  refine ⟨z,hzgen,hz,hQcard,hclassQ,?_,?_⟩
  · exact ⟨FiveFour.action,FiveFour.action_injective,
      ⟨eC.trans (Tits.ExceptionalParabolics.FirstQuotient.coreQuotientEquiv.symm.trans
        ReeTwo.ParabolicConcrete.titsQuotientEquiv)⟩⟩
  · let : Fact (Nat.Prime 5) := ⟨by decide⟩
    let P : Sylow 5 C := Classical.choice inferInstance
    have hCcard : Nat.card C = 10240 := by
      have hc := ((T : Subgroup G).subgroupOf C).index_mul_card
      rw [Nat.card_congr (subgroupOfEquivOfLe hH.1.1.2).toEquiv] at hc
      change (T : Subgroup G).relIndex C * Nat.card (T : Subgroup G) = Nat.card C at hc
      rw [hi,hTcard] at hc
      omega
    have hPcard : Nat.card P = 5 := by
      rw [P.card_eq_multiplicity,hCcard]
      decide +kernel
    let A := (P : Subgroup C).map C.subtype
    have hA : Nat.card A = 5 :=
      (card_map_of_injective C.subtype_injective).trans hPcard
    have hfixed := source_core512_five_centralizer
      hG T hempty hM hu hmany hcard e C hH hi hQupper A (map_subtype_le _) hA
    refine ⟨P,?_⟩
    intro x hx
    have hxZ : ((x : C) : G) ∈ centralInvolutions T := by
      apply hfixed.le
      refine ⟨mem_map_of_mem C.subtype x.property,?_⟩
      intro a ha
      obtain ⟨a,ha,rfl⟩ := ha
      exact congrArg C.subtype (hx a ha)
    have hHZ : C ≤ centralizer (centralInvolutions T : Set G) :=
      (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e C hH.1.1 hH.1.2).2
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hHZ (y : C).property) _ hxZ).symm

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
