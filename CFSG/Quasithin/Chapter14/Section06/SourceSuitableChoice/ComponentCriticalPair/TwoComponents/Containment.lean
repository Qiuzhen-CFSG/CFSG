module

public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.Endpoints
public import Theory.GroupTheory.CComponent.RelativeQuotientLifting

/-!
# Lifting the terminal pair comparison

After the critical point has been placed in the first component support,
the second component lies in the opposite point centralizer. Containment
of its image in a specified opposite component lifts through the actual
two-core quotient. A proper containment cannot be in its own conjugate;
the unequal orders then force both original components to be normal in Mc.

This proves the lifting and order step on p.1040 of Aschbacher--Smith,
14.6.24(3). The critical-point placement, exclusion of a diagonal image,
and exclusion of equality are explicit inputs to this intermediate lemma,
not claimed source conclusions. The remaining normal-pair contradiction
on p.1041 must still be proved before asserting 14.6.24(3).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A component centralizing the support containing Z-gamma lies in the
literal conjugate point centralizer, using the same left conjugator. -/
theorem le_conjugate_of_point_support
    (H Z W B : Subgroup G) (hH : H = centralizer (Z : Set G)) (g : G)
    (hpoint : Z.map (MulAut.conj g).toMonoidHom ≤ W)
    (hBW : B ≤ centralizer (W : Set G)) :
    B ≤ H.map (MulAut.conj g).toMonoidHom := by
  intro b hb
  let e := MulAut.conj g
  refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
  rw [hH]
  intro z hz
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using
    hBW hb (e z) (hpoint (mem_map_of_mem e.toMonoidHom hz))

/-- Proper inclusion in one of the two conjugates selects the other
component and proves unequal orders, rather than assuming a normal pair. -/
theorem strict_conjugate_pair
    (K Kplus J : Subgroup G) (g : G)
    (hJ : J = K.map (MulAut.conj g).toMonoidHom ∨
      J = Kplus.map (MulAut.conj g).toMonoidHom)
    (hle : Kplus ≤ J) (hne : Kplus ≠ J) :
    J = K.map (MulAut.conj g).toMonoidHom ∧
      Kplus < K.map (MulAut.conj g).toMonoidHom ∧ Nat.card Kplus < Nat.card K := by
  have hlt : Nat.card Kplus < Nat.card J := lt_of_le_of_ne
    (card_le_of_le hle) (fun he => hne (eq_of_le_of_card_ge hle he.ge))
  rcases hJ with he | he
  · refine ⟨he,he ▸ lt_of_le_of_ne hle hne,?_⟩
    rwa [he,card_map_of_injective (MulAut.conj g).injective] at hlt
  · rw [he,card_map_of_injective (MulAut.conj g).injective] at hlt
    exact (Nat.lt_irrefl _ hlt).elim

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- The original-source application of the proper component comparison.
It discharges quotient lifting, unequal orders, and relative normality.
Its placement and proper image-alignment premises remain to be proved. -/
theorem source_normal_pair_of_proper_quotient_alignment
    (K Kplus : Subgroup G) (hKM : K ≤ Mc) (hKplusM : Kplus ≤ Mc)
    (hK : (K.subgroupOf Mc).IsCComponent)
    (hKplus : (Kplus.subgroupOf Mc).IsCComponent)
    (hpair : ∀ J : Subgroup Mc, J.IsCComponent →
      J = K.subgroupOf Mc ∨ J = Kplus.subgroupOf Mc)
    (i : (ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab).CriticalEndpoint)
    (hpoint : i.conjugate (centralInvolutions T) ≤
      ⁅conjugateSpanBy (localModule T M) Mc,K⁆)
    (hcross : ⁅⁅conjugateSpanBy (localModule T M) Mc,K⁆,Kplus⁆ = ⊥)
    (J : Subgroup G) (hJ : J = i.conjugate K ∨ J = i.conjugate Kplus)
    (himage : (Kplus.subgroupOf (i.conjugate Mc)).map
        (QuotientGroup.mk' (pCore 2 (i.conjugate Mc))) ≤
      (J.subgroupOf (i.conjugate Mc)).map
        (QuotientGroup.mk' (pCore 2 (i.conjugate Mc))))
    (hne : Kplus ≠ J) :
    J = i.conjugate K ∧ Kplus < i.conjugate K ∧
      Nat.card Kplus < Nat.card K ∧
      (K.subgroupOf Mc).Normal ∧ (Kplus.subgroupOf Mc).Normal ∧
      ¬ ∃ t ∈ (T : Subgroup G), Kplus = K.map (MulAut.conj t⁻¹).toMonoidHom := by
  have hMc : Mc = centralizer (centralInvolutions T : Set G) :=
    (source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e).2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hBH : Kplus ≤ i.conjugate Mc := le_conjugate_of_point_support
    Mc (centralInvolutions T) _ Kplus hMc i.representative hpoint
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcross))
  have hJH : J ≤ i.conjugate Mc := by
    rcases hJ with rfl | rfl
    · exact map_mono hKM
    · exact map_mono hKplusM
  have hcomp : (J.subgroupOf (i.conjugate Mc)).IsCComponent := by
    rcases hJ with rfl | rfl
    · exact hK.map_relative_equiv Mc K hKM (MulAut.conj i.representative)
    · exact hKplus.map_relative_equiv Mc Kplus hKplusM (MulAut.conj i.representative)
  let := hKplus.perfect
  let : Group.IsPerfect Kplus := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hKplusM).toMonoidHom)
    (subgroupOfEquivOfLe hKplusM).surjective
  have hle := perfect_le_relative_cComponent_of_twoCore_image_le
    (i.conjugate Mc) Kplus J hBH hJH hcomp himage
  obtain ⟨he,hs,hc⟩ := strict_conjugate_pair K Kplus J i.representative hJ hle hne
  obtain ⟨hn,hnplus⟩ := relative_cComponent_pair_normal_of_card_ne
    Mc K Kplus hKM hKplusM hK hKplus hpair hc.ne.symm
  refine ⟨he,hs,hc,hn,hnplus,?_⟩
  rintro ⟨t,_,ht⟩
  rw [ht,card_map_of_injective (MulAut.conj t⁻¹).injective] at hc
  exact Nat.lt_irrefl _ hc

end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair.TwoComponents
