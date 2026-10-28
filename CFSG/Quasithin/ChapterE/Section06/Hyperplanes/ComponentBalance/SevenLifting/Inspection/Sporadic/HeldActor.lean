module
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.DegreeThree
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.Sporadic.Reduction
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Application
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Fusion.Normalizer
public import Theory.SpecificGroups.Held.LocalPairs.SylowPointwise
public import Theory.GroupTheory.NormalizerOuterQuotient

/-!
# The actual Held seven-subgroup actor

A two-subgroup of Aut(He) fixing A₇ or its perfect triple cover meets Inn(He)
trivially. The 2A fixed row reduces to PSL₃(4); an element of order five
conjugate to its square cannot embed in that degree-three model. Coprime
centers preserve injectivity in the reduction. The 2B row is excluded by order.
The actual permutation normalizer realization then bounds the actor by two.
If it fixes a Sylow two-subgroup pointwise, the checked Held Sylow-centralizer
calculation makes the actor inner, hence trivial.

This is the valid intrinsic input to the ambient E.6.18 argument. It does
not assert unrestricted seven-component inspection: the actual outer row
3.A₇.2 prevents that stronger statement.

Source: Aschbacher–Smith, E.6.18, printed p.252; GLS3 Table 5.3p.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
namespace HeldInspection

private theorem seven_perfect {G : Type*} [Group G] {L : Subgroup G}
    (hs : IsSeven L) : Group.IsPerfect L := by
  rcases hs with ha | h
  · obtain ⟨e⟩ := ha
    let : Group.IsPerfect (alternatingGroup (Fin 7)) :=
      ⟨commutator_alternatingGroup_eq_top (by norm_num)⟩
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · exact h.1.toIsPerfect

private theorem seven_center_card {G : Type*} [Group G] {L : Subgroup G}
    (hs : IsSeven L) : Nat.card (center L) = 1 ∨ Nat.card (center L) = 3 := by
  rcases hs with ha | h
  · obtain ⟨e⟩ := ha
    left
    rw [Nat.card_congr (centerCongr e).toEquiv,alternatingGroup.center_eq_bot (by simp),card_bot]
  · right
    obtain ⟨e⟩ := h.2.1
    rw [Nat.card_congr e.toEquiv]
    simp

private theorem seven_no_psl3four_embedding {G : Type*} [Group G] {L : Subgroup G}
    (hs : IsSeven L) (f : L →* Matrix.PSL3Four.PSL) (hf : Function.Injective f) : False := by
  let F := Matrix.PSL3Four.F
  let q : SL(3,F) →* PSL(3,F) := QuotientGroup.mk' (center SL(3,F))
  have hk : q.ker = center SL(3,F) := QuotientGroup.ker_mk' _
  have hp : IsPGroup 3 q.ker := by
    rw [hk]
    intro x
    refine ⟨1,?_⟩
    let c := Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (R := F) (0 : Fin 3)
    apply c.injective
    rw [map_pow,map_one]
    apply Subtype.ext
    exact (c x).property
  obtain ⟨x,y,hx,hxy⟩ := BinaryLie.seven_has_five_square_pair hs
  obtain ⟨a,b,ha,hab⟩ := q.exists_five_cycle_square_lift (QuotientGroup.mk'_surjective _)
    hk.le hp (f x) (f y) ((orderOf_injective f hf x).trans hx)
    (by simpa only [map_mul,map_inv,map_pow] using congrArg f hxy)
  exact Representation.FiveCycleDegreeThree.not_conjugate_square_of_matrix
    Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective
    (CharP.cast_ne_zero_of_ne_of_prime F (by decide : Nat.Prime 5) (by decide : 2 ≠ 5))
    a b ha hab

private theorem seven_no_inner_fixed (r : MulAut Held.He) (hr : orderOf r = 2)
    (hi : ∃ g, r = MulAut.conj g) (L : Subgroup Held.He)
    (hLF : L ≤ r.fixedSubgroup) (hs : IsSeven L) : False := by
  obtain ⟨g,rfl⟩ := hi
  rcases Held.InvolutionFixedData.innerRowsWithQuotient g hr with hd | hb
  · obtain ⟨D,hn,hq,hd,hz,⟨e⟩⟩ := hd
    let : D.Normal := hn
    let : IsQuasisimple D := hq
    let : Group.IsPerfect L := seven_perfect hs
    let LF := L.subgroupOf (MulAut.conj g).fixedSubgroup
    let ef : L ≃* LF := (subgroupOfEquivOfLe hLF).symm
    let : Group.IsPerfect LF := Group.IsPerfect.ofSurjective (f := ef.toMonoidHom) ef.surjective
    have hLD : LF ≤ D := le_of_isPerfect_of_index_eq_two LF D hd
    let j : L →* D := (inclusion hLD).comp ef.toMonoidHom
    have hj : Function.Injective j := (inclusion_injective hLD).comp ef.injective
    let f := e.toMonoidHom.comp ((QuotientGroup.mk' (center D)).comp j)
    have hkj : f.ker.map j ≤ center D := by
      rintro x ⟨l,hl,rfl⟩
      apply (QuotientGroup.eq_one_iff _).mp
      exact e.map_eq_one_iff.mp hl
    have hk : f.ker ≤ center L := by
      intro l hl
      apply mem_center_iff.mpr
      intro a
      apply hj
      simpa only [map_mul] using mem_center_iff.mp (hkj (mem_map_of_mem j hl)) (j a)
    have hc4 : Nat.card f.ker ∣ 4 := by
      have hh := card_dvd_of_le hkj
      rw [card_map_of_injective hj,hz] at hh
      exact hh
    have hc3 := card_dvd_of_le hk
    have hc : Nat.card f.ker = 1 := by
      rcases seven_center_card hs with hz1 | hz3
      · exact Nat.dvd_one.mp (hz1 ▸ hc3)
      · rw [hz3] at hc3
        exact Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 4) hc3 hc4
    have hfi : Function.Injective f := (MonoidHom.ker_eq_bot_iff _).mp (card_eq_one.mp hc)
    exact seven_no_psl3four_embedding hs f hfi
  · have hh := (SporadicInspection.seven_card_dvd hs).trans (card_dvd_of_le hLF)
    rw [hb] at hh
    norm_num at hh

/-- A two-group fixing a seven subgroup meets the actual inner automorphism
subgroup of Held trivially. No component assertion is required. -/
theorem inner_intersection_eq_bot
    (P : Subgroup (MulAut Held.He)) (hp : IsPGroup 2 P)
    (L : Subgroup Held.He) (hLF : L ≤ FixedPoints.subgroup P Held.He) (hs : IsSeven L) :
    P ⊓ MulAut.innerSubgroup Held.He = ⊥ := by
  let K := P ⊓ MulAut.innerSubgroup Held.He
  have hk : IsPGroup 2 K := hp.of_injective (inclusion inf_le_left)
    (inclusion_injective inf_le_left)
  by_contra hn
  obtain ⟨a, ha, hane⟩ := K.bot_or_exists_ne_one.resolve_left hn
  have hne : (⟨a, ha⟩ : K) ≠ 1 := fun h => hane (congrArg Subtype.val h)
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := K) 2
    ((hk.dvd_orderOf hne).trans (orderOf_dvd_natCard (x := (⟨a, ha⟩ : K))))
  have ht' : orderOf (t : MulAut Held.He) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hi : ∃ g, (t : MulAut Held.He) = MulAut.conj g := by
    obtain ⟨g, hg⟩ := t.property.2
    exact ⟨g, hg.symm⟩
  have hLt : L ≤ (t : MulAut Held.He).fixedSubgroup := by
    intro x hx
    exact (MulAut.mem_fixedSubgroup _ _).mpr (hLF hx ⟨t, t.property.1⟩)
  exact seven_no_inner_fixed t ht' hi L hLt hs

/-- Such an actor has order at most two. Full automorphism realization and
both actual inner involution rows are discharged. -/
theorem actor_card_le_two
    (P : Subgroup (MulAut Held.He)) (hp : IsPGroup 2 P)
    (L : Subgroup Held.He) (hLF : L ≤ FixedPoints.subgroup P Held.He) (hs : IsSeven L) :
    Nat.card P ≤ 2 := by
  have hd := inner_intersection_eq_bot P hp L hLF hs
  have hi := (MulAut.innerSubgroup Held.He).relIndex_dvd_index_of_normal (K := P)
  rw [← inf_relIndex_right, inf_comm _ P, hd, relIndex_bot_left, index_eq_card] at hi
  have ho : Nat.card (MulAut.Outer Held.He) ≤ 2 :=
    (Nat.card_le_card_of_surjective Held.permutationGroup.normalizerOuterHom
      (Held.permutationGroup.normalizerOuterHom_surjective
        Held.Realization.normalizer_surjective)).trans
      Held.permutationNormalizerQuotient_card_le_two
  exact (Nat.le_of_dvd Nat.card_pos hi).trans ho

/-- If the actor also fixes an actual Sylow two-subgroup pointwise, it is
trivial. This is the intrinsic endpoint needed by the ambient E.6.18 repair. -/
theorem eq_bot_of_fixes_sylow
    (P : Subgroup (MulAut Held.He)) (hp : IsPGroup 2 P)
    (L : Subgroup Held.He) (hLF : L ≤ FixedPoints.subgroup P Held.He) (hs : IsSeven L)
    (S : Sylow 2 Held.He)
    (hfix : ∀ a ∈ P, ∀ s ∈ (S : Subgroup Held.He), a s = s) : P = ⊥ := by
  have hd := inner_intersection_eq_bot P hp L hLF hs
  apply le_antisymm _ bot_le
  intro a ha
  have hi := Held.LocalPairs.SylowPointwise.isInner_of_fixes_sylow
    Held.Realization.normalizer_surjective S a (hfix a ha)
  exact hd ▸ (show a ∈ P ⊓ MulAut.innerSubgroup Held.He from ⟨ha, hi⟩)

end HeldInspection
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
