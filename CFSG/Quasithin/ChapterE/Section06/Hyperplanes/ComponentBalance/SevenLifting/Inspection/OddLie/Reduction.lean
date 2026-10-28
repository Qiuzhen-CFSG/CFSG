module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Rank and order reductions for the odd-characteristic seven inspection

Both A₇ and its perfect central three-cover have three-rank at least two,
and their orders are divisible by seven. Either invariant can exclude an
embedding in a particular model.

For a two-subgroup P of Aut(G), an ordinary component L of the common fixed
group is perfect. Its inclusion in the fixed group of any involution in P
therefore factors through that fixed group's derived subgroup. If all such
derived subgroups have three-rank at most one, Cauchy's theorem forces P = 1.
This proves the transfer for the entire actor; no component membership in the
larger, single-involution fixed group is asserted. The concrete rank bounds
remain separate mathematical obligations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the inspection
in E.6.18, printed p.252 (PDF p.263), and Theorem C, printed p.33.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddLie
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem seven_dvd_card {L : Subgroup G} (hL : IsSeven L) : 7 ∣ Nat.card L := by
  have ha : 7 ∣ Nat.card (alternatingGroup (Fin 7)) := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rcases hL with hL | hL
  · obtain ⟨e⟩ := hL
    rwa [Nat.card_congr e.toEquiv]
  · obtain ⟨_, _, ⟨e⟩⟩ := hL
    rw [← Nat.card_congr e.toEquiv] at ha
    exact ha.trans (card_quotient_dvd_card (center L))

theorem not_isSeven_of_three_rank_le_one (hr : primeRank 3 G ≤ 1)
    (L : Subgroup G) : ¬ IsSeven L := by
  intro hL
  have hu := (primeRank_subgroup_le 3 L).trans hr
  have hl := hL.two_le_primeRank
  omega

omit [Finite G] in
theorem not_isSeven_of_seven_not_dvd (hc : ¬ 7 ∣ Nat.card G)
    (L : Subgroup G) : ¬ IsSeven L := by
  intro hL
  exact hc ((seven_dvd_card hL).trans L.card_subgroup_dvd_card)

/-- A concrete sufficient bound on derived subgroups of involution fixed groups. -/
@[expose] def InvolutionDerivedThreeRank (X : Type*) [Group X] : Prop :=
  ∀ a : MulAut X, orderOf a = 2 → primeRank 3 (commutator a.fixedSubgroup) ≤ 1

/-- A component of the common fixed group embeds in the derived fixed group
of any actor involution. Cauchy therefore excludes every nontrivial two-actor. -/
theorem sevenActionInspection_of_involutionDerivedThreeRank
    (hr : InvolutionDerivedThreeRank G) : SevenActionInspection G := by
  intro P hP L hLF hLc hL
  by_contra hPne
  obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  have hd : 2 ∣ Nat.card P := (hP.dvd_orderOf hx).trans (orderOf_dvd_natCard x)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := P) 2 hd
  have hao : orderOf (a : MulAut G) = 2 := (Subgroup.orderOf_coe a).trans ha
  let : IsQuasisimple (L.subgroupOf (FixedPoints.subgroup P G)) := hLc.2
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hLF).toMonoidHom) (subgroupOfEquivOfLe hLF).surjective
  have hLa : L ≤ (a : MulAut G).fixedSubgroup := by
    intro l hl
    exact (MulAut.mem_fixedSubgroup _ _).mpr ((hLF hl) a)
  let f : L →* (a : MulAut G).fixedSubgroup :=
    { toFun := fun l => ⟨l, hLa l.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hfc : f.range ≤ commutator (a : MulAut G).fixedSubgroup := by
    rw [← Subgroup.commutator_eq_self (H := f.range)]
    exact commutator_mono le_top le_top
  let g : L →* commutator (a : MulAut G).fixedSubgroup :=
    f.codRestrict _ (fun l => hfc ⟨l, rfl⟩)
  have hgi : Function.Injective g := by
    intro x y h
    exact Subtype.ext (congrArg (fun z => z.val.val) h)
  have hu := (Theory.GroupTheory.primeRank_le_of_injective 3 g hgi).trans (hr _ hao)
  have hl := hL.two_le_primeRank
  omega

/-- Transport the bound through the actual automorphism and fixed-group equivalences. -/
theorem InvolutionDerivedThreeRank.of_equiv {H : Type*} [Group H] [Finite H]
    (h : InvolutionDerivedThreeRank H) (e : G ≃* H) : InvolutionDerivedThreeRank G := by
  intro a ha
  let c := MulAut.fixedSubgroupCongr e a
  have hc : (commutator a.fixedSubgroup).map c.toMonoidHom =
      commutator (MulAut.congr e a).fixedSubgroup := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr c.surjective]
    rfl
  let d := (c.subgroupMap (commutator a.fixedSubgroup)).trans (MulEquiv.subgroupCongr hc)
  rw [primeRank_congr 3 d]
  exact h _ (((MulAut.congr e).orderOf_eq a).trans ha)


end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddLie
