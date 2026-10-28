module

public import Theory.GroupTheory.SimpleFiveSmallSectionAction
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.Frattini.PGroup
public import Theory.GroupAction.FaithfulSixteen
public import Theory.GroupAction.IrreducibleTwoCoreKernel

/-!
# The first possible nontrivial two-section of a simple five-action

A nontrivial action by a two-perfect group with simple, five-divisible
two-core quotient requires five in the automorphism group. If the acted-on
two-group has order at most sixteen, its order is exactly sixteen. A
nontrivial Frattini subgroup would leave a quotient of order at most eight;
Burnside's basis-kernel theorem and the absence of quintic automorphisms on
that quotient then give a contradiction. Thus the actual section is
elementary abelian. No identification of its four-dimensional module is used.
The original action is irreducible and its kernel is exactly the original
two-core, so it descends faithfully to the specified simple quotient.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {L U : Type*} [Group L] [Finite L] [Group U] [Finite U]

private theorem card_dvd_eight_of_two_group_card_le_eight
    (hU : IsPGroup 2 U) (hsmall : Nat.card U ≤ 8) : Nat.card U ∣ 8 := by
  obtain ⟨n,hn⟩ := hU.exists_card_eq
  have hn3 : n ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by
    simpa only [←hn] using hsmall)
  rw [hn]
  exact pow_dvd_pow 2 hn3

omit [Group L] [Finite L] in
private theorem elementary_sixteen_of_five_dvd_aut
    (hU : IsPGroup 2 U) (hsmall : Nat.card U ≤ 16)
    (hfive : 5 ∣ Nat.card (MulAut U)) :
    Nat.card U = 16 ∧ IsElementaryAbelian 2 U := by
  have hcard : Nat.card U = 16 := by
    obtain ⟨n,hn⟩ := hU.exists_card_eq
    have hn4 : n ≤ 4 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (by
      simpa only [←hn] using hsmall)
    have hn3 : ¬ n ≤ 3 := by
      intro hn3
      have hc := five_coprime_card_mulAut_of_card_dvd_eight (Q := U) (by
        rw [hn]; exact pow_dvd_pow 2 hn3)
      exact Nat.prime_five.coprime_iff_not_dvd.mp hc hfive
    have : n = 4 := by omega
    simpa [this] using hn
  have hphi : frattini U = ⊥ := by
    by_contra hn
    have hphicard : 2 ≤ Nat.card (frattini U) :=
      (frattini U).one_lt_card_iff_ne_bot.mpr hn
    have hquot : Nat.card (U ⧸ frattini U) ≤ 8 := by
      have hh := (frattini U).card_mul_index
      change Nat.card (frattini U) * Nat.card (U ⧸ frattini U) = Nat.card U at hh
      nlinarith
    have hquotcop := five_coprime_card_mulAut_of_card_dvd_eight
      (card_dvd_eight_of_two_group_card_le_eight (hU.to_quotient _) hquot)
    let f := quotientAut (frattini U)
    obtain ⟨n,hn⟩ := (isPGroup_quotientAut_frattini_kernel hU).exists_card_eq
    have hcop : Nat.Coprime 5 (Nat.card f.ker) := by
      rw [hn]
      exact (by decide : Nat.Coprime 5 2).pow_right n
    have hc : Nat.card f.ker * Nat.card f.range = Nat.card (MulAut U) := by
      rw [← index_ker]
      exact f.ker.card_mul_index
    have hr : 5 ∣ Nat.card f.range := hcop.dvd_of_dvd_mul_left (hc ▸ hfive)
    exact Nat.prime_five.coprime_iff_not_dvd.mp hquotcop
      (hr.trans f.range.card_subgroup_dvd_card)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 U) := ⟨hU⟩
  exact ⟨hcard,(frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi⟩

/-- A nontrivial action on a two-section of order at most sixteen forces that
literal section to be elementary of order sixteen. -/
theorem elementary_sixteen_of_nontrivial_simple_five_action
    [IsSimpleGroup (L ⧸ pCore 2 L)] (hL : IsPPerfect 2 L)
    (hfive : 5 ∣ Nat.card (L ⧸ pCore 2 L))
    (hU : IsPGroup 2 U) (hsmall : Nat.card U ≤ 16)
    (ρ : L →* MulAut U) (hne : ρ ≠ 1) :
    Nat.card U = 16 ∧ IsElementaryAbelian 2 U := by
  apply elementary_sixteen_of_five_dvd_aut hU hsmall
  by_contra hn
  exact hne (hom_eq_one_of_twoPerfect_simple_five_section hL hfive ρ
    (Nat.prime_five.coprime_iff_not_dvd.mpr hn))

private theorem five_dvd_range_of_nontrivial_action
    [IsSimpleGroup (L ⧸ pCore 2 L)] (hL : IsPPerfect 2 L)
    (hfive : 5 ∣ Nat.card (L ⧸ pCore 2 L))
    (ρ : L →* MulAut U) (hne : ρ ≠ 1) : 5 ∣ Nat.card ρ.range := by
  by_contra hn
  have hh := hom_eq_one_of_twoPerfect_simple_five_section hL hfive ρ.rangeRestrict
    (Nat.prime_five.coprime_iff_not_dvd.mpr hn)
  apply hne
  apply MonoidHom.ext
  intro l
  exact congrArg Subtype.val (DFunLike.congr_fun hh l)

/-- Every subgroup invariant under the actual nontrivial action is trivial or
full; this is irreducibility of the literal elementary section. -/
theorem invariant_eq_bot_or_top_of_nontrivial_simple_five_action
    [IsSimpleGroup (L ⧸ pCore 2 L)] (hL : IsPPerfect 2 L)
    (hfive : 5 ∣ Nat.card (L ⧸ pCore 2 L))
    (hU : IsPGroup 2 U) (hsmall : Nat.card U ≤ 16)
    (ρ : L →* MulAut U) (hne : ρ ≠ 1)
    (D : Subgroup U) (hD : ∀ l : L, ∀ x : U, x ∈ D ↔ ρ l x ∈ D) :
    D = ⊥ ∨ D = ⊤ :=
  Theory.GroupAction.invariant_eq_bot_or_top_of_image_five ρ
    (five_dvd_range_of_nontrivial_action hL hfive ρ hne)
    (elementary_sixteen_of_nontrivial_simple_five_action hL hfive hU hsmall ρ hne).1 D hD

/-- The original action on this chief section kills exactly the original
two-core, and therefore gives a faithful action of the simple quotient. -/
theorem kernel_eq_core_of_nontrivial_simple_five_action
    [IsSimpleGroup (L ⧸ pCore 2 L)] (hL : IsPPerfect 2 L)
    (hfive : 5 ∣ Nat.card (L ⧸ pCore 2 L))
    (hU : IsPGroup 2 U) (hsmall : Nat.card U ≤ 16)
    (ρ : L →* MulAut U) (hne : ρ ≠ 1) : ρ.ker = pCore 2 L := by
  obtain ⟨hcard,helem⟩ :=
    elementary_sixteen_of_nontrivial_simple_five_action hL hfive hU hsmall ρ hne
  let : IsElementaryAbelian 2 U := helem
  let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hirr : ∀ D : Subgroup U,
      (∀ g : ρ.range, ∀ x : U, x ∈ D → g • x ∈ D) → D = ⊥ ∨ D = ⊤ := by
    intro D hD
    apply invariant_eq_bot_or_top_of_nontrivial_simple_five_action hL hfive hU hsmall ρ hne D
    intro l x
    constructor
    · exact hD (ρ.rangeRestrict l) x
    · intro hx
      have hh := hD (ρ.rangeRestrict l⁻¹) (ρ l x) hx
      change ρ l⁻¹ (ρ l x) ∈ D at hh
      simpa only [map_inv,MulAut.inv_apply,MulEquiv.symm_apply_apply] using hh
  have hcore : pCore 2 L ≤ ρ.ker := irreducible_range_core_le_ker ρ hirr
  apply le_antisymm ?_ hcore
  let π := QuotientGroup.mk' (pCore 2 L)
  let : (ρ.ker.map π).Normal := ρ.normal_ker.map π (QuotientGroup.mk'_surjective _)
  rcases (inferInstance : (ρ.ker.map π).Normal).eq_bot_or_eq_top with hb | ht
  · simpa only [π,QuotientGroup.ker_mk'] using (map_eq_bot_iff ρ.ker).mp hb
  · have hh := congrArg (Subgroup.comap π) ht
    rw [comap_map_eq,comap_top,QuotientGroup.ker_mk',sup_of_le_left hcore] at hh
    exact (hne (ρ.ker_eq_top_iff.mp hh)).elim

end Theory.GroupTheory
