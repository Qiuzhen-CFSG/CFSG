module
public import Theory.Mathieu.M22.UniversalMultiplier.TwoPrimary

/-!
# Comparison of genuine perfect M₂₂ covers

Remove the odd part of a central kernel. The remaining two-primary kernel
is cyclic by the proved native hexad argument; the odd part has order at
most three. Coprimality makes the whole kernel cyclic. The universal lifts
onto two covers of the same degree therefore have the same kernel, giving
an isomorphism commuting with their specified projections to M₂₂.

The application is the perfect six-cover comparison in AS91 (8.3), p.606.
Only proved multiplier upper bounds and two-primary cyclicity are used;
no exact multiplier order or split product model is assumed. The elementary
cyclic-subgroup argument is adapted from `PrimeCyclicCentralizer.lean`.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open PerfectCentralCovering Subgroup Sporadic.Mathieu

private theorem odd_kernel_arithmetic {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hc : m * n ∣ 12) (hn4 : n ∣ 4)
    (hpow : ∀ i : ℕ, 2 ^ i ∣ m * n ↔ 2 ^ i ∣ n) :
    m ∣ 3 ∧ Nat.Coprime m n := by
  have hmn := Nat.le_of_dvd (by decide : 0 < 12) hc
  have hml : m ≤ 12 := (Nat.le_mul_of_pos_right m hn).trans hmn
  have hnl := Nat.le_of_dvd (by decide : 0 < 4) hn4
  have h1 := hpow 1
  have h2 := hpow 2
  have h3 := hpow 3
  interval_cases m <;> interval_cases n <;> norm_num at *

/-- Cyclicity needs only the genuine upper bounds and cyclic two-primary kernels. -/
theorem m22_cover_kernel_isCyclic {E : Type*} [Group E] [Finite E]
    (f : Cover E M22) : IsCyclic f.toMonoidHom.ker := by
  obtain ⟨D,hDn,hD,hp,hd⟩ := M22UniversalMultiplier.exists_twoPrimary_quotient f
  let : D.Normal := hDn
  let g := f.quotientKernelSubgroup D hD
  let q : f.toMonoidHom.ker →* g.toMonoidHom.ker :=
    ((QuotientGroup.mk' D).comp f.toMonoidHom.ker.subtype).codRestrict _
      (fun x => x.property)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x,hx⟩ := QuotientGroup.mk'_surjective D y.val
    have hxK : x ∈ f.toMonoidHom.ker := by
      change g.toMonoidHom (QuotientGroup.mk' D x) = 1
      rw [hx]
      exact y.property
    exact ⟨⟨x,hxK⟩,Subtype.ext hx⟩
  have hc : Nat.card q.ker * Nat.card g.toMonoidHom.ker = Nat.card f.toMonoidHom.ker := by
    have hc := q.ker.card_mul_index
    rwa [index_eq_card,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv] at hc
  have hm := odd_kernel_arithmetic (Nat.card_pos (α := q.ker))
    (Nat.card_pos (α := g.toMonoidHom.ker))
    (hc ▸ M22UniversalMultiplier.kernel_card_dvd_twelve f)
    (M22UniversalMultiplier.twoPrimary_kernel_card_dvd_four g hp)
    (fun i => hc ▸ hd i)
  let : IsCyclic q.ker := isCyclic_of_card_dvd_prime (p := 3) hm.1
  let : IsCyclic g.toMonoidHom.ker := M22UniversalMultiplier.twoPrimary_kernel_isCyclic g hp
  let : CommGroup f.toMonoidHom.ker := { (inferInstance : Group f.toMonoidHom.ker) with
    mul_comm x y := Subtype.ext (mem_center_iff.mp (f.ker_le_center y.property) x) }
  exact Group.isCyclic_of_coprime_card_ker q hm.2 hq

-- The finite root-count argument also appears privately in PrimeCyclicCentralizer.
theorem subgroups_eq_of_card_eq_in_cyclic
    {U : Type*} [Group U] [Finite U] (A B C : Subgroup U) [IsCyclic C]
    (ha : A ≤ C) (hb : B ≤ C) (hc : Nat.card A = Nat.card B) : A = B := by
  classical
  let : Fintype C := Fintype.ofFinite C
  let B' := B.subgroupOf C
  have hcard : Nat.card B' = Nat.card B :=
    Nat.card_congr (subgroupOfEquivOfLe hb).toEquiv
  have hsub : (B' : Set C).toFinset ⊆
      Finset.univ.filter (fun a : C => a ^ Nat.card B' = 1) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      congrArg Subtype.val (pow_card_eq_one' (x := (⟨x,Set.mem_toFinset.mp hx⟩ : B')))⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    simpa [Set.toFinset_card, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
      using IsCyclic.card_pow_eq_one_le (α := C) (Nat.card_pos (α := B')))
  apply eq_of_le_of_card_ge ?_ hc.ge
  intro x hx
  have hpow : (⟨x,ha hx⟩ : C) ^ Nat.card B' = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, hcard, ← hc]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨x,hx⟩ : A)))
  have hm : (⟨x,ha hx⟩ : C) ∈ (B' : Set C).toFinset := by
    rw [heq]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpow⟩
  have hm' : (⟨x,ha hx⟩ : C) ∈ B' := Set.mem_toFinset.mp hm
  exact hm'

/-- Equal-degree perfect covers of the actual M₂₂ are isomorphic over the
specified base, without an exact formula for the multiplier order. -/
theorem exists_m22_cover_equiv_over
    {E F : Type*} [Group E] [Finite E] [Group F] [Finite F]
    (f : Cover E M22) (g : Cover F M22)
    (hc : Nat.card f.toMonoidHom.ker = Nat.card g.toMonoidHom.ker) :
    ∃ e : E ≃* F, ∀ x, g.toMonoidHom (e x) = f.toMonoidHom x := by
  let := f.isPerfect
  let := g.isPerfect
  obtain ⟨a,ha,_⟩ := universalProjection_existsUnique_lift
    f.toMonoidHom f.surjective f.ker_le_center
  obtain ⟨b,hb,_⟩ := universalProjection_existsUnique_lift
    g.toMonoidHom g.surjective g.ker_le_center
  have has : Function.Surjective a :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect f.toMonoidHom a
      (ha ▸ universalProjection_surjective M22) f.ker_le_center
  have hbs : Function.Surjective b :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect g.toMonoidHom b
      (hb ▸ universalProjection_surjective M22) g.ker_le_center
  have hcarda := kernel_card_eq_mul_of_surjective_factor (universalProjection M22)
    f.toMonoidHom a f.surjective has ha
  have hcardb := kernel_card_eq_mul_of_surjective_factor (universalProjection M22)
    g.toMonoidHom b g.surjective hbs hb
  have hcard : Nat.card a.ker = Nat.card b.ker :=
    Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := g.toMonoidHom.ker))
      (by rw [← hc, ← hcarda, hc, ← hcardb])
  let : IsCyclic (universalProjection M22).ker := m22_cover_kernel_isCyclic (universalCover M22)
  have hak : a.ker ≤ (universalProjection M22).ker := by
    intro x hx
    change universalProjection M22 x = 1
    rw [← ha, MonoidHom.comp_apply, hx, map_one]
  have hbk : b.ker ≤ (universalProjection M22).ker := by
    intro x hx
    change universalProjection M22 x = 1
    rw [← hb, MonoidHom.comp_apply, hx, map_one]
  have heq := subgroups_eq_of_card_eq_in_cyclic a.ker b.ker (universalProjection M22).ker hak hbk hcard
  let ea := QuotientGroup.quotientKerEquivOfSurjective a has
  let eb := QuotientGroup.quotientKerEquivOfSurjective b hbs
  let e := ea.symm.trans ((QuotientGroup.quotientMulEquivOfEq heq).trans eb)
  refine ⟨e,fun x => ?_⟩
  obtain ⟨u,rfl⟩ := has x
  have heu : e (a u) = b u := by
    change eb (QuotientGroup.quotientMulEquivOfEq heq (ea.symm (a u))) = b u
    have hea : ea.symm (a u) = QuotientGroup.mk u :=
      ea.symm_apply_eq.mpr rfl
    rw [hea]
    rfl
  rw [heu]
  exact (DFunLike.congr_fun hb u).trans (DFunLike.congr_fun ha u).symm

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
