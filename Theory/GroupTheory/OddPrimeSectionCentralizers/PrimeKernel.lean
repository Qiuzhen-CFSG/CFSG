module

public import Theory.GroupTheory.OddPrimeSectionCentralizers.Involution
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.PCoreSurjective
public import Theory.Quasithin.Rank

/-!
# Cyclic centralizers through a prime-group kernel

For a surjection with p-group kernel, the preimage of the target p-core is
the source p-core. Self-centralization therefore lifts to the source.
Lift a target involution through the odd kernel and apply the rank-two
fixed-subgroup theorem there. Coprime fixed-point lifting gives a surjection
of the literal fixed subgroups, so cyclicity descends. The centralizer of
the original two-subgroup embeds in this cyclic fixed subgroup.

Source: Aschbacher–Smith, Lemma A.1.31(1), printed pp.27–28. The rank
hypothesis remains on the group before taking the surjective image.
-/

public section

open Subgroup
namespace Theory.GroupTheory
universe u v

private theorem odd_core_card {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) : Odd (Nat.card (pCore p G)) := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := p) (G := G)).exists_card_eq
  rw [hn]
  exact hp.pow

/-- A nonidentity involution has cyclic fixed subgroup in a self-centralizing
prime core when the ambient prime rank is at most two. -/
theorem cyclic_primeCore_fixedSubgroup_of_involution
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hrank : primeRank p G ≤ 2)
    (hc : centralizer (pCore p G : Set G) ≤ pCore p G)
    (t : G) (ht : orderOf t = 2) :
    IsCyclic (MulAut.conjNormal t : MulAut (pCore p G)).fixedSubgroup := by
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  let a : MulAut (pCore p G) := MulAut.conjNormal t
  have ha2 : a ^ 2 = 1 := by
    rw [show a = MulAut.conjNormal t from rfl, ← map_pow, ht2, map_one]
  have ha : Function.Involutive a := fun x => DFunLike.congr_fun ha2 x
  apply cyclic_fixedSubgroup_of_involution_rank_le_two pCore_isPGroup hp
    ((primeRank_subgroup_le p _).trans hrank) a ha
  intro hone
  have htc : t ∈ centralizer (pCore p G : Set G) := by
    intro x hx
    have he := congrArg Subtype.val (DFunLike.congr_fun hone (⟨x, hx⟩ : pCore p G))
    change t * x * t⁻¹ = x at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  let tp : pCore p G := ⟨t, hc htc⟩
  have htp2 : tp ^ 2 = 1 := Subtype.ext ht2
  have htp1 : tp = 1 := (odd_core_card (G := G) hp).coprime_two_right.pow_left_bijective.injective
    (htp2.trans (one_pow 2).symm)
  have ht1 : t = 1 := congrArg Subtype.val htp1
  simp [ht1] at ht

/-- The section-centralizer conclusion when the surjection has p-group kernel. -/
theorem cyclic_primeCore_centralizer_of_surjective_pGroup_kernel
    {A : Type u} [Group A] [Finite A] {D : Type v} [Group D] [Finite D]
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hrank : primeRank p A ≤ 2)
    (f : A →* D) (hf : Function.Surjective f) (hk : IsPGroup p f.ker)
    (hF : generalizedFitting D = pCore p D)
    (S : Subgroup D) (hS : IsPGroup 2 S) (hne : S ≠ ⊥) :
    IsCyclic ((centralizer (S : Set D)).subgroupOf (pCore p D)) := by
  have hpre := f.comap_pCore_of_ker_isPGroup hf hk
  have hmap : (pCore p A).map f = pCore p D := by
    rw [← hpre, map_comap_eq_self]
    rw [f.range_eq_top_of_surjective hf]
    exact le_top
  have hD : centralizer (pCore p D : Set D) ≤ pCore p D := by
    simpa only [hF] using centralizer_generalizedFitting_le D
  have hA : centralizer (pCore p A : Set A) ≤ pCore p A := by
    intro x hx
    rw [← hpre]
    apply hD
    rw [← hmap]
    exact map_centralizer_le_centralizer_image _ f (mem_map_of_mem f hx)
  let : Nontrivial S := S.nontrivial_iff_ne_bot.mpr hne
  have hdiv : 2 ∣ Nat.card S := hS.card_eq_or_dvd.resolve_left
    (Nat.ne_of_gt (Finite.one_lt_card (α := S)))
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 2 hdiv
  have hsD : orderOf (s : D) = 2 := (Subgroup.orderOf_coe s).trans hs
  let T := zpowers (s : D)
  let : IsElementaryAbelian 2 T := IsElementaryAbelian.zpowers_of_pow_eq_one
    (hsD ▸ pow_orderOf_eq_one (s : D))
  have hoddker : Odd (Nat.card f.ker) := by
    obtain ⟨n, hn⟩ := hk.exists_card_eq
    rw [hn]
    exact hp.pow
  obtain ⟨U, hU, hUT, _⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    f hf hoddker.coprime_two_left T
  let : IsElementaryAbelian 2 U := hU
  obtain ⟨t, htU, hts⟩ := (show (s : D) ∈ U.map f from hUT ▸ mem_zpowers (s : D))
  have ht : orderOf t = 2 := by
    have hi := injective_comp_subtype_of_coprime_ker f hoddker.coprime_two_left U
      (IsElementaryAbelian.isPGroup 2 U)
    have he := (orderOf_injective (f.comp U.subtype) hi (⟨t, htU⟩ : U)).symm
    exact (Subgroup.orderOf_coe (⟨t, htU⟩ : U)).trans (he.trans (by simpa [hts] using hsD))
  let a : MulAut (pCore p A) := MulAut.conjNormal t
  let b : MulAut (pCore p D) := MulAut.conjNormal (s : D)
  let q : pCore p A →* pCore p D :=
    (f.comp (pCore p A).subtype).codRestrict _ (fun x => by
      have hx : (x : A) ∈ (pCore p D).comap f := hpre.symm ▸ x.property
      exact hx)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    rw [← hpre]
    change f x ∈ pCore p D
    rw [hx]
    exact y.property
  have ha : Function.Involutive a := by
    have he : a ^ 2 = 1 := by
      rw [show a = MulAut.conjNormal t from rfl, ← map_pow,
        (show t ^ 2 = 1 from ht ▸ pow_orderOf_eq_one t), map_one]
    exact fun x => DFunLike.congr_fun he x
  have hb : Function.Involutive b := by
    have he : b ^ 2 = 1 := by
      rw [show b = MulAut.conjNormal (s : D) from rfl, ← map_pow,
        (show (s : D) ^ 2 = 1 from hsD ▸ pow_orderOf_eq_one (s : D)), map_one]
    exact fun x => DFunLike.congr_fun he x
  have heq (x : pCore p A) : q (a x) = b (q x) := by
    apply Subtype.ext
    change f (t * x * t⁻¹) = (s : D) * f x * (s : D)⁻¹
    rw [map_mul, map_mul, map_inv, hts]
  let qfixed : a.fixedSubgroup →* b.fixedSubgroup :=
    (q.comp a.fixedSubgroup.subtype).codRestrict _ (fun x => by
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      change b (q x.val) = q x.val
      rw [← heq, (MulAut.mem_fixedSubgroup _ _).mp x.property])
  have hqfixed : Function.Surjective qfixed := by
    intro y
    obtain ⟨x, hx, hxy⟩ := MulAut.exists_fixed_preimage_of_odd_card
      (odd_core_card hp) (odd_core_card hp) a b ha hb q hq heq y
      ((MulAut.mem_fixedSubgroup _ _).mp y.property)
    exact ⟨⟨x, (MulAut.mem_fixedSubgroup _ _).mpr hx⟩, Subtype.ext hxy⟩
  let : IsCyclic a.fixedSubgroup := cyclic_primeCore_fixedSubgroup_of_involution hp hrank hA t ht
  let : IsCyclic b.fixedSubgroup := isCyclic_of_surjective qfixed hqfixed
  let j : (centralizer (S : Set D)).subgroupOf (pCore p D) →* b.fixedSubgroup :=
    { toFun := fun x => ⟨x.val, by
        apply (MulAut.mem_fixedSubgroup _ _).mpr
        apply Subtype.ext
        change (s : D) * x.val.val * (s : D)⁻¹ = x.val.val
        have hc : (s : D) * x.val.val = x.val.val * (s : D) := x.property (s : D) s.property
        rw [hc]
        simp only [mul_inv_cancel_right]⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply isCyclic_of_injective j
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : b.fixedSubgroup => z.val) h

end Theory.GroupTheory
