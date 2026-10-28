module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveResidualCenter
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
public import Theory.GroupTheory.SemidirectProductNormalizerAction
public import Theory.SpecificGroups.Suzuki.SmallAutomorphisms

/-!
# Native squaring symmetry of the original quintic core

The proved Sz(2) quotient realizes every automorphism of its normal
five-subgroup. Coprime normalizer lifting realizes those same automorphisms
on every actual order-five subgroup of H. The Frattini argument also makes
its normalizer supplement the full core, so [Q,A] is H-normal.

The resulting squaring element preserves Q, A and the literal residual
[Q,A]. It fixes or inverts any cyclic-four generator of C_Q(A). These are
the native symmetry conditions required by semilinear extension recognition;
no cyclicity, residual class, order-four complement, or Ree model is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

private theorem five_normalizer_of_quotient
    {K : Type*} [Group K] [Finite K]
    (f : K →* FiveFour.Group) (hf : Function.Surjective f)
    (hker : IsPGroup 2 f.ker) (A : Subgroup K) (hA : Nat.card A = 5) :
    Function.Surjective A.normalizerMonoidHom ∧ normalizer (A : Set K) ⊔ f.ker = ⊤ := by
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hAp : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  let : Fact (IsPGroup 5 A) := ⟨hAp⟩
  have hd : Disjoint A f.ker := hAp.disjoint_of_coprime hker (by decide)
  have hinj : Function.Injective (f.subgroupMap A) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply bot_unique
    intro x hx
    have hfx : f (x : K) = 1 := congrArg Subtype.val (show f.subgroupMap A x = 1 from hx)
    exact Subtype.ext (hd.le_bot ⟨x.property, hfx⟩)
  let B := A.map f
  let e : A ≃* B := MulEquiv.ofBijective (f.subgroupMap A)
    ⟨hinj, f.subgroupMap_surjective A⟩
  have hB : Nat.card B = 5 := (Nat.card_congr e.toEquiv).symm.trans hA
  let L := (SemidirectProduct.inl : FiveFour.Cyclic 5 →* FiveFour.Group).range
  have hL : Nat.card L = 5 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inl_injective).toEquiv]
    exact Nat.card_zmod 5
  have hBL : B ≤ L := by
    let r : B →* FiveFour.Cyclic 4 := SemidirectProduct.rightHom.comp B.subtype
    have hc : Nat.card r.range = 1 := Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 5 4)
      (by simpa only [hB] using card_range_dvd r)
      (by simpa [FiveFour.Cyclic] using r.range.card_subgroup_dvd_card)
    have hr : r.range = ⊥ := r.range.eq_bot_of_card_eq hc
    intro b hb
    change b ∈ (SemidirectProduct.inl : FiveFour.Cyclic 5 →* FiveFour.Group).range
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    have hm : r ⟨b, hb⟩ ∈ r.range := ⟨⟨b, hb⟩, rfl⟩
    rw [hr] at hm
    exact hm
  have hBeq : B = L := eq_of_le_of_card_ge hBL (by rw [hB, hL])
  have hφ : Function.Surjective FiveFour.action := by
    apply ((Nat.bijective_iff_injective_and_card FiveFour.action).mpr
      ⟨FiveFour.action_injective, ?_⟩).2
    rw [IsCyclic.card_mulAut]
    simp [FiveFour.Cyclic]
    decide
  have hfull : Function.Surjective B.normalizerMonoidHom := by
    rw [hBeq]
    exact SemidirectProduct.normalizerMonoidHom_inl_surjective FiveFour.action hφ
  have hBnormal : B.Normal := by
    rw [hBeq]
    change (SemidirectProduct.inl : FiveFour.Cyclic 5 →* FiveFour.Group).range.Normal
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  let := hBnormal
  obtain ⟨n, hn⟩ := hker.exists_card_eq
  have hcop : Nat.Coprime 5 (Nat.card f.ker) := by
    rw [hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n
  have hN := normalizer_map_eq_of_coprime_kernel 5 A f hf hcop
  refine ⟨normalizerMonoidHom_surjective_of_lift A B f e (fun _ => rfl) hN.le hfull, ?_⟩
  have hm : (normalizer (A : Set K)).map f = ⊤ := by
    rw [← hN]
    exact B.normalizer_eq_top
  have hh := congrArg (Subgroup.comap f) hm
  simpa only [Subgroup.comap_map_eq, Subgroup.comap_top] using hh

private theorem conjugate_four_generator
    {K : Type*} [Group K] [Finite K] (t s : K) (ht : orderOf t = 4)
    (hs : s ∈ normalizer (zpowers t : Set K)) :
    s * t * s⁻¹ = t ∨ s * t * s⁻¹ = t⁻¹ := by
  classical
  have ht4 : t ^ 4 = 1 := ht ▸ pow_orderOf_eq_one t
  have hmem : s * t * s⁻¹ ∈ zpowers t := (hs t).mp (mem_zpowers t)
  have horder : orderOf (s * t * s⁻¹) = 4 := (MulAut.conj s).orderOf_eq t |>.trans ht
  rw [mem_zpowers_iff_mem_range_orderOf, ht] at hmem
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hmem
  have hn4 := Finset.mem_range.mp hn
  interval_cases n
  · simp only [pow_zero] at he
    rw [← he, orderOf_one] at horder
    contradiction
  · exact Or.inl (by simpa only [pow_one] using he.symm)
  · have htwo : (s * t * s⁻¹) ^ 2 = 1 := by rw [← he, ← pow_mul]; exact ht4
    have hd := orderOf_dvd_of_pow_eq_one htwo
    rw [horder] at hd
    norm_num at hd
  · apply Or.inr
    rw [← he]
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using ht4

private theorem le_normalizer_commutator_of_le_normalizers
    {G : Type*} [Group G] (X Q A : Subgroup G)
    (hXQ : X ≤ normalizer (Q : Set G))
    (hXA : X ≤ normalizer (A : Set G)) :
    X ≤ normalizer ((⁅Q, A⁆ : Subgroup G) : Set G) := by
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq]
  rw [map_commutator]
  rw [mem_normalizer_iff_map_conj_eq.mp (hXQ hx),
    mem_normalizer_iff_map_conj_eq.mp (hXA hx)]

variable {G : Type*} [Group G] [Finite G]

/-- The full local five-normalizer acts as Aut(A), supplements Q and
normalizes the actual residual. This holds for either exact core order. -/
theorem source_quintic_five_normalizer_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    Function.Surjective (A.normalizerMonoidHom.comp
      (H.subgroupOf (normalizer (A : Set G))).subtype) ∧
      (H ⊓ normalizer (A : Set G)) ⊔ H.pCoreIn 2 = H ∧
      H ≤ normalizer ((⁅H.pCoreIn 2,A⁆ : Subgroup G) : Set G) := by
  obtain ⟨_, ⟨eSuz⟩⟩ := source_quintic_suzuki_zero_quotient
    hG T hempty hM hu hmany hcard e H hH hi
  let eF := eSuz.trans FiveFour.suzukiZeroEquiv.symm
  let f : H →* FiveFour.Group := eF.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 H))
  have hf : Function.Surjective f := eF.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = pCore 2 H := by
    ext h
    change eF (QuotientGroup.mk' (pCore 2 H) h) = 1 ↔ h ∈ pCore 2 H
    exact (map_eq_one_iff _ eF.injective).trans
      (QuotientGroup.eq_one_iff (N := pCore 2 H) h)
  obtain ⟨hsurj, hcover⟩ := five_normalizer_of_quotient f hf
    (hker.symm ▸ pCore_isPGroup) (A.subgroupOf H)
    ((Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv).trans hA)
  have hcoverG : (H ⊓ normalizer (A : Set G)) ⊔ H.pCoreIn 2 = H := by
    have hm := congrArg (Subgroup.map H.subtype) hcover
    rw [Subgroup.map_sup, hker, ← subgroupOf_normalizer_eq hAH,
      subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype] at hm
    simpa only [pCoreIn, inf_comm] using hm
  have hHQ : H ≤ normalizer (H.pCoreIn 2 : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  refine ⟨normalizerMonoidHom_restrict_surjective A H hAH hsurj, hcoverG, ?_⟩
  have hX := le_normalizer_commutator_of_le_normalizers
    (H ⊓ normalizer (A : Set G)) (H.pCoreIn 2) A
    (inf_le_left.trans hHQ) inf_le_right
  have hsup := sup_le
    hX
    (normalizer_commutator_ge_left _ _)
  simpa only [hcoverG] using hsup

/-- An actual element of H squares A, preserves the original core and
residual, and fixes or inverts every cyclic-four generator of C_Q(A). -/
theorem source_quintic_five_squaring_element
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    let Q := H.pCoreIn 2
    let R := ⁅Q,A⁆
    let B := Q ⊓ centralizer (A : Set G)
    ∃ s : G, s ∈ H ∧ s ∈ normalizer (A : Set G) ∧
      s ∈ normalizer (Q : Set G) ∧ s ∈ normalizer (R : Set G) ∧
      s ∈ normalizer (B : Set G) ∧
      (∀ a ∈ A, s * a * s⁻¹ = a ^ 2) ∧
      ∀ t : G, orderOf t = 4 → zpowers t = B →
        s * t * s⁻¹ = t ∨ s * t * s⁻¹ = t⁻¹ := by
  let Q := H.pCoreIn 2
  obtain ⟨hfull, _, hHR⟩ := source_quintic_five_normalizer_action
    hG T hempty hM hu hmany hcard e H hH hi A hAH hA
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let : IsCyclic A := isCyclic_of_prime_card hA
  let : CommGroup A := IsCyclic.commGroup
  let square : MulAut A := { powCoprime (by rw [hA]; decide : (Nat.card A).Coprime 2) with
    map_mul' := fun x y => mul_pow x y 2 }
  obtain ⟨s, hs⟩ := hfull square
  have hsQ : (s : G) ∈ normalizer (Q : Set G) :=
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))) s.property
  have hsB : (s : G) ∈ normalizer ((Q ⊓ centralizer (A : Set G) : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hsQ, normalizer_le_normalizer_centralizer A s.val.property⟩
  refine ⟨s, s.property, s.val.property, hsQ, hHR s.property, hsB, ?_, ?_⟩
  · intro a ha
    exact congrArg (fun α : MulAut A => (α ⟨a, ha⟩ : G)) hs
  · intro t ht hgen
    exact conjugate_four_generator t s ht (hgen.symm ▸ hsB)

/-- The actual conjugation action admits a residual-preserving squaring
automorphism. Every chosen cyclic fixed root is retained up to inversion. -/
theorem source_quintic_five_squaring_automorphism
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5) :
    let Q := H.pCoreIn 2
    let R := ⁅Q,A⁆
    let B := Q ⊓ centralizer (A : Set G)
    ∃ (ρ : A →* MulAut Q) (σ : MulAut Q),
      (∀ a q, (ρ a q : G) = (a : G) * (q : G) * (a : G)⁻¹) ∧
      (∀ a, σ * ρ a * σ⁻¹ = ρ (a ^ 2)) ∧
      (∀ a q, (ρ a q : G) ∈ R ↔ (q : G) ∈ R) ∧
      (∀ q, (σ q : G) ∈ R ↔ (q : G) ∈ R) ∧
      ∀ t : Q, orderOf (t : G) = 4 → zpowers (t : G) = B →
        (∀ a, ρ a t = t) ∧ (σ t = t ∨ σ t = t⁻¹) := by
  let Q := H.pCoreIn 2
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  let f : H →* MulAut Q := Q.normalizerMonoidHom.comp (inclusion hHQ)
  let ρ : A →* MulAut Q := f.comp (inclusion hAH)
  obtain ⟨s, hsH, _, _, hsR, _, hs, hroot⟩ := source_quintic_five_squaring_element
    hG T hempty hM hu hmany hcard e H hH hi A hAH hA
  let sH : H := ⟨s, hsH⟩
  let σ := f sH
  refine ⟨ρ, σ, fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro a
    have he : sH * inclusion hAH a * sH⁻¹ = inclusion hAH (a ^ 2) := Subtype.ext (hs a a.property)
    change f sH * f (inclusion hAH a) * (f sH)⁻¹ = f (inclusion hAH (a ^ 2))
    rw [← map_inv, ← map_mul, ← map_mul, he]
  · intro a q
    exact ((mem_normalizer_iff.mp (normalizer_commutator_ge_right Q A a.property)) (q : G)).symm
  · intro q
    exact ((mem_normalizer_iff.mp hsR) (q : G)).symm
  · intro t ht hgen
    have htA : (t : G) ∈ centralizer (A : Set G) := (hgen.le (mem_zpowers (t : G))).2
    refine ⟨fun a => Subtype.ext (mul_inv_eq_iff_eq_mul.mpr
      (mem_centralizer_iff.mp htA a a.property)), ?_⟩
    rcases hroot t ht hgen with hh | hh
    · exact Or.inl (Subtype.ext hh)
    · exact Or.inr (Subtype.ext hh)

end CFSG.Quasithin.Chapter14.Section06
