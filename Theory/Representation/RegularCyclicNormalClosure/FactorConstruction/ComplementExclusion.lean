module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.ComplementKernel

/-!
# Excluding the local complement alternative

Every ambient involution in the pointwise fixer fixes its entire local
fixed-space orbit. In the complement case the orbit kernel centralizes the
cyclic actor. An involution commuting with an odd regular actor fixes its
moved space: its permutation of nonzero vectors is an odd-order translation.
It also fixes F, giving the prohibited small ambient displacement rank.

Thus the pointwise fixer is odd. Its transitive fixed-space orbit has
cardinality equal to the binary moved space, an even number, contradicting
orbit-stabilizer. All quotient, kernel and involution ranks use the actual
maps; no lower rank bound is asserted for the quotient action.

This excludes GLS Number 2 C.14.2(iii) in the maximal-intersection approach
to Aschbacher–Smith E.6.24, printed p.255.
-/

public section

open Module Subgroup Representation.BinaryOffender
namespace Representation.RegularCyclicNormalClosure
open FactorConstruction
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W] {ρ : Representation (ZMod 2) A W} {C : Subgroup A}

/-- A commuting involution fixes the moved space of an odd regular actor. -/
theorem Input.involution_fixes_moved_of_commutes (h : Input ρ C)
    (t : A) (ht : t ^ 2 = 1) (hcomm : ∀ c ∈ C, Commute c t) :
    ∀ v ∈ displacementSpan ρ C ⊤, ρ t v = v := by
  let S := displacementSpan ρ C ⊤
  have hne : S ≠ ⊥ := by
    intro he
    have hh := h.moved_dimension_gt_one
    change 1 < finrank (ZMod 2) S at hh
    rw [he, finrank_bot] at hh
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have htN : t ∈ normalizer (C : Set A) := centralizer_le_normalizer _
    (mem_centralizer_iff.mpr (fun c hc => (hcomm c hc).eq))
  have hS := displacementSpan_map_of_normalized ρ C t (mem_normalizer_iff_map_conj_eq.mp htN)
  have htu : ρ t u ∈ S := by
    change ρ t u ∈ displacementSpan ρ C ⊤
    rw [← hS]
    exact Submodule.mem_map_of_mem hu
  have htu0 : ρ t u ≠ 0 := by
    intro he
    apply hu0
    apply (ρ.apply_bijective t).injective
    simpa only [map_zero] using he
  obtain ⟨c, hc, _⟩ := h.regular u hu hu0 (ρ t u) htu htu0
  have hact (c : C) (v : W) : ρ (c : A) (ρ t v) = ρ t (ρ (c : A) v) := by
    simp only [← Module.End.mul_apply, ← map_mul]
    rw [(hcomm c c.property).eq]
  have htt (v : W) : ρ t (ρ t v) = v := by
    simpa only [pow_two, map_mul, Module.End.mul_apply, map_one, Module.End.one_apply]
      using congrArg (fun a => ρ a v) ht
  have hcc : ρ ((c * c : C) : A) u = u := by
    change ρ ((c : A) * (c : A)) u = u
    rw [map_mul, Module.End.mul_apply, hc, hact, hc, htt]
  obtain ⟨z, _, hz⟩ := h.regular u hu hu0 u hu hu0
  have hc2 : c ^ 2 = 1 := by
    rw [pow_two]
    exact (hz (c * c) hcc).trans (hz 1 (by simp)).symm
  have hodd : Odd (orderOf c) := h.odd_card.of_dvd_nat (orderOf_dvd_natCard c)
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hodd.coprime_two_left
  have hc1 : c = 1 := by rw [hc2, one_pow] at hn; exact hn.symm
  have hfixu : ρ t u = u := by rw [hc1] at hc; simpa using hc.symm
  intro v hv
  by_cases hv0 : v = 0
  · simp [hv0]
  obtain ⟨d, hd, _⟩ := h.regular u hu hu0 v hv hv0
  rw [← hd, ← hact, hfixu]

variable [Finite A]

/-- The complement alternative contradicts the ambient involution bound.
All local involutions lie in the orbit kernel; that kernel centralizes the
cyclic actor, and regularity makes them fix its moved space. -/
theorem Input.not_complement_onFixer (h : Input ρ C)
    (F : Submodule (ZMod 2) W) (hFU : F ≤ fixedSpace ρ C)
    (hsmall : finrank (ZMod 2) (fixedSpace ρ C) ≤ finrank (ZMod 2) F +
      finrank (ZMod 2) (displacementSpan ρ C ⊤))
    (hmax : ∀ b : A, (fixedSpace ρ C).map (ρ b) ≠ fixedSpace ρ C →
      finrank (ZMod 2) ↥(fixedSpace ρ C ⊓ (fixedSpace ρ C).map (ρ b)) ≤ finrank (ZMod 2) F)
    (hlocal : GoldschmidtONan.Input (quotientOnFixer ρ F)
      (C.subgroupOf (pointwiseFixer ρ F))) :
    ¬ GoldschmidtONan.ComplementCase (quotientOnFixer ρ F)
      (C.subgroupOf (pointwiseFixer ρ F)) := by
  intro hs
  let : Finite (W ⧸ F) := Finite.of_surjective F.mkQ F.mkQ_surjective
  have hsub := hlocal.suborbitGeometry
  have hCK := (le_pointwiseFixer_iff ρ C F).mpr hFU
  have hodd : Odd (Nat.card (pointwiseFixer ρ F)) := by
    by_contra ho
    have hdiv : 2 ∣ Nat.card (pointwiseFixer ρ F) :=
      even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp ho)
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := pointwiseFixer ρ F) 2 hdiv
    have htA : orderOf (t : A) = 2 := (orderOf_injective
      (pointwiseFixer ρ F).subtype Subtype.val_injective t).trans ht
    have hker : t ∈ (fixedOrbitPermutation (quotientOnFixer ρ F)
        (C.subgroupOf (pointwiseFixer ρ F))).ker := by
      apply (mem_fixedOrbitPermutation_ker _ _ t).mpr
      rintro _ ⟨x, rfl⟩
      dsimp only
      have hm := h.involution_preserves_local_orbit F hFU hmax t x htA
      have hh := congrArg (fun L : Submodule (ZMod 2) W => L.map F.mkQ) hm
      rw [map_quotientOnFixer F ((fixedSpace ρ C).map (ρ (x : A))) t,
        map_quotientOnFixer F (fixedSpace ρ C) x] at hh
      simpa only [h.fixedSpace_quotientOnFixer F hFU] using hh
    have hcent := complement_kernel_centralizes_actor hlocal hs hsub t hker
    have ht2 : (t : A) ^ 2 = 1 := by simpa only [← htA] using pow_orderOf_eq_one (t : A)
    have hS := h.involution_fixes_moved_of_commutes t ht2 (by
      intro c hc
      exact (hcent ⟨c, hCK hc⟩ hc).map (pointwiseFixer ρ F).subtype)
    have hFS : F ⊔ displacementSpan ρ C ⊤ ≤ fixedSpace ρ (zpowers (t : A)) := by
      apply sup_le
      · intro v hv
        exact (mem_fixedSpace_zpowers_iff ρ t v).mpr ((mem_pointwiseFixer ρ F t).mp t.property v hv)
      · intro v hv
        exact (mem_fixedSpace_zpowers_iff ρ t v).mpr (hS v hv)
    have hdim := F.finrank_sup_add_finrank_inf_eq (displacementSpan ρ C ⊤)
    rw [(h.split.disjoint.mono_left hFU).eq_bot, finrank_bot, add_zero] at hdim
    have hle := Submodule.finrank_mono hFS
    have hsplit := Submodule.finrank_add_eq_of_isCompl h.split
    have hr := fixedCodim_add_finrank ρ (zpowers (t : A))
    have hb := h.no_small_involutions (t : A) htA
    omega
  have htwo : 2 ∣ Nat.card (GoldschmidtONan.fixedOrbit (quotientOnFixer ρ F)
      (C.subgroupOf (pointwiseFixer ρ F))) := by
    rw [hs.1, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
      h.moved_finrank_quotientOnFixer F hFU]
    exact dvd_pow_self 2 (by have := h.moved_dimension_gt_one; omega)
  exact hodd.not_two_dvd_nat (htwo.trans (fixedOrbit_card_dvd (σ := quotientOnFixer ρ F)
    (Y := C.subgroupOf (pointwiseFixer ρ F))))

end Representation.RegularCyclicNormalClosure
