module

public import Theory.SpecificGroups.GL2.ThreeResidualImages.Generation
public import Theory.SpecificGroups.GL2.ThreeResidualImages.QuaternionCore

/-!
# Two-perfect images in GL₂(3)

A two-perfect subgroup lies in the determinant kernel. If it contains two
independent cubic elements, their actual embedded subgroups generate SL₂(3).
Otherwise its cubic elements lie in a single cyclic subgroup, normal in the
subgroup under consideration. The quotient has exponent dividing four, so
two-perfectness makes that cyclic subgroup the whole group.

If D has elementary abelian two-core and cubic quotient, D has exponent
dividing six. Its two-perfect matrix image therefore cannot be SL₂(3),
which contains elements of order four; an image of order three kills O₂(D).
This proves precisely the small-image consequence of the source's assertion
that A₄ is not involved in SL₂(3), without assuming a section classification.

The imported quaternion-core calculation uses the intrinsic O₂(H) and
retains its actual inclusion in GL₂(3). These results supply the ternary
matrix steps in Aschbacher–Smith, *The Classification of Quasithin Groups*,
F.6.16, printed pp.308–309 (PDF319–320, combined manuscript 1 March 2004).
-/

public section
open Matrix Subgroup
namespace Matrix.GeneralLinearGroup

/-- Nontrivial two-perfect matrix subgroups are cubic or the determinant kernel. -/
theorem three_twoPerfect_subgroup (K : Subgroup (GL (Fin 2) (ZMod 3))) (hp : IsPPerfect 2 K)
    (hne : K ≠ ⊥) : Nat.card K = 3 ∨ K = threeSpecialLinear := by
  have hKS := three_pPerfect_le_specialLinear K hp
  by_cases hSK : threeSpecialLinear ≤ K
  · exact Or.inr (le_antisymm hKS hSK)
  have hcubic : ∃ c : (GL (Fin 2) (ZMod 3)), c ∈ K ∧ c ^ 3 = 1 ∧ c ≠ 1 := by
    by_contra hn
    push Not at hn
    have htwo : IsPGroup 2 K := by
      intro x
      refine ⟨2, Subtype.ext ?_⟩
      exact hn (x.val ^ 4) (K.pow_mem x.property 4) (by
        rw [← pow_mul]
        exact three_special_pow_twelve x.val (hKS x.property))
    have hbot := hp ⊥ inferInstance (htwo.of_equiv QuotientGroup.quotientBot.symm)
    apply hne
    apply (eq_bot_iff_forall K).mpr
    intro x hx
    have h : (⟨x,hx⟩ : K) ∈ (⊥ : Subgroup K) := hbot ▸ mem_top _
    exact congrArg Subtype.val (mem_bot.mp h)
  obtain ⟨c, hcK, hc3, hc1⟩ := hcubic
  let C := zpowers c
  have hCK : C ≤ K := zpowers_le.mpr hcK
  have hall : ∀ y : (GL (Fin 2) (ZMod 3)), y ∈ K → y ^ 3 = 1 → y ∈ C := by
    intro y hyK hy3
    by_contra hyC
    apply hSK
    exact three_cubic_pair_generate K c y hcK hyK hc3 hy3 hc1
      (fun h => hyC (h ▸ C.one_mem))
      (fun h => hyC (h ▸ mem_zpowers c))
      (fun h => hyC (h ▸ C.pow_mem (mem_zpowers c) 2))
  let N := C.subgroupOf K
  have hN3 (n : K) (hn : n ∈ N) : n.val ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp
      ((orderOf_dvd_of_mem_zpowers hn).trans (orderOf_dvd_of_pow_eq_one hc3))
  let _ : N.Normal := ⟨by
    intro n hn g
    apply hall _ (g * n * g⁻¹).property
    change ((MulAut.conj g.val) n.val) ^ 3 = 1
    rw [← map_pow, hN3 n hn, map_one]⟩
  have hq : IsPGroup 2 (K ⧸ N) := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    refine ⟨2, ?_⟩
    change (QuotientGroup.mk' N x) ^ 4 = 1
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    apply hall _ (K.pow_mem x.property 4)
    rw [← pow_mul]
    exact three_special_pow_twelve x.val (hKS x.property)
  have hNt := hp N inferInstance hq
  have hKC : K ≤ C := by
    intro x hx
    exact show (⟨x,hx⟩ : K) ∈ N from hNt ▸ mem_top _
  left
  rw [le_antisymm hKC hCK, Nat.card_zpowers, orderOf_eq_prime hc3 hc1]

/-- Distinct nontrivial two-perfect subgroups generate the actual determinant kernel.
This is the image-generation form used when the two local images are distinct. -/
theorem three_distinct_twoPerfect_join (C D : Subgroup (GL (Fin 2) (ZMod 3)))
    (hC : IsPPerfect 2 C) (hD : IsPPerfect 2 D)
    (hCne : C ≠ ⊥) (hDne : D ≠ ⊥) (hne : C ≠ D) :
    C ⊔ D = threeSpecialLinear := by
  rcases three_twoPerfect_subgroup C hC hCne with hc | hc
  · rcases three_twoPerfect_subgroup D hD hDne with hd | hd
    · exact three_distinct_cubic_join C D hc hd hne
    · rw [hd]
      exact sup_eq_right.mpr (three_pPerfect_le_specialLinear C hC)
  · rw [hc]
    exact sup_eq_left.mpr (three_pPerfect_le_specialLinear D hD)

/-- Every homomorphism in the elementary-core cubic-quotient case kills that core. -/
theorem three_kills_elementary_twoCore {D : Type*} [Group D] [Finite D]
    (hp : IsPPerfect 2 D) [IsElementaryAbelian 2 (pCore 2 D)]
    (hquot : Nat.card (D ⧸ pCore 2 D) = 3) (f : D →* (GL (Fin 2) (ZMod 3))) :
    pCore 2 D ≤ f.ker := by
  have hD6 (d : D) : d ^ 6 = 1 := by
    have h3 : d ^ 3 ∈ pCore 2 D := by
      apply (QuotientGroup.eq_one_iff _).mp
      have h := pow_card_eq_one' (x := QuotientGroup.mk' (pCore 2 D) d)
      rw [hquot, ← map_pow] at h
      exact h
    simpa only [← pow_mul] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (d ^ 3) h3
  have hR6 (x : f.range) : x.val ^ 6 = 1 := by
    obtain ⟨d, hd⟩ := x.property
    rw [← hd, ← map_pow, hD6, map_one]
  by_cases hbot : f.range = ⊥
  · intro d _
    exact mem_bot.mp (hbot ▸ (show f d ∈ f.range from ⟨d, rfl⟩))
  have hR : Nat.card f.range = 3 := by
    rcases three_twoPerfect_subgroup f.range
      (hp.of_surjective f.rangeRestrict f.rangeRestrict_surjective) hbot with h | h
    · exact h
    · obtain ⟨x,hx,hx6⟩ := three_special_exists_pow_six_ne
      exact (hx6 (hR6 ⟨x, h.symm ▸ hx⟩)).elim
  intro d hd
  have h2 : (f d) ^ 2 = 1 := by
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian d hd, map_one]
  have h3 : (f d) ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := f.rangeRestrict d)
    rw [hR] at h
    exact congrArg Subtype.val h
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3)
      (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3))
end Matrix.GeneralLinearGroup
