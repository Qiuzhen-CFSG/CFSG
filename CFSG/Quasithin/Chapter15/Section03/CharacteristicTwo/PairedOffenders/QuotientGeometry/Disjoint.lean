module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedOffenders.QuotientGeometry.Transport

/-!
# The transposition and disjoint-transposition quotient calculations

Parity and the order formula prove (II). The uniqueness of the full pair-swap
group in a common two-overgroup reduces every conjugate in (III) to the canonical
one. Its intersection with the block kernel has four elements. The resulting
bound on the three rank terms is the input to paired replacement.

Source: Aschbacher–Smith, proof of 15.3.25, printed pp.1133–1134.
-/

public section

open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.Offenders
open CFSG.Quasithin.ChapterB.Offenders.Eight

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient

/-- The marked even four-group is the image of the actual alternating part,
so parity can be read in the quotient for every subgroup of the Sylow group. -/
theorem quotientImage_le_evenFour_iff {A : Subgroup Perm} (hAS : A ≤ canonicalSylow) :
    quotientImage A ≤ evenFour ↔ A ≤ alternatingGroup (Fin 8) := by
  change (A.subgroupOf canonicalSylow).map quotientMap ≤ evenSylow.map quotientMap ↔ _
  rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_map_eq_self
    (show quotientMap.ker ≤ evenSylow by
      rw [quotientMap, QuotientGroup.ker_mk']; exact sylowCore_le_evenSylow)]
  constructor
  · intro h a ha
    exact h (show (⟨a, hAS ha⟩ : SylowGroup) ∈ A.subgroupOf canonicalSylow from ha)
  · intro h a ha
    exact h ha

private theorem transposition_not_le_alternating {A : Subgroup Perm}
    (hA : EightCase.transposition.Realizes A) : ¬ A ≤ alternatingGroup (Fin 8) := by
  obtain ⟨g, rfl⟩ := hA
  intro h
  have hh := h (mem_map_of_mem (MulAut.conj g).toMonoidHom
    (pairSwap_mem (n := 8) (m := 1) 0 (by decide)))
  change Equiv.Perm.sign (g * pairSwap 8 0 * g⁻¹) = 1 at hh
  have hs : Equiv.Perm.sign (pairSwap 8 0) = -1 := by decide +kernel
  simp only [map_mul, map_inv, hs] at hh
  have he := congrArg (fun x => (Equiv.Perm.sign g)⁻¹ * x * Equiv.Perm.sign g) hh
  simp at he

/-- Calculation (II) for every conjugate transposition subgroup. -/
theorem transposition_position {A : Subgroup Perm}
    (hA : EightCase.transposition.Realizes A) (hAS : A ≤ canonicalSylow) :
    Position .transposition evenFour (quotientImage A) := by
  have hcard : Nat.card A = 2 := by
    have he := hA.isElementaryTwo (isElementaryTwo_disjointTranspositions 1 (by decide))
    rw [he.card_eq_two_pow_rank, (EightCase.dimensions hA).1]
    rfl
  have hnon : quotientImage A ≠ ⊥ :=
    fun h => transposition_not_le_blockCore hA ((quotientImage_eq_bot_iff hAS).mp h)
  have hgt := (Subgroup.one_lt_card_iff_ne_bot (quotientImage A)).mpr hnon
  have hc := card_inf_mul_card_quotientImage hAS
  have hk := Nat.card_pos (α := (A ⊓ blockCore : Subgroup Perm))
  rw [hcard] at hc
  refine ⟨by nlinarith, ?_⟩
  exact fun h => transposition_not_le_alternating hA ((quotientImage_le_evenFour_iff hAS).mp h)

theorem transposition_ranks {A : Subgroup Perm}
    (hA : EightCase.transposition.Realizes A) (hAS : A ≤ canonicalSylow) :
    rank (quotientImage A) = 1 ∧ rank (A ⊓ blockCore) = 0 := by
  have hr : rank (quotientImage A) = 1 := by
    rw [rank, (transposition_position hA hAS).1]; rfl
  have hk := rank_inf_add_rank_quotientImage hAS
  have ha := (EightCase.dimensions hA).1
  change rank A = 1 at ha
  exact ⟨hr, by omega⟩

private def dCoreWords (i : Fin 4) : Perm :=
  dWords ⟨3 * (i.val % 2) + 12 * (i.val / 2), by omega⟩

private theorem mem_D_inf_blockCore (x : Perm) :
    x ∈ (D 8 ⊓ blockCore : Subgroup Perm) ↔ ∃ i, dCoreWords i = x := by
  have h : ∀ i j, dWords i = coreWords j → ∃ k, dCoreWords k = dWords i := by decide +kernel
  have hd : ∀ k, ∃ i, dWords i = dCoreWords k := by decide +kernel
  have hk : ∀ k, ∃ j, coreWords j = dCoreWords k := by decide +kernel
  constructor
  · rintro ⟨hx, j, hj⟩
    obtain ⟨i, hi⟩ := (mem_disjointTranspositions_iff 4 x).mp hx
    obtain ⟨k, he⟩ := h i j (hi.trans hj.symm)
    exact ⟨k, he.trans hi⟩
  · rintro ⟨k, rfl⟩
    exact ⟨(mem_disjointTranspositions_iff 4 _).mpr (hd k), hk k⟩

theorem card_D_inf_blockCore : Nat.card (D 8 ⊓ blockCore : Subgroup Perm) = 4 := by
  have e : (D 8 ⊓ blockCore : Subgroup Perm) ≃ Set.range dCoreWords :=
    Equiv.setCongr (by ext x; exact mem_D_inf_blockCore x)
  rw [Nat.card_congr e,
    ← Nat.card_congr (Equiv.ofInjective dCoreWords (by decide +kernel))]
  simp

theorem card_quotientImage_D : Nat.card (quotientImage (D 8)) = 4 := by
  have hc := card_inf_mul_card_quotientImage D_le_canonicalSylow
  have hD : Nat.card (D 8) = 16 := card_disjointTranspositions 4
  rw [card_D_inf_blockCore, hD] at hc
  omega

theorem quotientImage_D_ne_evenFour : quotientImage (D 8) ≠ evenFour := by
  intro he
  have h : (D 8).subgroupOf canonicalSylow ≤ evenSylow := by
    have hh : ((D 8).subgroupOf canonicalSylow).map quotientMap ≤
        evenSylow.map quotientMap := he.le
    rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_map_eq_self
      (show quotientMap.ker ≤ evenSylow by
        rw [quotientMap, QuotientGroup.ker_mk']; exact sylowCore_le_evenSylow)] at hh
    exact hh
  have hs : (⟨pairSwap 8 0, sylowGenerators_mem 0⟩ : SylowGroup) ∈
      (D 8).subgroupOf canonicalSylow := pairSwap_mem 0 (by decide)
  have hp := h hs
  change Equiv.Perm.sign (pairSwap 8 0) = 1 at hp
  exact (by decide +kernel : Equiv.Perm.sign (pairSwap 8 0) ≠ 1) hp

/-- Calculation (III) for every disjoint-transposition offender in the fixed
Sylow: the preceding Sylow uniqueness theorem identifies its actual image. -/
theorem disjoint_position {A : Subgroup Perm} (hA : EightCase.disjoint.Realizes A)
    (hAS : A ≤ canonicalSylow) : Position .disjoint evenFour (quotientImage A) := by
  have he : A = D 8 := conjugate_D_eq_of_le_isPGroup canonicalSylow.isPGroup'
    D_le_canonicalSylow hA hAS
  subst A
  have : IsElementaryAbelian 2 (D 8) := isElementaryTwo_D8.2
  have : IsElementaryAbelian 2 ((D 8).subgroupOf canonicalSylow) :=
    IsElementaryAbelian.subgroupOf D_le_canonicalSylow
  exact ⟨card_quotientImage_D, IsElementaryAbelian.map quotientMap,
    quotientImage_D_ne_evenFour⟩

theorem disjoint_ranks {A : Subgroup Perm} (hA : EightCase.disjoint.Realizes A)
    (hAS : A ≤ canonicalSylow) :
    rank (quotientImage A) = 2 ∧ rank (A ⊓ blockCore) = 2 := by
  have he : A = D 8 := conjugate_D_eq_of_le_isPGroup canonicalSylow.isPGroup'
    D_le_canonicalSylow hA hAS
  subst A
  constructor
  · rw [rank, card_quotientImage_D]; rfl
  · rw [rank, card_D_inf_blockCore]; rfl

variable {G H : Type*} [Group G] [Group H]

/-- The concrete disjoint/disjoint calculation supplies the replacement bound
without any assumed quotient positions or numerical ranks. -/
theorem disjoint_paired_rank_bound {S A : Subgroup G} {f g : G →* Perm} {q : G →* H}
    (d : SylowCoordinates S f q) (e : SylowCoordinates S g q)
    (hAS : A ≤ S) (hP : q.ker.map f = blockCore) (hP' : q.ker.map g = blockCore)
    (hA : EightCase.disjoint.Realizes (A.map f))
    (hA' : EightCase.disjoint.Realizes (A.map g)) :
    rank (A.map q) + rank (A.map f ⊓ q.ker.map f) + rank ((A ⊓ q.ker).map g) ≤ 6 := by
  have hd := disjoint_ranks hA (d.action_image_le hAS)
  have he := disjoint_ranks hA' (e.action_image_le hAS)
  have hq := d.rank_quotient_image hAS
  have hb := kernel_action_rank_le A g q
  rw [hP'] at hb
  rw [hP]
  omega

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.PairedQuotient

end
