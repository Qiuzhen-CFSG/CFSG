module

public import Theory.GroupTheory.InvolutionTransfer
public import Theory.GroupTheory.PResidual.Defs

/-!
# Thompson transfer and the two-residual

If every conjugate in a Sylow two-subgroup of an involution has nontrivial
image under an order-two character, transfer has nontrivial value on that
involution. The transfer kernel has a two-group quotient, so it contains
O²(G). Thus the involution lies outside O²(G).

The proof refines the existing no-normal-index-two transfer argument by
retaining the value of transfer on the specified involution. In particular,
this conclusion concerns the two-residual, not the two-core O₂(G).

Source: Kurzweil–Stellmacher, Lemma 12.1.1, printed pp.338–339; used in
Aschbacher–Smith, proof of 16.4.9(2), printed p.1192 of the combined
manuscript of 1 March 2004.
-/

namespace Sylow

/-- An involution whose Sylow conjugates avoid an order-two character kernel lies outside O²(G). -/
public theorem not_mem_twoResidual_of_nonfusion_character
    {G A : Type*} [Group G] [CommGroup A] [Finite G] [Finite A]
    (S : Sylow 2 G) (character : S →* A) (hcard : Nat.card A = 2)
    (element : S) (horder : orderOf element = 2)
    (hnot : ∀ other : S, IsConj (element : G) (other : G) → character other ≠ 1) :
    (element : G) ∉ pResidual 2 G := by
  classical
  have hnontrivial : character element ≠ 1 := hnot element (IsConj.refl _)
  have heq (left right : A) (hleft : left ≠ 1) (hright : right ≠ 1) : left = right := by
    obtain ⟨unique, _, hunique⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hcard
    exact (hunique left hleft).trans (hunique right hright).symm
  have hrespect (power : ℕ) (other : S)
      (hconj : IsConj (((element ^ power) : S) : G) (other : G)) :
      character other = character (element ^ power) := by
    have hreduce : element ^ power = element ^ (power % 2) := by
      simpa only [horder] using (pow_mod_orderOf element power).symm
    rw [hreduce] at hconj ⊢
    have hbound : power % 2 < 2 := Nat.mod_lt _ (by decide)
    generalize hremainder : power % 2 = remainder at hconj ⊢ hbound
    interval_cases remainder
    · have hother : other = 1 := Subtype.coe_injective
        (isConj_one_right.mp (by simpa using hconj))
      simp [hother]
    · simp only [pow_one] at hconj ⊢
      exact heq _ _ (hnot other hconj) hnontrivial
  have htransfer := character.transfer_apply_eq_pow_of_conjugate_powers element hrespect
  have hodd : (S : Subgroup G).index % 2 = 1 := by
    have h := S.not_dvd_index
    omega
  have hpower : character element ^ (S : Subgroup G).index = character element := by
    have h := pow_mod_natCard (character element) (S : Subgroup G).index
    simpa only [hcard, hodd, pow_one] using h.symm
  have hpg : IsPGroup 2 A := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hr : IsPGroup 2 character.transfer.range :=
    hpg.of_injective character.transfer.range.subtype character.transfer.range.subtype_injective
  have hquot : IsPGroup 2 (G ⧸ character.transfer.ker) :=
    hr.of_equiv (QuotientGroup.quotientKerEquivRange character.transfer).symm
  have hle : pResidual 2 G ≤ character.transfer.ker := sInf_le ⟨inferInstance, hquot⟩
  intro hmem
  have htrivial : character.transfer (element : G) = 1 := hle hmem
  exact hnontrivial (hpower.symm.trans (htransfer.symm.trans htrivial))

/-- Thompson transfer in its two-residual form for an index-two subgroup of a Sylow subgroup. -/
public theorem not_mem_twoResidual_of_nonfusion_index_two
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (U : Subgroup S) (hU : U.index = 2)
    (element : S) (horder : orderOf element = 2)
    (hnot : ∀ other : S, IsConj (element : G) (other : G) → other ∉ U) :
    (element : G) ∉ pResidual 2 G := by
  let : U.Normal := U.normal_of_index_eq_two hU
  have hcard : Nat.card (S ⧸ U) = 2 := hU
  let : IsCyclic (S ⧸ U) := isCyclic_of_prime_card hcard
  let : CommGroup (S ⧸ U) := IsCyclic.commGroup
  apply S.not_mem_twoResidual_of_nonfusion_character (QuotientGroup.mk' U) hcard element horder
  intro other hconj he
  exact hnot other hconj ((QuotientGroup.eq_one_iff (N := U) (x := other)).mp he)

end Sylow
