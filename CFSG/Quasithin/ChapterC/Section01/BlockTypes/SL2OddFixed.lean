module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.OddFixedPoints
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import Theory.SpecificGroups.PSL2.AutomorphismModel
/-!
# Fixed vectors of odd actors in an even natural block

A nonidentity odd matrix in SL₂ over a binary field has no nonzero fixed
natural vector. The original block module map therefore puts the odd
fixed subgroup of U(L) in the center. The cubic-part variant chooses an
actual Sylow subgroup, and the field-four comparison retains the actual
core quotient. These are used in original15.3.18, pp.1126–1127.
-/
public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L] [Finite L]

theorem IsL2EvenBlock.blockU_odd_fixed_le_center {n : ℕ} (hL : IsL2EvenBlock L n)
    (D : Subgroup L) (hodd : Odd (Nat.card D)) (hD : D ≠ ⊥) :
    blockU L ⊓ centralizer (D : Set L) ≤ center L := by
  obtain ⟨_,_,F,_,_,hF,_,ρ,⟨m⟩,hρ⟩ := hL
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q : L →* SL(2,F) := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hk : q.ker = pCore 2 L := by
    ext x
    exact m.quotientIso.map_eq_one_iff.trans (QuotientGroup.eq_one_iff _)
  have hdis : Disjoint (pCore 2 L) D := by
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact (Nat.coprime_two_left.mpr hodd).pow_left k
  obtain ⟨d,hd,hd1⟩ := D.bot_or_exists_ne_one.resolve_left hD
  have hqd : q d ≠ 1 := by
    intro he
    exact hd1 (disjoint_def.mp hdis (hk ▸ he) hd)
  have hpow : (q d)^(Nat.card D) = 1 := by
    rw [←map_pow]
    have he := congrArg Subtype.val (pow_card_eq_one' (x := (⟨d,hd⟩ : D)))
    exact (congrArg q he).trans q.map_one
  rintro x ⟨hxU,hxD⟩
  let u : blockU L := ⟨x,hxU⟩
  let v := m.moduleIso (QuotientGroup.mk' (blockFixed L) u)
  have hv : (q d).val *ᵥ v.toAdd = v.toAdd := by
    have hconj : blockConjugate L d u = u := by
      apply Subtype.ext
      change d*x*d⁻¹=x
      rw [(mem_centralizer_iff.mp hxD) d hd,mul_inv_cancel_right]
    have he := m.intertwining d u
    rw [hconj] at he
    have hh := congrArg Multiplicative.toAdd he
    rw [hρ] at hh
    exact hh.symm
  have hv0 : v.toAdd = 0 := by
    by_contra hvne
    have htwo := Matrix.SL2.pow_two_eq_one_of_nonzero_fixed (q d) v.toAdd hvne hv
    exact hqd (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.coprime_two_left.mpr hodd) (orderOf_dvd_of_pow_eq_one htwo)
      (orderOf_dvd_of_pow_eq_one hpow)))
  have hv1 : v = 1 := Multiplicative.toAdd.injective hv0
  have hu1 : QuotientGroup.mk' (blockFixed L) u = 1 := m.moduleIso.map_eq_one_iff.mp hv1
  exact (QuotientGroup.eq_one_iff u).mp hu1

theorem IsL2EvenBlock.blockU_fixed_le_center_of_three_part {n : ℕ}
    (hL : IsL2EvenBlock L n) (A : Subgroup L)
    (hA : 3^(Nat.card A).factorization 3 = 3) :
    blockU L ⊓ centralizer (A : Set L) ≤ center L := by
  let P : Sylow 3 A := Classical.choice inferInstance
  let D := (P : Subgroup A).map A.subtype
  have hD : Nat.card D = 3 := by
    rw [card_map_of_injective A.subtype_injective,P.card_eq_multiplicity,hA]
  have hDne : D ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hD
    omega
  exact (inf_le_inf_left _ (centralizer_le (map_subtype_le _))).trans
    (hL.blockU_odd_fixed_le_center D (hD ▸ (by decide : Odd 3)) hDne)

omit [Finite L] in
theorem IsL2EvenBlock.four_quotient_alternatingFive (h : IsL2EvenBlock L 2) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨_,_,F,_,_,hF,_,ρ,⟨m⟩,_⟩ := h
  have hF4 : Nat.card F = 4 := by simpa using hF
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  obtain ⟨e⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF4
  exact ⟨m.quotientIso.trans ((Theory.PSL2.sl2QuotientEquiv F).trans e)⟩
end CFSG.Quasithin.ChapterC
