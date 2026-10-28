module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.SpecificGroups.SL2.OddSylowCentralizer
public import Theory.SpecificGroups.SL2.NaturalStabilizer
public import Theory.GroupTheory.CoprimeSylowGeneration
/-!
# Odd fixed points in a natural block

If the two-core of a natural L₂(2ⁿ)-block is its commutator module, the
centralizer of any nontrivial odd subgroup inside a Sylow two subgroup
lies in the center of the block. The SL₂ quotient first puts a fixed element
in the two-core. Its image in the natural plane is then zero, since a
nontrivial odd matrix has no nonzero fixed vector in characteristic two.

Source: Aschbacher–Smith, Lemma 2.4.8(5), printed p.530.
-/
public section
open Subgroup Matrix
namespace CFSG.Quasithin.ChapterC
open Subgroup
open scoped MatrixGroups
variable {L : Type*} [Group L] [Finite L]

theorem IsL2EvenBlock.sylow_odd_fixed_le_core_center {n : ℕ} (hL : IsL2EvenBlock L n)
    (hcore : pCore 2 L = blockU L) (P : Sylow 2 L) (D : Subgroup L)
    (hodd : Odd (Nat.card D)) (hD : D ≠ ⊥) :
    (P : Subgroup L) ⊓ centralizer (D : Set L) ≤ center L ⊓ pCore 2 L := by
  obtain ⟨_,_,F,_,_,hF,_,ρ,⟨m⟩,hρ⟩ := hL
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let q : L →* SL(2,F) := m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)
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
    have hc : d ∈ pCore 2 L := hk ▸ he
    exact hd1 (disjoint_def.mp hdis hc hd)
  have hpow : (q d)^(Nat.card D) = 1 := by
    rw [←map_pow]
    have he := congrArg Subtype.val (pow_card_eq_one' (x := (⟨d,hd⟩ : D)))
    exact (congrArg q he).trans q.map_one
  rintro x ⟨hxP,hxD⟩
  have hcomm : Commute (q x) (q d) := by
    have he := (mem_centralizer_iff.mp hxD) d hd
    simpa only [Commute,SemiconjBy,map_mul] using (congrArg q he).symm
  have hqx : q x = 1 := Matrix.SpecialLinearGroup.eq_one_of_sylow_commutes_nontrivial_odd
    (P.mapSurjective hq) (q x) (q d) (mem_map_of_mem q hxP) hqd hodd hpow hcomm
  have hxcore : x ∈ pCore 2 L := hk ▸ hqx
  let u : blockU L := ⟨x,hcore ▸ hxcore⟩
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
  have hu : u ∈ blockFixed L := (QuotientGroup.eq_one_iff u).mp hu1
  exact ⟨hu,hxcore⟩

/-- The centralizer form used by the original shadow construction. -/
theorem IsL2EvenBlock.sylow_odd_fixed_le_center {n : ℕ} (hL : IsL2EvenBlock L n)
    (hcore : pCore 2 L = blockU L) (P : Sylow 2 L) (D : Subgroup L)
    (hodd : Odd (Nat.card D)) (hD : D ≠ ⊥) :
    (P : Subgroup L) ⊓ centralizer (D : Set L) ≤ center L :=
  (hL.sylow_odd_fixed_le_core_center hcore P D hodd hD).trans inf_le_left

/-- A nontrivial odd torus generates the Sylow group through commutators. -/
theorem IsL2EvenBlock.sylow_odd_commutator_eq {n : ℕ} (hL : IsL2EvenBlock L n)
    (hcore : pCore 2 L = blockU L) (P : Sylow 2 L) (D : Subgroup L)
    (hodd : Odd (Nat.card D)) (hD : D ≠ ⊥) (hn : D ≤ normalizer (P : Set L)) :
    ⁅(P : Subgroup L),D⁆ = (P : Subgroup L) := by
  have hc : Nat.Coprime (Nat.card D) (Nat.card P) := by
    obtain ⟨k,hk⟩ := P.isPGroup'.exists_card_eq
    rw [hk]
    exact (Nat.coprime_two_right.mpr hodd).pow_right k
  have hU : pCore 2 L ≤ _root_.commutator L := by
    rw [hcore]
    exact commutator_mono le_top le_rfl
  exact sylow_commutator_eq_of_central_derived_fixed P D hn hc
    ((hL.sylow_odd_fixed_le_core_center hcore P D hodd hD).trans
      (inf_le_inf_left _ hU))

end CFSG.Quasithin.ChapterC
