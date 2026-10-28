module

public import Theory.GroupTheory.Commutator.CentralElementaryFourQuotient
public import Theory.GroupTheory.CentralCommutatorQuotient

/-!
# A central extension with a small element centralizer

Let `N` be central of order eight, with `K/N` elementary abelian of order
eight, and suppose every characteristic subgroup of `K` contained in
`N` is either trivial or all of `N`. An element outside `N` whose
centralizer has index at most two forces `K` to be abelian.

The abelian quotient puts the derived subgroup inside `N`. The central
commutator homomorphism `x ↦ [y,x]` has image `C` of order at most two.
In `K/C`, the image of `N ⊔ ⟨y⟩` is central and has index four; the quotient
is elementary abelian. The central elementary-four extension bound gives
`|(K/C)'| ≤ 2`, hence `|K'| ≤ 4`. Characteristic irreducibility now forces
`K' = 1`. The argument includes `C = 1`, and does not require an exponent
hypothesis on `N`.

This independent counting lemma supplies the binary natural `SL₃` step in
Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two* (1993),
(3.6), printed pp.870–871. Its source application, including construction
of the characteristic irreducibility and quotient hypotheses, belongs to
the parent distance-two argument.
-/

open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.SmallExtension

private theorem normal_of_central {K : Type*} [Group K] (C : Subgroup K)
    (hC : C ≤ center K) : C.Normal := by
  constructor
  intro c hc g
  simpa only [mem_center_iff.mp (hC hc) g, mul_inv_cancel_right] using hc

/-- Quotient by the central commutator image of the chosen element, then
apply the central elementary-four extension bound. -/
private theorem card_commutator_le_four
    {K : Type*} [Group K] [Finite K]
    (N : Subgroup K) [N.Normal] (hN : N ≤ center K)
    [IsElementaryAbelian 2 (K ⧸ N)] (hquot : Nat.card (K ⧸ N) = 8)
    (y : K) (hy : y ∉ N) (hindex : (centralizer ({y} : Set K)).index ≤ 2) :
    Nat.card (_root_.commutator K) ≤ 4 := by
  have hD : _root_.commutator K ≤ N :=
    Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  have hr (x : K) (_hx : x ∈ (⊤ : Subgroup K)) : ⁅y, x⁆ ∈ N :=
    hD (commutator_mem_commutator (mem_top y) (mem_top x))
  let f : K →* K := N.subtype.comp
    ((centralCommutatorHom ⊤ N (hN.trans (center_le_centralizer _)) y hr).comp
      topEquiv.symm.toMonoidHom)
  have hf (x : K) : f x = ⁅y, x⁆ := rfl
  let C := f.range
  have hCD : C ≤ _root_.commutator K := by
    rintro x ⟨z, rfl⟩
    exact commutator_mem_commutator (mem_top y) (mem_top z)
  have hCN : C ≤ N := hCD.trans hD
  have hCcenter : C ≤ center K := hCN.trans hN
  let _ : C.Normal := normal_of_central C hCcenter
  have hker : f.ker = centralizer ({y} : Set K) := by
    ext x
    change ⁅y, x⁆ = 1 ↔ x ∈ centralizer ({y} : Set K)
    rw [commutatorElement_eq_one_iff_mul_comm, mem_centralizer_singleton_iff]
    exact eq_comm
  have hCcard : Nat.card C ≤ 2 := by
    rw [show Nat.card C = f.ker.index from (index_ker f).symm, hker]
    exact hindex
  let q := QuotientGroup.mk' C
  let A := N ⊔ zpowers y
  let B := A.map q
  have hBcenter : B ≤ center (K ⧸ C) := by
    change (N ⊔ zpowers y).map q ≤ _
    rw [Subgroup.map_sup, q.map_zpowers]
    apply sup_le
    · rintro _ ⟨n, hn, rfl⟩
      apply mem_center_iff.mpr
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C z
      simpa only [map_mul] using congrArg q (mem_center_iff.mp (hN hn) x)
    · apply zpowers_le.mpr
      apply mem_center_iff.mpr
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C z
      have hh : q ⁅y, x⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨x, hf x⟩
      rw [map_commutatorElement] at hh
      exact (commutatorElement_eq_one_iff_mul_comm.mp hh).symm
  let _ : B.Normal := normal_of_central B hBcenter
  let qN := QuotientGroup.mk' N
  have hpow (x : K) : x ^ 2 ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change qN (x ^ 2) = 1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (K ⧸ N)) (qN x)
  have hmapA : A.map qN = zpowers (qN y) := by
    change (N ⊔ zpowers y).map qN = _
    rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, qN.map_zpowers, bot_sup_eq]
  have hline : Nat.card (zpowers (qN y)) = 2 := by
    rw [Nat.card_zpowers]
    apply orderOf_eq_prime
    · rw [← map_pow]
      exact (QuotientGroup.eq_one_iff (y ^ 2)).mpr (hpow y)
    · exact fun hh => hy ((QuotientGroup.eq_one_iff y).mp hh)
  have hAindex : A.index = 4 := by
    have hh := (zpowers (qN y)).index_mul_card
    rw [hline, hquot] at hh
    have he : (A.map qN).index = A.index :=
      A.index_map_eq (QuotientGroup.mk'_surjective N) (by
        simpa only [qN, QuotientGroup.ker_mk'] using (show N ≤ A from le_sup_left))
    rw [hmapA] at he
    omega
  have hBindex : B.index = 4 := by
    rw [show B.index = A.index from
      A.index_map_eq (QuotientGroup.mk'_surjective C) (by
        simpa only [q, QuotientGroup.ker_mk'] using (hCN.trans (show N ≤ A from le_sup_left))), hAindex]
  have hDmap : (_root_.commutator K).map q = _root_.commutator (K ⧸ C) := by
    rw [map_commutator_eq, q.range_eq_top_of_surjective (QuotientGroup.mk'_surjective C)]
    rfl
  have hDB : _root_.commutator (K ⧸ C) ≤ B := by
    rw [← hDmap]
    exact map_mono (hD.trans le_sup_left)
  let _ : IsElementaryAbelian 2 ((K ⧸ C) ⧸ B) := {
    toIsMulCommutative := Normal.quotient_commutative_iff_commutator_le.mpr hDB
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro z
      obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective B z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C w
      rw [← map_pow, ← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      exact mem_map_of_mem q (show x ^ 2 ∈ A from (show N ≤ A from le_sup_left) (hpow x)) }
  have hsmall : Nat.card (_root_.commutator (K ⧸ C)) ≤ 2 :=
    card_commutator_le_two_of_central_elementary_four_quotient B hBcenter hBindex
  let g := q.subgroupMap (_root_.commutator K)
  have hgker : g.ker = C.subgroupOf (_root_.commutator K) := by
    ext x
    rw [MonoidHom.mem_ker, Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  have hgcard : Nat.card g.ker = Nat.card C := by
    rw [hgker]
    exact Nat.card_congr (subgroupOfEquivOfLe hCD).toEquiv
  have hcard : Nat.card (_root_.commutator K) =
      Nat.card (_root_.commutator (K ⧸ C)) * Nat.card C := by
    rw [card_eq_card_quotient_mul_card_subgroup g.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective g
        (q.subgroupMap_surjective (_root_.commutator K))).toEquiv, hgcard]
    rw [hDmap]
  rw [hcard]
  exact (Nat.mul_le_mul hsmall hCcard).trans (by decide)

/-- A central elementary-eight quotient with a characteristic-irreducible
kernel of order eight is abelian if some element outside the kernel has
centralizer index at most two. No elementary-abelian hypothesis on the
kernel is needed. -/
public theorem isMulCommutative_of_small_centralizer
    {K : Type*} [Group K] [Finite K]
    (N : Subgroup K) [N.Normal] (hN : N ≤ center K) (hcard : Nat.card N = 8)
    [IsElementaryAbelian 2 (K ⧸ N)] (hquot : Nat.card (K ⧸ N) = 8)
    (hirr : ∀ D : Subgroup K, D.Characteristic → D ≤ N → D = ⊥ ∨ D = N)
    (hy : ∃ y : K, y ∉ N ∧ (centralizer ({y} : Set K)).index ≤ 2) :
    IsMulCommutative K := by
  apply (_root_.commutator_eq_bot_iff K).mp
  have hD : _root_.commutator K ≤ N :=
    Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  rcases hirr (_root_.commutator K) inferInstance hD with hz | hfull
  · exact hz
  · obtain ⟨y, hy, hi⟩ := hy
    have hsmall := card_commutator_le_four N hN hquot y hy hi
    rw [hfull, hcard] at hsmall
    omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceTwo.SmallExtension
