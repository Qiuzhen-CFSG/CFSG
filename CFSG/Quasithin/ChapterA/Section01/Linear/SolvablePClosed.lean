module
public import CFSG.Quasithin.ChapterA.Section01.Linear.Dickson
public import GorensteinWalter.PSL2PerfectOfCard
public import GorensteinWalter.SL2ProjectiveCover
public import Theory.PGroupCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Solvable prime-field linear groups are p-closed

Corrected Dickson gives the prime-to-p index of the p-core in a solvable
PSL₂(p) subgroup for p > 3. The exceptional A₅ and whole-field alternatives
are nonsolvable, while the cyclic, dihedral, A₄ and S₄ alternatives have
prime-to-p order. The affine alternative supplies its normal p-subgroup.

P-closedness lifts through a central kernel because the preimage of a
normal p-group is nilpotent. This gives the special-linear assertion.
The determinant kernel then gives the general-linear assertion, since
its quotient has order dividing p−1. All groups and maps are literal.

Source: Aschbacher–Smith, corrected A.1.3, printed p.20, and its use in
15.4.3 on printed p.1157. The correction and Huppert II.8.27 attribution
are recorded in the imported Dickson module.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA

private theorem prime_not_dvd_predecessor {p : ℕ} (hp : p.Prime) : ¬ p ∣ p - 1 :=
  Nat.not_dvd_of_pos_of_lt (by have := hp.two_le; omega) (by have := hp.two_le; omega)

private theorem prime_not_dvd_successor {p : ℕ} (hp : p.Prime) : ¬ p ∣ p + 1 := by
  intro hd
  have hone : p ∣ 1 := (Nat.dvd_add_iff_right (dvd_refl p)).mpr hd
  exact hp.not_dvd_one hone

private theorem pCore_index_of_not_dvd_card {A : Type*} [Group A] [Finite A]
    {p : ℕ} (h : ¬ p ∣ Nat.card A) : ¬ p ∣ (pCore p A).index :=
  fun hd => h (hd.trans (pCore p A).index_dvd_card)

/-- The projective part of the solvable prime-field p-closed corollary. -/
theorem solvable_PSL₂_primeCore_index {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (H : Subgroup PSL(2, ZMod p)) (hs : Group.IsSolvable H) :
    ¬ p ∣ (pCore p H).index := by
  let : Group.IsSolvable H := hs
  have hprime : p.Prime := Fact.out
  have hdivbound : ∀ z : ℕ,
      (z ∣ (p ^ 1 - 1) / Nat.gcd (p ^ 1 - 1) 2 ∨
       z ∣ (p ^ 1 + 1) / Nat.gcd (p ^ 1 - 1) 2) → ¬ p ∣ z := by
    intro z hz hd
    rcases hz with hz | hz
    · exact prime_not_dvd_predecessor hprime
        (by simpa using hd.trans (hz.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))))
    · have hg : Nat.gcd (p ^ 1 - 1) 2 ∣ p ^ 1 + 1 := by
        have hsum := Nat.dvd_add (Nat.gcd_dvd_left (p ^ 1 - 1) 2)
          (Nat.gcd_dvd_right (p ^ 1 - 1) 2)
        simpa [show p - 1 + 2 = p + 1 by omega] using hsum
      exact prime_not_dvd_successor hprime (by simpa using hd.trans (hz.trans (Nat.div_dvd_of_dvd hg)))
  rcases lemma_A_1_3_corrected (F := ZMod p) (p := p) (f := 1)
      (by simp) H with he | hc | hd | ha4 | hs4 | ha5 | haff | hpsl | hpgl
  · let : IsElementaryAbelian p H := he.1
    have ht : pCore p H = ⊤ := top_unique
      (le_sSup ⟨inferInstance, (IsElementaryAbelian.isPGroup p H).to_subgroup ⊤⟩)
    rw [ht, index_top]
    exact hprime.not_dvd_one
  · obtain ⟨z, hz, hc, _⟩ := hc
    apply pCore_index_of_not_dvd_card
    rw [hc]
    exact hdivbound z hz
  · obtain ⟨z, hz, hc, _⟩ := hd
    apply pCore_index_of_not_dvd_card
    rw [hc, hprime.dvd_mul]
    exact not_or.mpr ⟨Nat.not_dvd_of_pos_of_lt (by decide) (by omega), hdivbound z hz⟩
  · obtain ⟨_, ⟨e⟩⟩ := ha4
    apply pCore_index_of_not_dvd_card
    have hc : Nat.card H = 12 := by rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]; norm_num [Nat.factorial]
    rw [hc]
    intro hd
    have hh := hprime.dvd_mul.mp (show p ∣ 3 * 2 ^ 2 from hd)
    rcases hh with h3 | h2
    · have := Nat.le_of_dvd (by decide : 0 < 3) h3; omega
    · have := Nat.le_of_dvd (by decide : 0 < 2) (hprime.dvd_of_dvd_pow h2); omega
  · obtain ⟨_, ⟨e⟩⟩ := hs4
    apply pCore_index_of_not_dvd_card
    have hc : Nat.card H = 24 := by rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]; decide
    rw [hc]
    intro hd
    have hh := hprime.dvd_mul.mp (show p ∣ 3 * 2 ^ 3 from hd)
    rcases hh with h3 | h2
    · have := Nat.le_of_dvd (by decide : 0 < 3) h3; omega
    · have := Nat.le_of_dvd (by decide : 0 < 2) (hprime.dvd_of_dvd_pow h2); omega
  · obtain ⟨_, ⟨e⟩⟩ := ha5
    have hs5 : Group.IsSolvable (alternatingGroup (Fin 5)) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) hs5).elim
  · obtain ⟨m, t, hm, ht, htf, N, C, hNn, hNe, _, _, hCc, hd, hsup, _⟩ := haff
    let : N.Normal := hNn
    let : IsElementaryAbelian p N := hNe
    have hNC : N ≤ pCore p H := le_sSup ⟨hNn, IsElementaryAbelian.isPGroup p N⟩
    have hcompl : N.IsComplement' C := isComplement'_of_disjoint_and_mul_eq_univ hd
      (by rw [← normal_mul N C, hsup, coe_top])
    have hi : N.index = t := hcompl.symm.index_eq_card.trans hCc
    intro hiP
    have hpt : p ∣ t := hi ▸ hiP.trans (index_dvd_of_le hNC)
    exact hdivbound t (Or.inl htf) hpt
  · obtain ⟨m, _, hm, ⟨e⟩⟩ := hpsl
    have hm1 : m = 1 := Nat.dvd_one.mp hm
    subst m
    let : Group.IsPerfect PSL(2, GaloisField p 1) :=
      GorensteinWalter.psl2_isPerfect_of_card_gt_three _ (by
        simpa [GaloisField.card p 1 (by decide)] using hp)
    have hsP : Group.IsSolvable PSL(2, GaloisField p 1) :=
      Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
    exact (Group.IsPerfect.not_isSolvable PSL(2, GaloisField p 1) hsP).elim
  · obtain ⟨m, _, hm, _⟩ := hpgl
    have he := Nat.dvd_one.mp hm
    omega

private theorem pGroup_le_core_of_primeCore_index {A : Type*} [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] (h : ¬ p ∣ (pCore p A).index)
    (U : Subgroup A) (hU : IsPGroup p U) : U ≤ pCore p A := by
  let q := QuotientGroup.mk' (pCore p A)
  have hcard : Nat.card (U.map q) = 1 := (hU.map q).card_eq_or_dvd.resolve_right
    (fun hd => h (hd.trans (U.map q).card_subgroup_dvd_card))
  have hz := Subgroup.card_eq_one.mp hcard
  simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using hz

private theorem pGroup_le_core_of_central_kernel {A B : Type*} [Group A] [Finite A]
    [Group B] [Finite B] {p : ℕ} [Fact p.Prime]
    (f : A →* B) (hk : f.ker ≤ center A)
    (hB : ∀ U : Subgroup B, IsPGroup p U → U ≤ pCore p B)
    (U : Subgroup A) (hU : IsPGroup p U) : U ≤ pCore p A := by
  let N := (pCore p B).comap f
  let g := f.subgroupMap N
  have hNmap : N.map f ≤ pCore p B := map_comap_le _ _
  let : Group.IsNilpotent (N.map f) := (pCore_isPGroup.to_le hNmap).isNilpotent
  have hgc : g.ker ≤ center N := by
    intro x hx
    have hxk : (x : A) ∈ f.ker := congrArg Subtype.val hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp (hk hxk) (y : A))
  have hnil : Group.IsNilpotent N := Subgroup.isNilpotent_of_ker_le_center g hgc
  have hUN : U ≤ N := map_le_iff_le_comap.mp (hB _ (hU.map f))
  obtain ⟨S, hS⟩ := (show IsPGroup p (U.subgroupOf N) from hU.comap_subtype).exists_le_sylow
  have hh := map_mono (f := N.subtype) hS
  rw [map_subgroupOf_eq_of_le hUN] at hh
  exact hh.trans (Sylow.map_le_pCore inferInstance hnil p S)

private theorem pGroup_le_core_of_injective {A B : Type*} [Group A] [Finite A]
    [Group B] [Finite B] {p : ℕ} [Fact p.Prime]
    (f : A →* B) (hf : Function.Injective f)
    (hB : ∀ U : Subgroup B, IsPGroup p U → U ≤ pCore p B)
    (U : Subgroup A) (hU : IsPGroup p U) : U ≤ pCore p A :=
  (map_le_iff_le_comap.mp (hB _ (hU.map f))).trans
    (le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective f hf⟩)

/-- In a solvable subgroup of SL₂(p), every p-subgroup lies in its p-core. -/
theorem solvable_SL₂_pGroup_le_core {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (H : Subgroup SL(2, ZMod p)) (hs : Group.IsSolvable H)
    (U : Subgroup H) (hU : IsPGroup p U) : U ≤ pCore p H := by
  let : Group.IsSolvable H := hs
  let q := GorensteinWalter.sl2ProjectiveProjection (ZMod p)
  let f := q.subgroupMap H
  have hk : f.ker ≤ center H := by
    intro x hx
    have hxk : (x : SL(2, ZMod p)) ∈ q.ker := congrArg Subtype.val hx
    rw [GorensteinWalter.sl2ProjectiveProjection_ker] at hxk
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp hxk (y : SL(2, ZMod p)))
  have hsQ : Group.IsSolvable (H.map q) :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective H)
  exact pGroup_le_core_of_central_kernel f hk
    (pGroup_le_core_of_primeCore_index (solvable_PSL₂_primeCore_index hp (H.map q) hsQ)) U hU

/-- The solvable GL₂(p) p-closed corollary, with p > 3. -/
theorem solvable_GL₂_pGroup_le_core {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (H : Subgroup (GL (Fin 2) (ZMod p))) (hs : Group.IsSolvable H)
    (U : Subgroup H) (hU : IsPGroup p U) : U ≤ pCore p H := by
  let : Group.IsSolvable H := hs
  let d := (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := ZMod p)).comp H.subtype
  let D := d.ker
  let j : D →* SL(2, ZMod p) := {
    toFun := fun x => ⟨((x.val.val : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)),
      congrArg Units.val x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val hxy
  have hsJ : Group.IsSolvable j.range := Group.isSolvable_of_surjective j.rangeRestrict_surjective
  have hclosed : ∀ V : Subgroup D, IsPGroup p V → V ≤ pCore p D :=
    pGroup_le_core_of_injective j.rangeRestrict (by
      intro x y hxy; exact hj (congrArg Subtype.val hxy))
      (solvable_SL₂_pGroup_le_core hp j.range hsJ)
  have hUD : U ≤ D := by
    have hcard : Nat.card (U.map d) = 1 := (hU.map d).card_eq_or_dvd.resolve_right (by
      intro hd
      have hn : ¬ p ∣ Nat.card (ZMod p)ˣ := by
        simpa [Nat.card_eq_fintype_card, ZMod.card_units, Nat.totient_prime (Fact.out : p.Prime)] using prime_not_dvd_predecessor (Fact.out : p.Prime)
      exact hn (hd.trans (U.map d).card_subgroup_dvd_card))
    exact (Subgroup.map_eq_bot_iff U).mp (Subgroup.card_eq_one.mp hcard)
  have hm := map_mono (f := D.subtype) (hclosed (U.subgroupOf D) hU.comap_subtype)
  rw [map_subgroupOf_eq_of_le hUD] at hm
  exact hm.trans (le_sSup ⟨inferInstance, pCore_isPGroup.map D.subtype⟩)

end CFSG.Quasithin.ChapterA
