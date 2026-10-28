module

public import Theory.GroupTheory.InvolutionCentralizerFourCyclicComplement
public import Theory.GroupTheory.NormalizingInvolutionCentralizer
public import Theory.GroupTheory.PGroup.InvolutionFour
public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral
public import Mathlib.GroupTheory.IndexNormal

/-!
# Dihedral recognition from a normalizing involution with two fixed points

A finite two-subgroup containing an elementary four is dihedral when an
ambient normalizing involution has centralizer in it of order at most two.
The ambient group need not be a two-group.

Adjoin the involution and apply the cyclic-complement theorem for involution
centralizers of order four. An involution in the original elementary four
outside that cyclic complement inverts a generator: its product with the
external involution is an odd power of a cyclic generator. The original
subgroup is therefore a cyclic group extended by an inverting involution,
and the conclusion gives its actual dihedral equivalence.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, the deduction from |C_B(y)| = 2. The cyclic-complement theorem
supplies the standard finite-two-group recognition used in that deduction.
-/

open Subgroup

private theorem dihedral_index_two
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (B : Subgroup P) (hBi : B.index = 2)
    (E : Subgroup B) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (y : P) (hy : orderOf y = 2) (hyB : y ∉ B)
    (hyZ : y ∉ center P) (hCy : Nat.card (centralizer ({y} : Set P)) = 4) :
    ∃ n : ℕ, 1 ≤ n ∧ Nonempty (B ≃* DihedralGroup (2 ^ n)) := by
  classical
  obtain ⟨a, hai, hya⟩ :=
    exists_zpowers_index_two_of_involution_centralizer_card_four hP y hy hyZ hCy
  let A := zpowers a
  let F := E.map B.subtype
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map B.subtype
  have hF : Nat.card F = 4 := (card_map_of_injective B.subtype_injective).trans hE
  have hFA : ¬ F ≤ A := by
    intro h
    let : IsCyclic F := isCyclic_of_le h
    have hd : Nat.card F ∣ 2 := by
      rw [← IsCyclic.exponent_eq_card]
      exact IsElementaryAbelian.exponent_dvd_p 2 F
    norm_num [hF] at hd
  obtain ⟨e, heF, heA⟩ := SetLike.not_le_iff_exists.mp hFA
  have heB : e ∈ B := map_subtype_le E heF
  have he2 : e ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian e heF
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  let d := e * y
  have hdA : d ∈ A := (mul_mem_iff_of_index_two hai).mpr (iff_of_false heA hya)
  have hdB : d ∉ B := by
    intro h
    exact hyB ((B.mul_mem_cancel_left heB).mp h)
  obtain ⟨k, _, hkd⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hdA)
  have hkodd : Odd k := by
    apply Nat.not_even_iff_odd.mp
    rintro ⟨j, hj⟩
    apply hdB
    rw [← hkd, hj, ← two_mul, pow_mul]
    exact B.pow_mem (sq_mem_of_index_two hBi a) j
  have had : a ∈ zpowers d := by
    rw [← hkd, mem_zpowers_pow_iff]
    obtain ⟨m, hm⟩ := hP.exists_orderOf_eq_pow a
    rw [hm]
    exact (Nat.coprime_two_right.mpr hkodd).pow_right m
  have hAd : A = zpowers d := le_antisymm (zpowers_le.mpr had) (zpowers_le.mpr hdA)
  have heinv : e * d * e⁻¹ = d⁻¹ := by
    have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using he2)
    have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hy2)
    dsimp [d]
    simp only [mul_inv_rev, hei, hyi]
    have hee : e * e = 1 := by simpa [pow_two] using he2
    simp [← mul_assoc, hee]
  let R := B ⊓ A
  have hRcyc : IsCyclic R := isCyclic_of_le (show R ≤ A from inf_le_right)
  have heR : e ∉ R := fun h => heA h.2
  have hinv (r : P) (hr : r ∈ R) : e * r * e⁻¹ = r⁻¹ := by
    have hrA := hr.2
    rw [hAd] at hrA
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hrA
    change MulAut.conj e (d ^ j) = (d ^ j)⁻¹
    rw [map_zpow, MulAut.conj_apply, heinv, inv_zpow]
  have hgen : R ⊔ zpowers e = B := by
    apply le_antisymm (sup_le inf_le_left (zpowers_le.mpr heB))
    intro x hx
    by_cases hxA : x ∈ A
    · exact mem_sup_left (show x ∈ R from ⟨hx, hxA⟩)
    · have hxe : x * e ∈ R := ⟨B.mul_mem hx heB,
        (mul_mem_iff_of_index_two hai).mpr (iff_of_false hxA heA)⟩
      have hh := (R ⊔ zpowers e).mul_mem (mem_sup_left hxe)
        (mem_sup_right ((zpowers e).inv_mem (mem_zpowers e)))
      simpa using hh
  obtain ⟨f⟩ := nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted R e hRcyc he2 heR hinv
  obtain ⟨n, hn⟩ := (hP.to_subgroup R).exists_card_eq
  let : B.Normal := B.normal_of_index_eq_two hBi
  let : A.Normal := A.normal_of_index_eq_two hai
  let : R.Normal := inferInstance
  have hBcard : Nat.card B = 2 * 2 ^ n := by
    rw [← hgen, card_sup_zpowers_of_normalizing_involution R e he2 heR
      (by rw [normalizer_eq_top]; trivial), hn]
  have hn1 : 1 ≤ n := by
    have hc := E.card_le_card_group
    rw [hE, hBcard] at hc
    by_contra h
    have : n = 0 := by omega
    simp [this] at hc
  refine ⟨n, hn1, ?_⟩
  rw [← hn]
  exact ⟨(MulEquiv.subgroupCongr hgen.symm).trans f⟩

open scoped IsMulCommutative

private theorem centralizer_lower_of_four
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (y : P) (hy : orderOf y = 2) :
    4 ≤ Nat.card (centralizer ({y} : Set P)) := by
  obtain ⟨V, hVe, hV, hyV⟩ := hP.exists_elementary_four_mem_of_four_le E hE.ge y hy
  let : IsElementaryAbelian 2 V := hVe
  have hVC : V ≤ centralizer ({y} : Set P) := by
    intro v hv
    exact mem_centralizer_singleton_iff.mpr ((V.le_centralizer hv) y hyV).symm
  simpa [hV] using card_le_of_le hVC

public theorem Subgroup.exists_dihedral_equiv_of_normalizing_involution_small_fixed
    {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) (hB : IsPGroup 2 B)
    (E : Subgroup B) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (y : G) (hy : orderOf y = 2) (hyn : y ∈ normalizer (B : Set G))
    (hfix : Nat.card (B ⊓ centralizer ({y} : Set G) : Subgroup G) ≤ 2) :
    ∃ n : ℕ, 1 ≤ n ∧ Nonempty (B ≃* DihedralGroup (2 ^ n)) := by
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  have hyB : y ∉ B := by
    intro hyB
    have hc := centralizer_lower_of_four hB E hE (⟨y, hyB⟩ : B) (by simpa using hy)
    have heq : (centralizer ({(⟨y, hyB⟩ : B)} : Set B)).map B.subtype =
        B ⊓ centralizer ({y} : Set G) := by
      ext x
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact ⟨v.property, mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hv))⟩
      · intro hx
        exact ⟨⟨x, hx.1⟩, mem_centralizer_singleton_iff.mpr
          (Subtype.ext (mem_centralizer_singleton_iff.mp hx.2)), rfl⟩
    have hcard := card_map_of_injective (f := B.subtype) (K := centralizer ({(⟨y, hyB⟩ : B)} : Set B))
      B.subtype_injective
    rw [heq] at hcard
    omega
  let P := B ⊔ zpowers y
  let D := B.subgroupOf P
  let f : D ≃* B := subgroupOfEquivOfLe (show B ≤ P from le_sup_left)
  let F := E.map f.symm.toMonoidHom
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map f.symm.toMonoidHom
  have hF : Nat.card F = 4 := (card_map_of_injective f.symm.injective).trans hE
  have hDcard : Nat.card D = Nat.card B := Nat.card_congr f.toEquiv
  have hPcard : Nat.card P = 2 * Nat.card B :=
    card_sup_zpowers_of_normalizing_involution B y hy2 hyB hyn
  have hP : IsPGroup 2 P := by
    obtain ⟨n, hn⟩ := hB.exists_card_eq
    exact IsPGroup.of_card (n := n + 1) (by rw [hPcard, hn, pow_succ, mul_comm])
  have hDi : D.index = 2 := by
    have hm := D.card_mul_index
    rw [hDcard, hPcard] at hm
    have hp : 0 < Nat.card B := Nat.card_pos
    nlinarith
  let yP : P := ⟨y, mem_sup_right (mem_zpowers y)⟩
  have hyP : orderOf yP = 2 := by simpa [yP] using hy
  have hyD : yP ∉ D := hyB
  have hyZ : yP ∉ center P := by
    intro hc
    have hle : B ≤ centralizer ({y} : Set G) := by
      intro b hb
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_center_iff.mp hc (⟨b, mem_sup_left hb⟩ : P)))
    have heq : B ⊓ centralizer ({y} : Set G) = B := inf_eq_left.mpr hle
    rw [heq] at hfix
    have hbound := E.card_le_card_group
    omega
  have hCy : Nat.card (centralizer ({yP} : Set P)) = 4 := by
    have hupper := card_centralizer_sup_zpowers_of_normalizing_involution B y hy2 hyB hyn
    change Nat.card (centralizer ({yP} : Set P)) = _ at hupper
    let F' := F.map D.subtype
    let : IsElementaryAbelian 2 F' := IsElementaryAbelian.map D.subtype
    have hF' : Nat.card F' = 4 := (card_map_of_injective D.subtype_injective).trans hF
    have hlower := centralizer_lower_of_four hP F' hF' yP hyP
    omega
  obtain ⟨n, hn, ⟨e⟩⟩ := dihedral_index_two hP D hDi F hF yP hyP hyD hyZ hCy
  exact ⟨n, hn, ⟨f.symm.trans e⟩⟩
