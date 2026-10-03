module

public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.ElementaryAbelian.Join
public import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# A normal four-group from a cyclic self-centralizing subgroup

Let `P` be a finite two-group with a normal cyclic subgroup `A` containing
its centralizer. If `P` contains an elementary abelian subgroup of order at
least eight, then `P` has a normal elementary abelian subgroup of order four.

Write `A = ⟨a⟩`, of order `2^n`. The kernel of any action of the elementary
subgroup that lies in `A` has order at most two. Applying this first to `A`
and then to its subgroup of order four gives `n ≥ 3` and an involution `e`
outside `A` centralizing that subgroup. Its action exponent `r` satisfies
`r ≡ 1 (mod 4)` and `r² ≡ 1 (mod 2^n)`, so the nontrivial action is
`r = 1 + 2^(n-1)`.

The unique involution `z` of `A` is central. Since `Aut(A)` is abelian and
`C_P(A) ≤ A`, each conjugate of `e` has the form `d * e` with `d ∈ A`.
Squaring shows `d^(2 + 2^(n-1)) = 1`; the odd factor can be cancelled in a
two-group, giving `d² = 1`. Thus `d` is either `1` or `z`, proving that
`⟨z,e⟩` is normal. The two commuting involutions generate a group of order
four.

This is the cyclic self-centralizer case of the elementary argument for
Gorenstein–Lyons–Solomon, *The Classification of the Finite Simple Groups*,
Number 2, Chapter C, Lemma 10.11. No classification of cyclic automorphisms
or of two-groups is used.
-/

open Subgroup

private theorem conj_diff_mem {P : Type*} [Group P]
    (A : Subgroup P) [A.Normal] [IsCyclic A]
    (hC : centralizer (A : Set P) ≤ A) (g e : P) :
    (g * e * g⁻¹) * e⁻¹ ∈ A := by
  let f : P →* MulAut A := MulAut.conjNormal
  let : CommGroup (MulAut A) :=
    (IsCyclic.mulAutMulEquiv A).toMonoidHom.commGroupOfInjective
      (IsCyclic.mulAutMulEquiv A).injective
  have hker : f ((g * e * g⁻¹) * e⁻¹) = 1 := by
    simp [map_mul, map_inv]
  apply hC
  intro a ha
  have hh := congrArg (fun t : MulAut A => (t ⟨a, ha⟩ : P)) hker
  change (g * e * g⁻¹ * e⁻¹) * a * (g * e * g⁻¹ * e⁻¹)⁻¹ = a at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The modular involution action on a cyclic normal self-centralizing subgroup
forces a normal elementary four-group. -/
public theorem IsPGroup.exists_normal_four_of_twist {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (A : Subgroup P) [A.Normal] [IsCyclic A]
    (hC : centralizer (A : Set P) ≤ A)
    (a e : P) (n : ℕ) (hn : 3 ≤ n) (hA : A = zpowers a)
    (ha : orderOf a = 2 ^ n) (he : e ^ 2 = 1) (heA : e ∉ A)
    (hact : e * a * e⁻¹ = a ^ (1 + 2 ^ (n - 1))) :
    ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4 := by
  classical
  have hsplit : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  let z := a ^ (2 ^ (n - 1))
  have hzA : z ∈ A := by rw [hA]; exact pow_mem (mem_zpowers a) _
  have hzorder : orderOf z = 2 := by
    have hh := orderOf_pow_orderOf_div (Nat.ne_of_gt (orderOf_pos a))
      (show 2 ∣ orderOf a by rw [ha, hsplit]; exact dvd_mul_left _ _)
    simpa [ha, hsplit, z] using hh
  have hz2 : z ^ 2 = 1 := hzorder ▸ pow_orderOf_eq_one z
  have hzfixed (g : P) : g * z * g⁻¹ = z := by
    have hmem : g * z * g⁻¹ ∈ A := Subgroup.Normal.conj_mem inferInstance z hzA g
    have hh : orderOf (g * z * g⁻¹) = 2 := by
      rw [← MulAut.conj_apply, (MulAut.conj g).orderOf_eq, hzorder]
    exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
      (x := (⟨g * z * g⁻¹, hmem⟩ : A)) (y := ⟨z, hzA⟩)
      (by simpa using hh) (by simpa using hzorder))
  have haction (d : P) (hd : d ∈ A) :
      e * d * e⁻¹ = d ^ (1 + 2 ^ (n - 1)) := by
    rw [hA] at hd
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hd)
    change MulAut.conj e (a ^ k) = _
    rw [map_pow, MulAut.conj_apply, hact, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have hconj (g : P) : g * e * g⁻¹ = e ∨ g * e * g⁻¹ = z * e := by
    let d := (g * e * g⁻¹) * e⁻¹
    have hdA : d ∈ A := conj_diff_mem A hC g e
    have hde : d * e = g * e * g⁻¹ := by simp [d]
    have hde2 : (d * e) ^ 2 = 1 := by
      rw [hde, ← MulAut.conj_apply, ← map_pow, he, map_one]
    have hdPow : d ^ (2 + 2 ^ (n - 1)) = 1 := by
      calc
        d ^ (2 + 2 ^ (n - 1)) = d * d ^ (1 + 2 ^ (n - 1)) := by
          rw [← pow_succ']; congr 1; omega
        _ = d * (e * d * e⁻¹) := by rw [haction d hdA]
        _ = (d * e) ^ 2 * (e ^ 2)⁻¹ := by simp only [pow_two]; group
        _ = 1 := by rw [hde2, he]; simp
    have hhalf : 2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
      conv_lhs => rw [show n - 1 = (n - 2) + 1 by omega]
      rw [pow_succ]
    have hodd : Nat.Coprime 2 (1 + 2 ^ (n - 2)) := by
      apply Nat.coprime_two_left.mpr
      have hp : Even (2 ^ (n - 2)) := Nat.even_pow.mpr ⟨by decide, by omega⟩
      exact Odd.add_even (by decide : Odd (1 : ℕ)) hp
    have hd2 : d ^ 2 = 1 := by
      apply (hP.powEquiv hodd).injective
      simp only [IsPGroup.powEquiv_apply, one_pow, ← pow_mul]
      convert hdPow using 1
      rw [hhalf]
      congr 1
      ring
    have hd : d = 1 ∨ d = z := by
      by_cases hdone : d = 1
      · exact Or.inl hdone
      right
      have hdorder : orderOf d = 2 := orderOf_eq_prime hd2 hdone
      exact congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two
        (x := (⟨d, hdA⟩ : A)) (y := ⟨z, hzA⟩)
        (by simpa using hdorder) (by simpa using hzorder))
    rcases hd with hd | hd
    · exact Or.inl (by simpa [hd] using hde.symm)
    · exact Or.inr (by simpa [hd] using hde.symm)
  let U := zpowers z ⊔ zpowers e
  have hzU : z ∈ U := (le_sup_left : zpowers z ≤ U) (mem_zpowers z)
  have heU : e ∈ U := (le_sup_right : zpowers e ≤ U) (mem_zpowers e)
  have hnormal : U.Normal := by
    constructor
    intro x hx g
    have hh : U.map (MulAut.conj g).toMonoidHom ≤ U := by
      dsimp [U]
      rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
      apply sup_le
      · apply zpowers_le.mpr
        change g * z * g⁻¹ ∈ U
        rw [hzfixed]
        exact hzU
      · apply zpowers_le.mpr
        change g * e * g⁻¹ ∈ U
        rcases hconj g with h | h
        · rw [h]; exact heU
        · rw [h]; exact U.mul_mem hzU heU
    exact hh (mem_map_of_mem _ hx)
  have heC : e ∈ centralizer (zpowers z : Set P) := by
    intro x hx
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
    have hcomm : Commute z e := (mul_inv_eq_iff_eq_mul.mp (hzfixed e)).symm
    exact (hcomm.zpow_left k).eq
  let : IsElementaryAbelian 2 (zpowers z) := IsElementaryAbelian.zpowers_of_pow_eq_one hz2
  let : IsElementaryAbelian 2 (zpowers e) := IsElementaryAbelian.zpowers_of_pow_eq_one he
  have helem : IsElementaryAbelian 2 U :=
    IsElementaryAbelian.sup_of_le_centralizer (zpowers_le.mpr heC)
  refine ⟨U, hnormal, helem, ?_⟩
  have heout : e ∉ zpowers z := fun hh => heA (zpowers_le.mpr hzA hh)
  rw [card_sup_zpowers_of_normalizing_involution (zpowers z) e he heout
    (centralizer_le_normalizer _ heC), Nat.card_zpowers, hzorder]

private theorem card_bound {P Q : Type*} [Group P] [Finite P] [Group Q] [Finite Q]
    (A E : Subgroup P) [IsCyclic A] [IsElementaryAbelian 2 E]
    (f : E →* Q) (hker : ∀ x : f.ker, ((x : E) : P) ∈ A) :
    Nat.card E ≤ 2 * Nat.card Q := by
  let j : f.ker →* A := {
    toFun := fun x => ⟨x, hker x⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    have hh : ((x : E) : P) = ((y : E) : P) := congrArg (fun v : A => (v : P)) h
    exact Subtype.ext (Subtype.ext hh)
  let : IsCyclic f.ker := isCyclic_of_injective j hj
  have hsmall : Nat.card f.ker ≤ 2 := by
    apply Nat.le_of_dvd (by decide)
    rw [← IsCyclic.exponent_eq_card]
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 E) (x : E)
  have hmul := f.ker.card_mul_index
  rw [index_ker] at hmul
  have hrange : Nat.card f.range ≤ Nat.card Q := card_le_card_group _
  nlinarith

private theorem kernel_centralizes {P : Type*} [Group P]
    (B E : Subgroup P) [B.Normal]
    (x : ((MulAut.conjNormal : P →* MulAut B).comp E.subtype).ker) :
    ((x : E) : P) ∈ centralizer (B : Set P) := by
  intro b hb
  have hh := congrArg (fun t : MulAut B => (t ⟨b, hb⟩ : P))
    (MonoidHom.mem_ker.mp x.property)
  change (x : P) * b * (x : P)⁻¹ = b at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

private theorem zpowers_pow_normal {P : Type*} [Group P]
    (a : P) [(zpowers a).Normal] (k : ℕ) : (zpowers (a ^ k)).Normal := by
  constructor
  intro x hx g
  have hga : g * a * g⁻¹ ∈ zpowers a := Normal.conj_mem inferInstance a (mem_zpowers a) g
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hga
  have hmap : (zpowers (a ^ k)).map (MulAut.conj g).toMonoidHom ≤ zpowers (a ^ k) := by
    rw [MonoidHom.map_zpowers]
    apply zpowers_le.mpr
    change MulAut.conj g (a ^ k) ∈ zpowers (a ^ k)
    rw [map_pow, MulAut.conj_apply, ← hj]
    have heq : (a ^ j) ^ k = (a ^ k) ^ j := by
      simp only [← zpow_natCast, ← zpow_mul, mul_comm]
    rw [heq]
    exact zpow_mem (mem_zpowers _) _
  exact hmap (mem_map_of_mem _ hx)

private theorem exists_twist {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (A : Subgroup P) [A.Normal] [IsCyclic A]
    (hC : centralizer (A : Set P) ≤ A)
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : 8 ≤ Nat.card E) :
    ∃ (a e : P) (n : ℕ), 3 ≤ n ∧ A = zpowers a ∧ orderOf a = 2 ^ n ∧
      e ^ 2 = 1 ∧ e ∉ A ∧ e * a * e⁻¹ = a ^ (1 + 2 ^ (n - 1)) := by
  classical
  obtain ⟨a, haA⟩ := A.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  obtain ⟨n, hn⟩ := (hP.to_subgroup A).exists_card_eq
  have ha : orderOf a = 2 ^ n := by rw [← Nat.card_zpowers, haA, hn]
  have hn3 : 3 ≤ n := by
    have hbound := card_bound A E ((MulAut.conjNormal : P →* MulAut A).comp E.subtype)
      (fun x => hC (kernel_centralizes A E x))
    rw [IsCyclic.card_mulAut, hn] at hbound
    by_contra hsmall
    have hnlt : n < 3 := by omega
    interval_cases n <;> norm_num [show Nat.totient 4 = 2 by decide] at hbound <;> omega
  let b := a ^ (2 ^ (n - 2))
  let B := zpowers b
  let : (zpowers a).Normal := haA.symm ▸ inferInstance
  let : B.Normal := zpowers_pow_normal a _
  have hsplit : 2 ^ n = 2 ^ (n - 2) * 4 := by
    conv_lhs => rw [show n = (n - 2) + 2 by omega]
    rw [pow_add]; norm_num
  have hBcard : Nat.card B = 4 := by
    rw [Nat.card_zpowers]
    have hh := orderOf_pow_orderOf_div (Nat.ne_of_gt (orderOf_pos a))
      (show 4 ∣ orderOf a by rw [ha, hsplit]; exact dvd_mul_left _ _)
    simpa [ha, hsplit, b] using hh
  let f : E →* MulAut B := (MulAut.conjNormal : P →* MulAut B).comp E.subtype
  have hex : ∃ x : f.ker, ((x : E) : P) ∉ A := by
    by_contra h
    have hbound := card_bound A E f (by simpa using h)
    rw [IsCyclic.card_mulAut, hBcard] at hbound
    norm_num [show Nat.totient 4 = 2 by decide] at hbound
    omega
  obtain ⟨x, hxA⟩ := hex
  let e : P := x
  have he : e ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian e (x : E).property
  have heb : e * b * e⁻¹ = b := by
    have hh := kernel_centralizes B E x (b) (mem_zpowers b)
    exact mul_inv_eq_iff_eq_mul.mpr hh.symm
  have hconjA : e * a * e⁻¹ ∈ zpowers a := by
    exact Normal.conj_mem inferInstance a (mem_zpowers a) e
  obtain ⟨r, hr, har⟩ := Finset.mem_image.mp
    (mem_zpowers_iff_mem_range_orderOf.mp hconjA)
  have hrlt : r < 2 ^ n := by simpa [ha] using Finset.mem_range.mp hr
  have hr4 : r % 4 = 1 := by
    have hp : b ^ r = b ^ 1 := by
      calc
        b ^ r = (a ^ r) ^ (2 ^ (n - 2)) := by dsimp [b]; rw [← pow_mul, ← pow_mul, Nat.mul_comm]
        _ = MulAut.conj e (a ^ (2 ^ (n - 2))) := by rw [map_pow, MulAut.conj_apply, har]
        _ = b := heb
        _ = b ^ 1 := (pow_one b).symm
    have hb : orderOf b = 4 := by simpa [B] using hBcard
    have hh := pow_eq_pow_iff_modEq.mp hp
    simpa [hb, Nat.ModEq] using hh
  have hr1 : r ≠ 1 := by
    intro hh
    have heC : e ∈ centralizer (A : Set P) := by
      intro y hy
      rw [← haA] at hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      have hhcomm : Commute a e := by
        have hc : e * a * e⁻¹ = a := by simpa [hh] using har.symm
        exact (mul_inv_eq_iff_eq_mul.mp hc).symm
      exact (hhcomm.zpow_left k).eq
    exact hxA (hC heC)
  have hrlower : 1 ≤ r := by omega
  have hrr : 2 ^ n ∣ r * r - 1 := by
    have hp : a ^ (r * r) = a := by
      calc
        a ^ (r * r) = MulAut.conj e (a ^ r) := by rw [map_pow, MulAut.conj_apply, ← har, pow_mul]
        _ = MulAut.conj e (MulAut.conj e a) := by congr 1
        _ = a := by
          have hee : e * e = 1 := by simpa [pow_two] using he
          simp only [MulAut.conj_apply]
          calc
            e * (e * a * e⁻¹) * e⁻¹ = (e * e) * a * (e * e)⁻¹ := by group
            _ = a := by rw [hee]; simp
    rw [← ha]
    exact (Nat.modEq_iff_dvd' (by nlinarith : 1 ≤ r * r)).mp
      (pow_eq_pow_iff_modEq.mp (hp.trans (pow_one a).symm)).symm
  have hrprod : 2 ^ n ∣ (r - 1) * (r + 1) := by
    convert hrr using 1
    have ht : r - 1 + 1 = r := by omega
    have ht2 : r * r - 1 + 1 = r * r := Nat.sub_add_cancel (by nlinarith)
    nlinarith
  have hrhalf : 2 ^ (n - 1) ∣ r - 1 := by
    have hrplus : r + 1 = 2 * (r / 2 + 1) := by omega
    have hsplit' : 2 ^ n = 2 ^ (n - 1) * 2 := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ]
    rw [hsplit', hrplus, ← mul_assoc, mul_right_comm] at hrprod
    have hdiv := (Nat.mul_dvd_mul_iff_right (by decide : 0 < 2)).mp hrprod
    have hodd : Nat.Coprime 2 (r / 2 + 1) := Nat.coprime_two_left.mpr (by
      exact ⟨r / 4, by omega⟩)
    exact (hodd.pow_left (n - 1)).dvd_mul_right.mp hdiv
  obtain ⟨k, hk⟩ := hrhalf
  have hhalfpos : 0 < 2 ^ (n - 1) := by positivity
  have hsplit' : 2 ^ n = 2 ^ (n - 1) * 2 := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  have hk1 : k = 1 := by
    rw [hsplit'] at hrlt
    have hrminus : r - 1 + 1 = r := by omega
    have hkpos : 0 < k := by
      by_contra h
      have : k = 0 := by omega
      simp [this] at hk
      omega
    nlinarith
  have hrval : r = 1 + 2 ^ (n - 1) := by rw [hk1, mul_one] at hk; omega
  exact ⟨a, e, n, hn3, haA.symm, ha, he, hxA, by rw [← har, hrval]⟩

namespace IsPGroup

/-- A finite two-group with a cyclic normal self-centralizing subgroup and
an elementary abelian subgroup of order at least eight has a normal four-group. -/
public theorem exists_normal_four_of_cyclic_selfcentralizer
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (A : Subgroup P) [A.Normal] [IsCyclic A]
    (hC : Subgroup.centralizer (A : Set P) ≤ A)
    (E : Subgroup P) [IsElementaryAbelian 2 E] (hE : 8 ≤ Nat.card E) :
    ∃ U : Subgroup P, U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4 := by
  obtain ⟨a, e, n, hn, hA, ha, he, heA, hact⟩ := exists_twist hP A hC E hE
  exact hP.exists_normal_four_of_twist A hC a e n hn hA ha he heA hact

end IsPGroup
