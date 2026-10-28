module

public import CFSG.Quasithin.Chapter14.Section01.SourcePreliminaries.ResidualSplitting.InvertedLift
public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Tactic.NormNum


/-!
# The normal S₃ factor in Lemma 14.1.18

Let a finite group map onto S₃, and let a reflection above a nonidentity
involution centralize the kernel. Its normal closure is the internal S₃
factor, with the kernel as its commuting direct complement.

The normal closure centralizes the kernel and maps onto S₃. Applying the
faithful inverted three-lift inside this closure gives an element of order
three. Together with the reflection it generates a dihedral subgroup of
order six mapping bijectively onto S₃. This subgroup supplements and
centralizes the kernel, hence is normal in the whole group. Minimality of
the normal closure identifies it with this subgroup. Multiplication of the
two factors then gives the asserted isomorphism, with both inclusions and
the original quotient map recorded explicitly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), printed pp.980–981, Lemmas 14.1.17–14.1.18.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter14.SourcePreliminaries


private theorem conjugates_generate :
    ∀ t : Equiv.Perm (Fin 3), t ^ 2 = 1 → t ≠ 1 →
      ∀ s, ∃ a b : Equiv.Perm (Fin 3),
        s = a * t * a⁻¹ ∨ s = (a * t * a⁻¹) * (b * t * b⁻¹) := by
  decide +kernel

private theorem three_two_generate :
    ∀ r t : Equiv.Perm (Fin 3), r ^ 3 = 1 → r ≠ 1 → t ^ 2 = 1 → t ≠ 1 →
      ∀ s, ∃ i : Fin 3, ∃ j : Fin 2, r ^ (i : ℕ) * t ^ (j : ℕ) = s := by
  decide +kernel

private theorem supplement_of_surjective_restriction
    {H Q : Type*} [Group H] [Group Q] (f : H →* Q) (B : Subgroup H)
    (hB : Function.Surjective (f.domRestrict B)) : B ⊔ f.ker = ⊤ := by
  apply top_unique
  intro h _
  obtain ⟨b, hb⟩ := hB (f h)
  have hk : (b : H)⁻¹ * h ∈ f.ker := by
    change f ((b : H)⁻¹ * h) = 1
    simp only [map_mul, map_inv, show f (b : H) = f h from hb, inv_mul_cancel]
  have hm := (B ⊔ f.ker).mul_mem ((show B ≤ B ⊔ f.ker from le_sup_left) b.property)
    ((show f.ker ≤ B ⊔ f.ker from le_sup_right) hk)
  simpa only [mul_inv_cancel_left] using hm

private theorem normalClosure_restriction_bijective
    {H : Type*} [Group H] [Finite H]
    (f : H →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (w : H) (hw : w ^ 2 = 1) (hfw : f w ≠ 1)
    (hcentral : ∀ k ∈ f.ker, w * k = k * w) :
    Function.Bijective (f.domRestrict (normalClosure (zpowers w : Set H))) := by
  let N := normalClosure (zpowers w : Set H)
  have hwN : w ∈ N := le_normalClosure (mem_zpowers w)
  have hNC : N ≤ centralizer (f.ker : Set H) := by
    apply normalClosure_le_normal
    exact zpowers_le.mpr (fun k hk => (hcentral k hk).symm)
  have hNsurj : Function.Surjective (f.domRestrict N) := by
    intro s
    obtain ⟨a, b, hs⟩ := conjugates_generate (f w)
      (by rw [← map_pow, hw, map_one]) hfw s
    obtain ⟨a, rfl⟩ := hf a
    obtain ⟨b, rfl⟩ := hf b
    have haN := (inferInstance : N.Normal).conj_mem w hwN a
    have hbN := (inferInstance : N.Normal).conj_mem w hwN b
    rcases hs with hs | hs
    · exact ⟨⟨a * w * a⁻¹, haN⟩, by simpa using hs.symm⟩
    · exact ⟨⟨(a * w * a⁻¹) * (b * w * b⁻¹), N.mul_mem haN hbN⟩,
        by simpa using hs.symm⟩
  let wn : N := ⟨w, hwN⟩
  obtain ⟨yn, hyn, hfyn, hinvn⟩ := inverted_three_lift_of_centralizing_kernel
    (f.domRestrict N) hNsurj wn
    (Subtype.ext hw) hfw (by
      intro k hk
      apply Subtype.ext
      exact hcentral k (show (k : H) ∈ f.ker from hk))
  let y : H := yn
  have hy : orderOf y = 3 := (orderOf_injective N.subtype N.subtype_injective yn).trans hyn
  have hfy : orderOf (f y) = 3 := hfyn
  have hinv : w * y * w⁻¹ = y⁻¹ := congrArg Subtype.val hinvn
  let B := zpowers y ⊔ zpowers w
  have hBN : B ≤ N := sup_le (zpowers_le.mpr yn.property) (zpowers_le.mpr hwN)
  have hwout : w ∉ zpowers y := by
    intro hwmem
    have hd : orderOf (f w) ∣ 3 := by
      have hd : orderOf (f w) ∣ orderOf (f y) := by
        apply orderOf_dvd_of_mem_zpowers
        rw [← MonoidHom.map_zpowers]
        exact mem_map.mpr ⟨w, hwmem, rfl⟩
      simpa only [hfy] using hd
    have hwo : orderOf (f w) = 2 := orderOf_eq_prime
      (by rw [← map_pow, hw, map_one]) hfw
    rw [hwo] at hd
    norm_num at hd
  obtain ⟨eB⟩ := Subgroup.nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted
    (zpowers y) w inferInstance hw hwout (by
      intro r hr
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hr
      change MulAut.conj w (y ^ i) = (y ^ i)⁻¹
      rw [map_zpow]
      change (w * y * w⁻¹) ^ i = (y ^ i)⁻¹
      rw [hinv, inv_zpow])
  have hBcard : Nat.card B = 6 := by
    rw [Nat.card_congr eB.toEquiv, DihedralGroup.nat_card, Nat.card_zpowers, hy]
  have hBsurj : Function.Surjective (f.domRestrict B) := by
    intro s
    obtain ⟨i, j, hij⟩ := three_two_generate (f y) (f w)
      (by simpa only [hfy] using pow_orderOf_eq_one (f y))
      (by intro h; simp [h] at hfy)
      (by rw [← map_pow, hw, map_one]) hfw s
    exact ⟨⟨y ^ (i : ℕ) * w ^ (j : ℕ), B.mul_mem
      ((show zpowers y ≤ B from le_sup_left) ((zpowers y).pow_mem (mem_zpowers y) _))
      ((show zpowers w ≤ B from le_sup_right) ((zpowers w).pow_mem (mem_zpowers w) _))⟩,
      by simpa using hij⟩
  have hBbij : Function.Bijective (f.domRestrict B) := by
    apply (Nat.bijective_iff_surjective_and_card _).mpr
    exact ⟨hBsurj, by simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using hBcard⟩
  have hsupp := supplement_of_surjective_restriction f B hBsurj
  have hBnormal : B.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hsupp]
    exact sup_le le_normalizer ((le_centralizer_iff.mp (hBN.trans hNC)).trans
      (centralizer_le_normalizer _))
  let : B.Normal := hBnormal
  have hNB : N ≤ B := normalClosure_le_normal (show zpowers w ≤ B from le_sup_right)
  have hNB_eq : N = B := le_antisymm hNB hBN
  change Function.Bijective (f.domRestrict N)
  rw [hNB_eq]
  exact hBbij


/-- A kernel-centralizing reflection normally generates the internal S₃ factor.
The splitting has first coordinate `f` and respects the inclusions of both
specified factors. No restriction on the size or structure of the kernel is needed. -/
public theorem normalClosure_s3_splitting
    {H : Type*} [Group H] [Finite H]
    (f : H →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (w : H) (hw : w ^ 2 = 1) (hfw : f w ≠ 1)
    (hcentral : ∀ k ∈ f.ker, w * k = k * w) :
    let N := normalClosure (zpowers w : Set H)
    Function.Bijective (f.domRestrict N) ∧
      N ⊔ f.ker = ⊤ ∧ Disjoint N f.ker ∧ ⁅N, f.ker⁆ = ⊥ ∧
      ∃ e : H ≃* Equiv.Perm (Fin 3) × f.ker,
        (∀ h, (e h).1 = f h) ∧
        (∀ n : N, e n = (f n, 1)) ∧
        (∀ k : f.ker, e k = (1, k)) := by
  classical
  dsimp only
  let N := normalClosure (zpowers w : Set H)
  have hbij := normalClosure_restriction_bijective f hf w hw hfw hcentral
  have hsupp : N ⊔ f.ker = ⊤ := supplement_of_surjective_restriction f N hbij.2
  have hdis : Disjoint N f.ker := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    have heq : f.domRestrict N ⟨x, hx.1⟩ = f.domRestrict N 1 := by
      simpa using MonoidHom.mem_ker.mp hx.2
    exact congrArg Subtype.val (hbij.1 heq)
  have hNC : N ≤ centralizer (f.ker : Set H) :=
    normalClosure_le_normal (zpowers_le.mpr (fun k hk => (hcentral k hk).symm))
  refine ⟨hbij, hsupp, hdis, commutator_eq_bot_iff_le_centralizer.mpr hNC, ?_⟩
  have hc : ∀ n : N, ∀ k : f.ker, Commute (n : H) (k : H) :=
    fun n k => (hNC n.property k k.property).symm
  let m : N × f.ker →* H := N.subtype.noncommCoprod f.ker.subtype hc
  have hm : Function.Bijective m := by
    refine ⟨mul_injective_of_disjoint hdis, MonoidHom.range_eq_top.mp ?_⟩
    exact (MonoidHom.noncommCoprod_range N.subtype f.ker.subtype hc).trans
      (by simpa only [range_subtype] using hsupp)
  let eN := MulEquiv.ofBijective (f.domRestrict N) hbij
  let eM := MulEquiv.ofBijective m hm
  let e : H ≃* Equiv.Perm (Fin 3) × f.ker :=
    eM.symm.trans (MulEquiv.prodCongr eN (MulEquiv.refl f.ker))
  have he (n : N) (k : f.ker) : e ((n : H) * (k : H)) = (f n, k) := by
    change (MulEquiv.prodCongr eN (MulEquiv.refl f.ker))
      (eM.symm (eM (n, k))) = _
    rw [eM.symm_apply_apply]
    rfl
  refine ⟨e, ?_, ?_, ?_⟩
  · intro h
    obtain ⟨⟨n, k⟩, rfl⟩ := hm.2 h
    change (e ((n : H) * (k : H))).1 = f ((n : H) * (k : H))
    rw [he, map_mul, MonoidHom.mem_ker.mp k.property, mul_one]
  · intro n
    simpa only [coe_one, mul_one] using he n 1
  · intro k
    simpa only [coe_one, one_mul, map_one] using he 1 k

end CFSG.Quasithin.Chapter14.SourcePreliminaries
