module
public import Theory.Representation.HermitianTensorThree.ParabolicTorus.ActorFixed
public import Theory.GroupTheory.OddPrimeSectionCentralizers.ThreeAxes
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.NormalizerAction.Permutations

/-!
# Split determinant norms and the actual rank-two cover

A prime dividing the split determinant norm supplies an element of that prime
order in the cyclic determinant group. Multiplying by determinant-one matrices
places all three independent diagonal axes in the same congruence image.
Their congruence action is faithful because the prime is coprime to 2^n + 1.
A special-linear coordinate swap interchanges two axes. The involution
centralizer theorem excludes this configuration in an image of a group of
odd-prime rank at most two. Rank stays on the actual cover throughout.

This supplies the ambient scalar obstruction needed after the plane-fixed
determinant calculation; it applies to arbitrary covering homomorphisms whose
images contain the literal special-linear Hermitian image.

Source: Aschbacher–Smith H.4.4(5) and 8.2.4, printed pp.381 and716,
using the section-centralizer input A.1.31(1), printed pp.27–28
(1 March 2004 manuscript, refs/quasithin.pdf).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Subgroup Representation Representation.BinaryOffender
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open Representation.HermitianTensorThree.ImageOuter.FieldSections
open UnitaryThree.OddTorusNormalizer
namespace Representation.HermitianTensorThree.ParabolicTorus
variable (n : ℕ) [NeZero n]

private def normUnits : (E n)ˣ →* (E n)ˣ :=
  (MonoidHom.id _) * (Units.map (sigma n).toMonoidHom)

private theorem congruence_mem_of_det_mem
    (H : Subgroup (BinaryAut n)) (hH : binaryImage n ≤ H)
    (g : GeneralLinearGroup (Fin 3) (E n)) (hg : binaryCongruence n g ∈ H)
    (a : GeneralLinearGroup (Fin 3) (E n))
    (ha : GeneralLinearGroup.det a ∈ zpowers (GeneralLinearGroup.det g)) :
    binaryCongruence n a ∈ H := by
  obtain ⟨m,hm⟩ := mem_zpowers_iff.mp ha
  let b := a * (g^m)⁻¹
  have hb : b.val.det = 1 := by
    have hh : GeneralLinearGroup.det b = 1 := by
      change GeneralLinearGroup.det (a * (g^m)⁻¹) = 1
      rw [map_mul,map_inv,map_zpow,←hm,mul_inv_cancel]
    exact congrArg Units.val hh
  let s : Cover n := ⟨b.val,hb⟩
  have hs : Matrix.SpecialLinearGroup.toGL s = b := Units.ext rfl
  have hbs : binaryCongruence n b ∈ H := by
    rw [←hs,binaryCongruence_toGL]
    exact hH ⟨s,rfl⟩
  have he : a = b * g^m := by simp [b,mul_assoc]
  rw [he,map_mul,map_zpow]
  exact H.mul_mem hbs (H.zpow_mem hg m)

private theorem diagonal_norm (a : Fin 3 → (E n)ˣ) (i : Fin 3) :
    (binaryCongruence n (diagonalHom a) (diagonalUnit n i)).val i i =
      (a i : E n) * sigma n (a i : E n) := by
  change ((diagonalHom a).val * (diagonalUnit n i).val * adjoint n (diagonalHom a).val) i i = _
  simp [diagonalHom,diagonalUnit,Matrix.mul_apply,Matrix.single_apply,adjoint,ite_and]

/-- A determinant prime from the split fixed-field torus cannot occur in an
actual rank-two cover containing the special linear image. -/
theorem no_split_det_prime_in_rank_two_cover
    {K : Type*} [Group K] [Finite K]
    (f : K →* BinaryAut n) (hinner : binaryImage n ≤ f.range)
    (p : ℕ) [Fact p.Prime] (hp : Odd p) (hcop : Nat.Coprime p (2^n+1))
    (hrank : primeRank p K ≤ 2)
    (g : GeneralLinearGroup (Fin 3) (E n)) (hg : binaryCongruence n g ∈ f.range)
    (hpd : p ∣ orderOf (GeneralLinearGroup.det g)) : False := by
  let H := f.range
  let : Finite H := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let C₀ := zpowers (GeneralLinearGroup.det g)
  have hpc : p ∣ Nat.card C₀ := by simpa only [C₀,Nat.card_zpowers] using hpd
  obtain ⟨l,hl⟩ := exists_prime_orderOf_dvd_card' (G := C₀) p hpc
  let lam := l.val
  have hlam : orderOf lam = p := (Subgroup.orderOf_coe l).trans hl
  let C := zpowers lam
  have hc : Nat.card C = p := by rw [Nat.card_zpowers,hlam]
  have hC : C ≤ C₀ := zpowers_le.mpr l.property
  have hnorm (a : C) (ha : (a.val : E n) * sigma n (a.val : E n) = 1) : a = 1 := by
    have hpow : a^(2^n+1) = 1 := by
      apply Subtype.ext
      apply Units.ext
      change (a.val : E n)^(2^n+1) = 1
      change (a.val : E n) * iterateFrobeniusEquiv (E n) 2 n (a.val : E n) = 1 at ha
      rw [iterateFrobeniusEquiv_def] at ha
      simpa only [pow_succ'] using ha
    have hd := orderOf_dvd_natCard a
    rw [hc] at hd
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hcop hd (orderOf_dvd_of_pow_eq_one hpow))
  let inc : (Fin 3 → C) →* (Fin 3 → (E n)ˣ) :=
    { toFun := fun a i => (a i).val
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hall (a : Fin 3 → C) : binaryCongruence n (diagonalHom (inc a)) ∈ H := by
    apply congruence_mem_of_det_mem n H hinner g hg
    have he : GeneralLinearGroup.det (diagonalHom (inc a)) = ∏ i, (a i).val := by
      apply Units.ext
      simp [diagonalHom,GeneralLinearGroup.det,Matrix.det_diagonal,inc]
    rw [he]
    exact C₀.prod_mem (fun i _ => hC (a i).property)
  let j : (Fin 3 → C) →* H :=
    ((binaryCongruence n).comp (diagonalHom.comp inc)).codRestrict H hall
  have hj : Function.Injective j := by
    apply (injective_iff_map_eq_one j).mpr
    intro a ha
    have he : binaryCongruence n (diagonalHom (inc a)) = 1 := congrArg Subtype.val ha
    funext i
    apply hnorm
    have hh := congrArg (fun z : BinaryAut n => (z (diagonalUnit n i)).val i i) he
    rw [diagonal_norm] at hh
    simpa [diagonalUnit,inc] using hh
  let τ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let u : GeneralLinearGroup (Fin 3) (E n) := permutationGL τ
  have hu : u.val.det = 1 := by
    change ((τ⁻¹).permMatrix (E n)).det = 1
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ⁻¹) with h | h <;>
      simp [h,CharTwo.neg_eq]
  let s : Cover n := ⟨u.val,hu⟩
  have hs : Matrix.SpecialLinearGroup.toGL s = u := Units.ext rfl
  have huH : binaryCongruence n u ∈ H := by
    rw [←hs,binaryCongruence_toGL]
    exact hinner ⟨s,rfl⟩
  let t : H := ⟨binaryCongruence n u,huH⟩
  have ht : orderOf t = 2 := by
    apply orderOf_eq_prime_iff.mpr
    constructor
    · apply Subtype.ext
      change binaryCongruence n u ^ 2 = 1
      rw [←map_pow]
      have he : u^2 = 1 := by
        change permutationGL τ ^ 2 = 1
        rw [←map_pow]
        have htau : τ^2 = 1 := by simp [τ,pow_two]
        rw [htau,map_one]
      rw [he,map_one]
    · intro he
      have hh := congrArg (fun z : H => (z.val (diagonalUnit n 0)).val 0 0) he
      change (u.val * (diagonalUnit n 0).val * adjoint n u.val) 0 0 =
        (diagonalUnit n 0).val 0 0 at hh
      simp [u,τ,permutationGL_apply,diagonalUnit,Matrix.mul_apply,
        Matrix.single_apply,adjoint,Fin.sum_univ_three,Equiv.swap_apply_def] at hh
  have hswap (a : Fin 3 → C) : t*j a*t⁻¹ = j (a ∘ Equiv.swap (0 : Fin 3) 1) := by
    apply Subtype.ext
    change binaryCongruence n u * binaryCongruence n (diagonalHom (inc a)) *
      (binaryCongruence n u)⁻¹ = binaryCongruence n (diagonalHom (inc (a ∘ τ)))
    rw [←map_inv,←map_mul,←map_mul]
    congr 1
    apply Units.ext
    change (permutationGL τ).val * (diagonalHom (inc a)).val *
      ((permutationGL τ)⁻¹).val = (diagonalHom (inc (a ∘ τ))).val
    rw [←map_inv]
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [permutationGL_apply,τ,diagonalHom,inc,Matrix.mul_apply,
        Fin.sum_univ_three,Equiv.swap_apply_def]
  exact Theory.GroupTheory.no_three_axes_swapped_in_rank_two_section
    hp f.rangeRestrict f.rangeRestrict_surjective hrank hc j hj t ht hswap

/-- The determinant norm of a plane-fixing split torus contradicts the
odd-prime ranks of its actual cover. No quotient-rank bound is assumed. -/
theorem no_split_det_norm_in_rank_two_cover
    {K : Type*} [Group K] [Finite K]
    (f : K →* BinaryAut n) (hinner : binaryImage n ≤ f.range)
    (hrank : ∀ p, p.Prime → Odd p → primeRank p K ≤ 2)
    (g : GeneralLinearGroup (Fin 3) (E n)) (hg : binaryCongruence n g ∈ f.range)
    (ho : orderOf (g.val.det * sigma n g.val.det) = 2^n-1) (hn : 1 < n) : False := by
  have hq : 4 ≤ 2^n := by
    calc 4 = 2^2 := by decide
         _ ≤ 2^n := Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd (show 2^n-1 ≠ 1 by omega)
  let : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (2^n-1) := Nat.Even.sub_odd (Nat.one_le_pow n 2 (by decide))
    (Nat.even_pow.mpr ⟨by decide,NeZero.ne n⟩) odd_one
  have hpo : Odd p := hodd.of_dvd_nat hpd
  have hcop : Nat.Coprime p (2^n+1) := by
    apply hp.coprime_iff_not_dvd.mpr
    intro hd
    have hd2 : p ∣ 2 := by
      have hh := Nat.dvd_sub hd hpd
      have he : (2^n+1)-(2^n-1) = 2 := by omega
      rwa [he] at hh
    have he : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp hd2).resolve_left hp.ne_one
    rw [he] at hpo
    exact (by decide : ¬ Odd 2) hpo
  have hod : orderOf (normUnits n (GeneralLinearGroup.det g)) = 2^n-1 := by
    rw [←orderOf_units]
    exact ho
  have hd : p ∣ orderOf (GeneralLinearGroup.det g) :=
    (hod ▸ hpd).trans (orderOf_map_dvd (normUnits n) (GeneralLinearGroup.det g))
  exact no_split_det_prime_in_rank_two_cover n f hinner p hpo hcop (hrank p hp hpo) g hg hd

end Representation.HermitianTensorThree.ParabolicTorus
