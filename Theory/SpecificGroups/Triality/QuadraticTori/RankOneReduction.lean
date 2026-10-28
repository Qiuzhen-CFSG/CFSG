module

public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.LocalCriteria
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal.Order
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.QuadraticTorus.NormOne
public import Mathlib.Data.ZMod.Basic

/-!
# Triality quadratic tori from an orthogonal rank-one product

A faithful embedding of SL₂(q³) × SL₂(q) in the genuine binary triality
carrier supplies tori of orders (q³−1)(q−1) and (q³+1)(q+1). The split
factors use diagonal matrices; the nonsplit factors use the already proved
quadratic-extension norm-one representations. Their inverters in the first
rank-one factor fix the second factor.

For p > 3 dividing q−1 or q+1, the corresponding torus index is 12 modulo p.
Two cyclic Sylow factors therefore map onto an ambient Sylow subgroup.
Independent inversion becomes the power action (2m−1, 1), where m is the
odd order of the first Sylow factor. Its determinant minus one is coprime
to m, including when that factor is trivial. This constructs `TorusPair`
and hence the `Geometry` consumed by the perfect-central-cover reduction.

The faithful rank-one product embedding is an explicit remaining premise.
No identification of the two existing parabolic Levis as commuting factors
is made. In the D₄ root model the relevant orthogonal subsystem comprises
the three simple arms and the highest root. Source: GLS3 §2.6, especially
2.6.2(a,b), in `refs/KGroup/GLS3/chapter2.tex`; the multiplier application is
GLS3 §6.1, Theorem 6.1.4 and Tables 6.1.2–3. The diagonal and Sylow arguments
adapt the existing symplectic `OddNondefining.Split` and `ProductTori` proofs
to two different coefficient fields. The imported G₂ module is used only
for its general finite-field norm-one representation in SL₂.
-/

@[expose] public section

namespace Triality.Standard.QuadraticTori

open Matrix Subgroup PerfectCentralCovering.OddSylow
open Triality.InnerDisplacement.PrimeToTwoCovers.ThreeLocal

private theorem pair_of_inversion {G : Type*} [Group G] (T : Subgroup G)
    (x y w : G) (hgen : closure ({x, y} : Set G) = T)
    (hc : Commute x y) (m : ℕ) (hm : Odd m) (hx : x ^ m = 1)
    (hi : w * x * w⁻¹ = x⁻¹) (hf : w * y * w⁻¹ = y) :
    Nonempty (TorusPair T) := by
  have hmpos : 0 < m := hm.pos
  refine ⟨{
    left := x
    right := y
    actor := w
    generates := hgen
    commute := hc
    exponent := m
    leftPower := 2 * m - 1
    rightPower := 1
    positive := by omega
    coprime := ?_
    pow_eq_one := hx
    conjugate_left := ?_
    conjugate_right := by simpa using hf }⟩
  · rw [mul_one, show 2 * m - 1 - 1 = 2 * (m - 1) by omega]
    exact hm.coprime_two_right.mul_right
      ((Nat.coprime_self_sub_right hmpos).mpr (Nat.coprime_one_right m))
  · rw [hi, pow_sub _ (by omega : 1 ≤ 2 * m), pow_mul', hx]
    simp

private theorem paired_cyclic {G C D : Type*} [Group G] [Finite G]
    [CommGroup C] [Finite C] [IsCyclic C] [CommGroup D] [Finite D] [IsCyclic D]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (ι : C × D →* G) (hι : Function.Injective ι)
    (hpindex : ¬ p ∣ ι.range.index) (w : G)
    (hinv : ∀ c : C, w * ι (c,1) * w⁻¹ = ι (c⁻¹,1))
    (hfix : ∀ d : D, w * ι (1,d) * w⁻¹ = ι (1,d)) :
    ∃ P : Sylow p G, Nonempty (TorusPair (P : Subgroup G)) := by
  classical
  have hp : p.Prime := Fact.out
  let R : Sylow p C := default
  let S : Sylow p D := default
  let A : Subgroup (C × D) := (R : Subgroup C).prod (S : Subgroup D)
  obtain ⟨m, hm⟩ := R.isPGroup'.exists_card_eq
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  have hAp : IsPGroup p A := by
    apply IsPGroup.of_card (n := m + k)
    rw [Nat.card_congr (Subgroup.prodEquiv (R : Subgroup C) (S : Subgroup D)).toEquiv,
      Nat.card_prod, hm, hk, pow_add]
  let Q : Subgroup G := A.map ι
  have hQp : IsPGroup p Q := hAp.map ι
  have hQi : ¬ p ∣ Q.index := by
    rw [Subgroup.index_map_of_injective _ hι, Subgroup.index_prod]
    exact hp.not_dvd_mul (hp.not_dvd_mul R.not_dvd_index S.not_dvd_index) hpindex
  let P : Sylow p G := hQp.toSylow hQi
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := R)
  obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := S)
  let x := ι ((a : C),1)
  let y := ι (1,(b : D))
  have hxQ : x ∈ Q := ⟨((a : C),1), ⟨a.property, (S : Subgroup D).one_mem⟩, rfl⟩
  have hyQ : y ∈ Q := ⟨(1,(b : D)), ⟨(R : Subgroup C).one_mem, b.property⟩, rfl⟩
  have hgen : closure ({x,y} : Set G) = Q := by
    apply le_antisymm
    · apply (closure_le Q).mpr
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact hxQ
      · exact hyQ
    · intro z hz
      obtain ⟨⟨c,d⟩, hcd, he⟩ := hz
      obtain ⟨i, hi⟩ := ha ⟨c, hcd.1⟩
      obtain ⟨j, hj⟩ := hb ⟨d, hcd.2⟩
      have hz : z = x ^ i * y ^ j := by
        rw [← he, ← map_zpow, ← map_zpow, ← map_mul]
        apply congrArg ι
        apply Prod.ext
        · simpa using (congrArg (fun u : R => (u : C)) hi).symm
        · simpa using (congrArg (fun u : S => (u : D)) hj).symm
      rw [hz]
      exact mul_mem (zpow_mem (subset_closure (by simp)) i)
        (zpow_mem (subset_closure (by simp)) j)
  refine ⟨P, pair_of_inversion Q x y w hgen
    ((Commute.all ((a : C),1) (1,(b : D))).map ι) (Nat.card R) ?_ ?_ ?_ (hfix b)⟩
  · rw [hm]
    exact (hp.odd_of_ne_two hp2).pow
  · have he : (a : C) ^ Nat.card R = 1 :=
      congrArg Subtype.val (pow_card_eq_one' (x := a))
    change ι ((a : C),1) ^ Nat.card R = 1
    rw [← map_pow]
    simpa using congrArg ι (show ((a : C), (1 : D)) ^ Nat.card R = 1 by ext <;> simp [he])
  · exact (hinv a).trans (by simpa using ι.map_inv ((a : C),1))

private theorem twelve_ne_zero {p : ℕ} [Fact p.Prime] (hp : 3 < p) :
    (12 : ZMod p) ≠ 0 := by
  have h2 : ¬ p ∣ 2 := fun h => by have := Nat.le_of_dvd (by decide : 0 < 2) h; omega
  have h3 : ¬ p ∣ 3 := fun h => by have := Nat.le_of_dvd (by decide : 0 < 3) h; omega
  have h12 : ¬ p ∣ 12 := by
    simpa using (Fact.out : p.Prime).not_dvd_mul
      ((Fact.out : p.Prime).not_dvd_mul h2 h2) h3
  exact fun h => h12 ((ZMod.natCast_eq_zero_iff 12 p).mp h)

/-- The split-torus index follows from its order in the literal binary carrier. -/
theorem split_torus_index_of_card (n : ℕ) (hn : 0 < n) (A : Subgroup (BinaryCarrier n hn))
    (hA : Nat.card A = ((2 ^ n) ^ 3 - 1) * (2 ^ n - 1)) :
    A.index = (2 ^ n) ^ 12 * (((2 ^ n) ^ 3 + 1) * (2 ^ n + 1) *
      ((2 ^ n) ^ 8 + (2 ^ n) ^ 4 + 1)) := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := A))
  rw [card_mul_index, card_binaryCarrier n hn, hA]
  ring

/-- Every prime greater than three dividing q−1 misses the split-torus index. -/
theorem not_dvd_split_index (n : ℕ) (hn : 0 < n)
    (A : Subgroup (BinaryCarrier n hn))
    (hA : Nat.card A = ((2 ^ n) ^ 3 - 1) * (2 ^ n - 1))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hd : p ∣ 2 ^ n - 1) :
    ¬ p ∣ A.index := by
  have hq : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
  have hqz : ((2 ^ n : ℕ) : ZMod p) = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (2 ^ n - 1) p).mpr hd
    rw [Nat.cast_sub hq, Nat.cast_one, sub_eq_zero] at h
    exact h
  intro h
  have hz := (ZMod.natCast_eq_zero_iff A.index p).mpr h
  rw [split_torus_index_of_card n hn A hA] at hz
  have h12 : (12 : ZMod p) = 0 := by
    have hqz' : (2 : ZMod p) ^ n = 1 := by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hqz
    norm_num [hqz'] at hz ⊢
    exact hz
  exact twelve_ne_zero hp h12

/-- Every prime greater than three dividing q+1 misses the nonsplit-torus index. -/
theorem not_dvd_nonsplit_index (n : ℕ) (hn : 0 < n)
    (A : Subgroup (BinaryCarrier n hn))
    (hA : Nat.card A = ((2 ^ n) ^ 3 + 1) * (2 ^ n + 1))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hd : p ∣ 2 ^ n + 1) :
    ¬ p ∣ A.index := by
  have hq : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by decide)
  have hq3 : 1 ≤ (2 ^ n) ^ 3 := Nat.one_le_pow 3 _ hq
  have hqz : ((2 ^ n : ℕ) : ZMod p) = -1 := by
    have h := (ZMod.natCast_eq_zero_iff (2 ^ n + 1) p).mpr hd
    rw [Nat.cast_add, Nat.cast_one, add_eq_zero_iff_eq_neg] at h
    exact h
  intro h
  have hz := (ZMod.natCast_eq_zero_iff A.index p).mpr h
  rw [nonsplit_torus_index n hn A hA] at hz
  have h12 : (12 : ZMod p) = 0 := by
    have hqz' : (2 : ZMod p) ^ n = -1 := by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hqz
    norm_num [Nat.cast_sub hq3, Nat.cast_sub hq, hqz'] at hz ⊢
    exact hz
  exact twelve_ne_zero hp h12

private def diagonalHom {F : Type*} [Field F] : Fˣ →* SpecialLinearGroup (Fin 2) F where
  toFun a := ⟨!![(a : F), 0; 0, (↑a⁻¹ : F)], by simp [det_fin_two]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    change !![(↑(a*b) : F), 0; 0, (↑((a*b)⁻¹) : F)] =
      !![(a : F), 0; 0, (↑a⁻¹ : F)] * !![(b : F), 0; 0, (↑b⁻¹ : F)]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_two, mul_comm]

private theorem diagonalHom_injective {F : Type*} [Field F] :
    Function.Injective (diagonalHom (F := F)) := by
  intro a b h
  exact Units.ext (congrArg (fun g : SpecialLinearGroup (Fin 2) F => g 0 0) h)

private def reflection {F : Type*} [Field F] : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, -1; 1, 0], by simp [det_fin_two]⟩

private theorem reflection_conjugate {F : Type*} [Field F] (a : Fˣ) :
    reflection * diagonalHom a * reflection⁻¹ = diagonalHom a⁻¹ := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  change !![0, -1; 1, 0] * !![(a : F), 0; 0, (↑a⁻¹ : F)] =
    !![(↑a⁻¹ : F), 0; 0, (↑((a⁻¹)⁻¹) : F)] * !![0, -1; 1, 0]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]

private theorem product_inversion
    {G H K C D : Type*} [Group G] [Group H] [Group K] [Group C] [Group D]
    (j : H × K →* G) (hj : Function.Injective j)
    (s : C →* H) (t : D →* K) (hs : Function.Injective s) (ht : Function.Injective t)
    (v : H) (hv : ∀ c, v * s c * v⁻¹ = s c⁻¹) :
    ∃ (ι : C × D →* G) (w : G), Function.Injective ι ∧
      (∀ c, w * ι (c,1) * w⁻¹ = ι (c⁻¹,1)) ∧
      (∀ d, w * ι (1,d) * w⁻¹ = ι (1,d)) := by
  let ι := j.comp (s.prodMap t)
  refine ⟨ι, j (v,1), hj.comp (Prod.map_injective.mpr ⟨hs, ht⟩), ?_, ?_⟩
  · intro c
    change j (v,1) * j (s c,t 1) * (j (v,1))⁻¹ = j (s c⁻¹,t 1)
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg j
    apply Prod.ext
    · exact hv c
    · simp
  · intro d
    change j (v,1) * j (s 1,t d) * (j (v,1))⁻¹ = j (s 1,t d)
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg j
    apply Prod.ext <;> simp

/-- The orthogonal rank-one subsystem whose faithful embedding remains to be constructed. -/
abbrev RankOneProduct (n : ℕ) :=
  SpecialLinearGroup (Fin 2) (GaloisField 2 (3 * n)) ×
    SpecialLinearGroup (Fin 2) (GaloisField 2 n)

/-- Norm-one units of the quadratic extension of the cubic coefficient field. -/
noncomputable abbrev NonsplitLeft (n : ℕ) :=
  Atlas.G2.MultiplierOrdinary.Nondefining.QuadraticTorus.normOne
    (GaloisField 2 (3 * n))

/-- Norm-one units of the quadratic extension of the base coefficient field. -/
noncomputable abbrev NonsplitRight (n : ℕ) :=
  Atlas.G2.MultiplierOrdinary.Nondefining.QuadraticTorus.normOne (GaloisField 2 n)

/-- Diagonal units in the two supplied rank-one factors give the full split torus
and an ambient element inverting the first factor and fixing the second. -/
theorem exists_split_product_of_rankOneProduct (n : ℕ) (hn : 0 < n)
    (j : RankOneProduct n →* BinaryCarrier n hn) (hj : Function.Injective j) :
    ∃ (ι : (GaloisField 2 (3 * n))ˣ × (GaloisField 2 n)ˣ →*
        BinaryCarrier n hn) (w : BinaryCarrier n hn),
      Function.Injective ι ∧
      Nat.card ι.range = ((2 ^ n) ^ 3 - 1) * (2 ^ n - 1) ∧
      (∀ c, w * ι (c,1) * w⁻¹ = ι (c⁻¹,1)) ∧
      (∀ d, w * ι (1,d) * w⁻¹ = ι (1,d)) := by
  obtain ⟨ι, w, hi, hleft, hright⟩ := product_inversion j hj
    diagonalHom diagonalHom diagonalHom_injective diagonalHom_injective
    reflection reflection_conjugate
  refine ⟨ι, w, hi, ?_, hleft, hright⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv,
    Nat.card_prod, Nat.card_units, Nat.card_units]
  have hbase : Nat.card (GaloisField 2 n) = 2 ^ n := card_baseField (binaryParameters n hn)
  have hext : Nat.card (GaloisField 2 (3 * n)) = (2 ^ n) ^ 3 :=
    card_extensionField (binaryParameters n hn)
  rw [hbase, hext]

/-- The genuine quadratic-extension norm-one tori give the full nonsplit order
and independent inversion, conditional only on the faithful rank-one product map. -/
theorem exists_nonsplit_product_of_rankOneProduct (n : ℕ) (hn : 0 < n)
    (j : RankOneProduct n →* BinaryCarrier n hn) (hj : Function.Injective j) :
    ∃ (ι : NonsplitLeft n × NonsplitRight n →* BinaryCarrier n hn)
      (w : BinaryCarrier n hn), Function.Injective ι ∧
      Nat.card ι.range = ((2 ^ n) ^ 3 + 1) * (2 ^ n + 1) ∧
      (∀ c, w * ι (c,1) * w⁻¹ = ι (c⁻¹,1)) ∧
      (∀ d, w * ι (1,d) * w⁻¹ = ι (1,d)) := by
  obtain ⟨s, v, hs, hv⟩ :=
    Atlas.G2.MultiplierOrdinary.Nondefining.QuadraticTorus.exists_normOne_SL
      (F := GaloisField 2 (3 * n))
  obtain ⟨t, _, ht, _⟩ :=
    Atlas.G2.MultiplierOrdinary.Nondefining.QuadraticTorus.exists_normOne_SL
      (F := GaloisField 2 n)
  obtain ⟨ι, w, hi, hleft, hright⟩ := product_inversion j hj s t hs ht v hv
  refine ⟨ι, w, hi, ?_, hleft, hright⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv, Nat.card_prod,
    Atlas.G2.MultiplierOrdinary.Nondefining.QuadraticTorus.card_normOne,
    Atlas.G2.MultiplierOrdinary.Nondefining.QuadraticTorus.card_normOne]
  have hbase : Nat.card (GaloisField 2 n) = 2 ^ n := card_baseField (binaryParameters n hn)
  have hext : Nat.card (GaloisField 2 (3 * n)) = (2 ^ n) ^ 3 :=
    card_extensionField (binaryParameters n hn)
  rw [hbase, hext]

/-- Both quadratic branches supply an actual Sylow subgroup with commuting
generators and the positive power exponents required by `TorusPair`. -/
theorem exists_torusPair_of_rankOneProduct (n : ℕ) (hn : 0 < n)
    (j : RankOneProduct n →* BinaryCarrier n hn) (hj : Function.Injective j)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hd : p ∣ (2 ^ n) ^ 2 - 1) :
    ∃ Q : Sylow p (BinaryCarrier n hn), Nonempty (TorusPair (Q : Subgroup (BinaryCarrier n hn))) := by
  have hfac : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq (2 ^ n) 1
  rw [hfac] at hd
  rcases (Fact.out : p.Prime).dvd_mul.mp hd with hminus | hplus
  · obtain ⟨ι, w, hi, hcard, hinv, hfix⟩ :=
      exists_split_product_of_rankOneProduct n hn j hj
    exact paired_cyclic (by omega) ι hi
      (not_dvd_split_index n hn ι.range hcard hp hminus) w hinv hfix
  · obtain ⟨ι, w, hi, hcard, hinv, hfix⟩ :=
      exists_nonsplit_product_of_rankOneProduct n hn j hj
    exact paired_cyclic (by omega) ι hi
      (not_dvd_nonsplit_index n hn ι.range hcard hp hplus) w hinv hfix

/-- Consumer of the two finite-field constructions and the exact index arguments.
Final source assembly must supply the displayed faithful rank-one product map. -/
theorem geometry_of_rankOneProduct (n : ℕ) (hn : 0 < n)
    (j : RankOneProduct n →* BinaryCarrier n hn) (hj : Function.Injective j)
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hd : p ∣ (2 ^ n) ^ 2 - 1) :
    Geometry p (BinaryCarrier n hn) := by
  obtain ⟨Q, ⟨d⟩⟩ := exists_torusPair_of_rankOneProduct n hn j hj hp hd
  exact Geometry.torus Q d


end Triality.Standard.QuadraticTori
