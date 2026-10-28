module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Data
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Base
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Reduction
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage.Seven

/-!
# Quintic coverage in the literal degree-100 Hall–Janko carrier

Two commuting fifth-order normal forms generate a certified subgroup of order
25, hence a Sylow subgroup by the carrier order 604800. Twenty-five checked
carrier conjugators cover this subgroup by the existing representatives.
The four nonidentity representatives are fixed-point-free in degree 100.

An element of order seven is conjugate to representative 19, whose fixed set
is exactly {13, 81}. A commuting fifth-order element would act without fixed
points on this pair, contradicting its odd order. This excludes a seven-part.
After removing the factors two and three, Lagrange and Sylow conjugacy then
force order exactly five and give the requested representative coverage.

Source: the retained ATLAS J2G1-p100B0 normal forms and the quintic pair in
`TraceGeometry/Generators.lean`; the group-theoretic argument is Lagrange and
Sylow theory on this literal carrier. `Five/source/` retains the untrusted
witness search. All identities are checked in Lean, using the certified
four-point base where appropriate. ATLAS attribution and data conventions
are in `Theory/SpecificGroups/LeechRelated/AtlasCarriers/source/README.md`.
The proof and witness-search script follow the repository's Apache 2.0 license.
-/

public section
namespace Sporadic.LeechRelated.J2.PowerFusionCertificate
open GeneratorPair.SecondOrbitCertificate

private def fiveX : Carrier := element (84, 51, 16, 2)
private def fiveY : Carrier := element (36, 42, 19, 0)
private def fivePair (i : Fin 5 × Fin 5) : Carrier := fiveX ^ i.1.val * fiveY ^ i.2.val

private theorem fiveX_pow : fiveX ^ 5 = 1 := by
  apply carrier_ext_base
  decide +kernel

private theorem fiveY_pow : fiveY ^ 5 = 1 := by
  apply carrier_ext_base
  decide +kernel

private theorem five_commute : Commute fiveX fiveY := by
  change fiveX * fiveY = fiveY * fiveX
  apply carrier_ext_base
  decide +kernel

private theorem fivePair_zero : fivePair (0, 0) = 1 := by
  simp [fivePair]

private theorem fivePair_mul (i j : Fin 5 × Fin 5) :
    fivePair i * fivePair j = fivePair (i.1 + j.1, i.2 + j.2) := by
  simp only [fivePair, Fin.val_add]
  rw [(five_commute.symm.pow_pow _ _).mul_mul_mul_comm,
    ← pow_add, ← pow_add, pow_eq_pow_mod (i.1.val + j.1.val) fiveX_pow,
    pow_eq_pow_mod (i.2.val + j.2.val) fiveY_pow]

private theorem fivePair_pow (i : Fin 5 × Fin 5) : fivePair i ^ 5 = 1 := by
  rw [fivePair, (five_commute.pow_pow _ _).mul_pow]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm i.1.val 5, Nat.mul_comm i.2.val 5,
    pow_mul, pow_mul, fiveX_pow, fiveY_pow, one_pow, one_pow, mul_one]

private def fiveGroup : Subgroup Carrier where
  carrier := Set.range fivePair
  one_mem' := ⟨(0, 0), fivePair_zero⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨(i.1 + j.1, i.2 + j.2), (fivePair_mul i j).symm⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    let j : Fin 5 × Fin 5 := (i.1 + i.1, i.2 + i.2)
    refine ⟨(j.1 + j.1, j.2 + j.2), ?_⟩
    have hsq : fivePair j = fivePair i ^ 2 := (fivePair_mul i i).symm.trans (pow_two _).symm
    rw [← fivePair_mul, hsq, ← pow_two, ← pow_mul]
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using fivePair_pow i

private theorem fivePair_injective : Function.Injective fivePair := by
  intro i j h
  have he := congrArg (fun g : Carrier => inclusion g 0) h
  exact (by decide +kernel : Function.Injective (fun i => inclusion (fivePair i) 0)) he

private theorem fiveGroup_card : Nat.card fiveGroup = 25 := by
  let f : Fin 5 × Fin 5 → fiveGroup := fun i => ⟨fivePair i, ⟨i, rfl⟩⟩
  have hf : Function.Bijective f := ⟨fun _ _ h => fivePair_injective (congrArg Subtype.val h), by
    rintro ⟨g, i, rfl⟩
    exact ⟨i, rfl⟩⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf)]
  simp

private instance five_prime : Fact (Nat.Prime 5) := ⟨by decide⟩

private def fiveSylow : Sylow 5 Carrier :=
  (IsPGroup.of_card (n := 2) (G := fiveGroup) fiveGroup_card).toSylow (by
    have hc := fiveGroup.card_mul_index
    rw [fiveGroup_card, ExceptionalParabolics.FirstParabolic.card_carrier] at hc
    intro hd
    obtain ⟨k, hk⟩ := hd
    omega)

private theorem conjugate_into_five {g : Carrier} {n : ℕ} (hg : orderOf g = 5 ^ n) :
    ∃ i : Fin 5 × Fin 5, IsConj g (fivePair i) := by
  obtain ⟨y, hy⟩ := fiveSylow.exists_isConj_of_orderOf_eq_prime_pow hg
  obtain ⟨i, hi⟩ := y.property
  exact ⟨i, hi ▸ hy⟩


private def fiveClass (i : Fin 5 × Fin 5) : Fin 21 :=
  match 5 * i.1.val + i.2.val with
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | 3 => 3
  | 4 => 2
  | 5 => 2
  | 6 => 10
  | 7 => 11
  | 8 => 10
  | 9 => 2
  | 10 => 3
  | 11 => 11
  | 12 => 11
  | 13 => 3
  | 14 => 10
  | 15 => 3
  | 16 => 10
  | 17 => 3
  | 18 => 11
  | 19 => 11
  | 20 => 2
  | 21 => 2
  | 22 => 10
  | 23 => 11
  | _ => 10

private def fiveConjugator (i : Fin 5 × Fin 5) : Index :=
  match 5 * i.1.val + i.2.val with
  | 0 => (0, 0, 0, 0)
  | 1 => (17, 24, 9, 2)
  | 2 => (5, 34, 23, 3)
  | 3 => (17, 24, 9, 2)
  | 4 => (5, 34, 23, 3)
  | 5 => (21, 41, 16, 0)
  | 6 => (83, 0, 17, 2)
  | 7 => (79, 31, 12, 0)
  | 8 => (45, 36, 4, 3)
  | 9 => (21, 34, 12, 2)
  | 10 => (5, 26, 21, 3)
  | 11 => (39, 57, 17, 0)
  | 12 => (79, 57, 19, 0)
  | 13 => (17, 48, 14, 0)
  | 14 => (79, 31, 12, 0)
  | 15 => (21, 41, 16, 0)
  | 16 => (45, 8, 11, 0)
  | 17 => (21, 34, 12, 2)
  | 18 => (83, 0, 17, 2)
  | 19 => (45, 36, 4, 3)
  | 20 => (5, 26, 21, 3)
  | 21 => (17, 48, 14, 0)
  | 22 => (39, 57, 17, 0)
  | 23 => (45, 8, 11, 0)
  | _ => (79, 57, 19, 0)

private theorem five_fusion_check : ∀ i j : Fin 5, ∀ k : Fin 4,
    normalForm (fiveConjugator (i,j))
        (normalForm (representativeIndex (fiveClass (i,j))) (k.castLE (by decide))) =
      ((normalForm (84,51,16,2)) ^ i.val * (normalForm (36,42,19,0)) ^ j.val)
        (normalForm (fiveConjugator (i,j)) (k.castLE (by decide))) := by
  apply allFin
  decide +kernel

private theorem fivePair_fusion (i : Fin 5 × Fin 5) :
    IsConj (representative (fiveClass i)) (fivePair i) := by
  apply isConj_of_base _ _ (element (fiveConjugator i))
  intro k
  simpa only [fivePair, fiveX, fiveY, map_mul, map_pow, representative,
    inclusion_element] using five_fusion_check i.1 i.2 k

private theorem five_power_coverage {g : Carrier} {n : ℕ} (hg : orderOf g = 5 ^ n) :
    ∃ i : Fin 21, IsConj (representative i) g := by
  obtain ⟨i, hi⟩ := conjugate_into_five hg
  exact ⟨fiveClass i, (fivePair_fusion i).trans hi.symm⟩

private theorem fiveClass_cases : ∀ i j : Fin 5, (i,j) ≠ (0,0) →
    fiveClass (i,j) = 2 ∨ fiveClass (i,j) = 3 ∨
    fiveClass (i,j) = 10 ∨ fiveClass (i,j) = 11 := by
  apply allFin
  decide +kernel

private theorem five_free_check : ∀ i : Fin 4, ∀ p : Fin 100,
    normalForm (representativeIndex (![2,3,10,11] i)) p ≠ p := by
  apply allFin
  decide +kernel

private theorem fixedPointFree_of_isConj {x y : Carrier} (h : IsConj x y)
    (hx : ∀ p : Fin 100, inclusion x p ≠ p) :
    ∀ p : Fin 100, inclusion y p ≠ p := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have he : c * x = y * c := mul_inv_eq_iff_eq_mul.mp hc
  intro p hp
  apply hx ((inclusion c).symm p)
  apply (inclusion c).injective
  have hh := congrArg (fun g : Carrier => inclusion g ((inclusion c).symm p)) he
  simpa only [map_mul, Equiv.Perm.mul_apply, Equiv.apply_symm_apply, hp] using hh

private theorem order_five_fixedPointFree (g : Carrier) (hg : orderOf g = 5) :
    ∀ p : Fin 100, inclusion g p ≠ p := by
  obtain ⟨i, hi⟩ := conjugate_into_five (hg.trans (pow_one 5).symm)
  have hn : i ≠ (0,0) := by
    intro he
    rw [he, fivePair_zero] at hi
    have hg1 := isConj_one_left.mp hi
    simp only [hg1, orderOf_one] at hg
    exact (by decide : (1 : ℕ) ≠ 5) hg
  apply fixedPointFree_of_isConj ((fivePair_fusion i).trans hi.symm)
  rcases fiveClass_cases i.1 i.2 hn with he | he | he | he
  · simpa [he, representative] using five_free_check 0
  · simpa [he, representative] using five_free_check 1
  · simpa [he, representative] using five_free_check 2
  · simpa [he, representative] using five_free_check 3

private theorem seven_class_check : ∀ i : Fin 21,
    (normalForm (representativeIndex i) ^ 7) 0 = 0 → i = 0 ∨ i = 19 := by
  apply allFin
  decide +kernel

private theorem order_seven_conjugate (g : Carrier) (hg : orderOf g = 7) :
    IsConj (representative 19) g := by
  obtain ⟨i, hi⟩ := covered_of_order_seven g hg
  have hp : g ^ 7 = 1 := hg ▸ pow_orderOf_eq_one g
  have hr : representative i ^ 7 = 1 := by
    have hh := hi.pow 7
    rw [hp] at hh
    exact isConj_one_left.mp hh
  have he : (normalForm (representativeIndex i) ^ 7) 0 = 0 := by
    simpa only [map_pow, map_one, representative, inclusion_element, Equiv.Perm.one_apply]
      using congrArg (fun g : Carrier => inclusion g 0) hr
  rcases seven_class_check i he with rfl | rfl
  · rw [representative_zero] at hi
    have hg1 := isConj_one_right.mp hi
    simp only [hg1, orderOf_one] at hg
    exact ((by decide : (1 : ℕ) ≠ 7) hg).elim
  · exact hi

private theorem seven_fixed_check : ∀ p : Fin 100,
    normalForm (representativeIndex 19) p = p ↔ p = 13 ∨ p = 81 := by
  apply allFin
  decide +kernel

private theorem five_seven_not_commute (g : Carrier) (hg : orderOf g = 5)
    (hc : Commute g (representative 19)) : False := by
  let f := inclusion g
  have preserves (p : Fin 100) (hp : p = 13 ∨ p = 81) : f p = 13 ∨ f p = 81 := by
    apply (seven_fixed_check (f p)).mp
    have hr : inclusion (representative 19) p = p := (seven_fixed_check p).mpr hp
    have he := congrArg (fun z : Carrier => inclusion z p) hc.eq
    change inclusion (representative 19) (f p) = f p
    simpa only [map_mul, Equiv.Perm.mul_apply, hr, f] using he.symm
  have h13 : f 13 = 81 := (preserves 13 (Or.inl rfl)).resolve_left
    (order_five_fixedPointFree g hg 13)
  have h81 : f 81 = 13 := (preserves 81 (Or.inr rfl)).resolve_right
    (order_five_fixedPointFree g hg 81)
  have hp : f ^ 5 = 1 := by
    change inclusion g ^ 5 = 1
    rw [← map_pow, ← hg, pow_orderOf_eq_one, map_one]
  have hf := congrArg (fun q : Equiv.Perm (Fin 100) => q 13) hp
  simp only [pow_succ, pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, h13, h81] at hf
  exact (by decide : (81 : Fin 100) ≠ 13) hf

private theorem not_five_and_seven (g : Carrier) (h5 : 5 ∣ orderOf g) :
    ¬7 ∣ orderOf g := by
  intro h7
  let u := g ^ (orderOf g / 7)
  let v := g ^ (orderOf g / 5)
  have hu : orderOf u = 7 := orderOf_pow_orderOf_div (orderOf_pos g).ne' h7
  have hv : orderOf v = 5 := orderOf_pow_orderOf_div (orderOf_pos g).ne' h5
  obtain ⟨c, hc⟩ := isConj_iff.mp (order_seven_conjugate u hu).symm
  have hcu : MulAut.conj c u = representative 19 := hc
  have hcv : orderOf (MulAut.conj c v) = 5 := by
    rw [MulEquiv.orderOf_eq, hv]
  have hcomm : Commute (MulAut.conj c v) (representative 19) := by
    rw [← hcu]
    exact (Commute.pow_pow_self g _ _).map (MulAut.conj c)
  exact five_seven_not_commute _ hcv hcomm

/-- The odd quintic branch has order exactly five: neither 25 nor a seven-part occurs. -/
theorem order_eq_five_of_no_two_three (g : Carrier) (h2 : ¬2 ∣ orderOf g)
    (h3 : ¬3 ∣ orderOf g) (h5 : 5 ∣ orderOf g) :
    orderOf g = 5 := by
  have c2 : (orderOf g).Coprime (2 ^ 7) :=
    ((Nat.prime_two.coprime_iff_not_dvd.mpr h2).symm).pow_right _
  have c3 : (orderOf g).Coprime (3 ^ 3) :=
    (((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr h3).symm).pow_right _
  have c7 : (orderOf g).Coprime 7 :=
    ((by decide : Nat.Prime 7).coprime_iff_not_dvd.mpr (not_five_and_seven g h5)).symm
  have hd : orderOf g ∣ 2 ^ 7 * (3 ^ 3 * (7 * 5 ^ 2)) := by
    change orderOf g ∣ 604800
    rw [← ExceptionalParabolics.FirstParabolic.card_carrier]
    exact orderOf_dvd_natCard g
  have hd5 : orderOf g ∣ 5 ^ 2 := c7.dvd_of_dvd_mul_left
    (c3.dvd_of_dvd_mul_left (c2.dvd_of_dvd_mul_left hd))
  obtain ⟨n, _, hn⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 5)).mp hd5
  obtain ⟨i, hi⟩ := conjugate_into_five hn
  have hpow := hi.pow 5
  rw [fivePair_pow] at hpow
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (isConj_one_left.mp hpow)) h5

/-- Coverage of every odd-order element divisible by five but not by three. -/
theorem covered_odd_of_five_dvd (g : Carrier) (h2 : ¬2 ∣ orderOf g)
    (h3 : ¬3 ∣ orderOf g) (h5 : 5 ∣ orderOf g) :
    ∃ i : Fin 21, IsConj (representative i) g :=
  five_power_coverage ((order_eq_five_of_no_two_three g h2 h3 h5).trans (pow_one 5).symm)

end Sporadic.LeechRelated.J2.PowerFusionCertificate
