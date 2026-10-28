module

public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.LinearQuadratic.SplitNorm
public import Theory.GroupTheory.PerfectCentralCoverThreeCycleNorm
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# Split-torus primes in degree-four linear covering kernels

Let U be a Sylow r-subgroup of the units of a finite field of prime order p,
where r is odd and divides p − 1. The three independent coordinates of the
literal determinant-one diagonal torus have cyclic generators. Signed
transpositions exchange any two of them, correcting the determinant on the
fourth coordinate. The swapping lemma for central extensions therefore makes
the full torus preimage abelian in every perfect central cover of PSL₄.

The order formula retains the scalar center of order gcd(4,p−1). After
cancelling the torus order, the remaining polynomial factor is
p⁶(p+1)²(p²+1)(p²+p+1). For r ≠ 3 it is nonzero modulo r; for r = 3
it is nonzero modulo nine. The actual coordinate three-cycle is outside the
projective torus, so adjoining it multiplies the torus order by three and
gives index prime to r in both cases. `SplitNorm` supplies the cubic norm
surjectivity and central transfer, including at r = 3.

This proves the split-prime part of the covering calculation used in
Aschbacher–Smith A.2.17, printed p.39, with the perfect central covering
convention and transfer principle of I.1.1–I.1.2, printed p.407. No multiplier
value or lift from the natural special-linear cover is assumed. The signed
matrices follow the same coordinate construction as `UnitaryQuadratic.Diagonal`;
the projective order formula is the attributed ATLAS port in
`AtlasPort.ExceptionalIsomorphisms.Support` (see LICENSES/ATLAS.txt).
-/

open Matrix Subgroup
open scoped MatrixGroups IsMulCommutative
noncomputable section
namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining.LinearQuadratic.Split
open Theory.SpecificGroups.HigherClassicalCovers.Nondefining.LinearQuadratic
variable {F : Type*} [Field F]

def swapMatrix (k : Fin 3) : Matrix (Fin 4) (Fin 4) F :=
  ![!![0,1,0,0; 1,0,0,0; 0,0,1,0; 0,0,0,-1],
    !![0,0,1,0; 0,1,0,0; 1,0,0,0; 0,0,0,-1],
    !![1,0,0,0; 0,0,1,0; 0,1,0,0; 0,0,0,-1]] k

def swapSL (k : Fin 3) : SL(4,F) :=
  ⟨swapMatrix k, by
    fin_cases k <;> simp [swapMatrix, Matrix.det_succ_row_zero,
      Fin.sum_univ_succ, Matrix.submatrix, Fin.succAbove]⟩

def swap (k : Fin 3) : PSL(4,F) := QuotientGroup.mk' _ (swapSL k)

def swapEntries {C : Type*} (k : Fin 3) (a : Fin 3 → C) : Fin 3 → C :=
  ![![a 1,a 0,a 2], ![a 2,a 1,a 0], ![a 0,a 2,a 1]] k

theorem swapMatrix_diagonal (k : Fin 3) (d : Fin 4 → F) :
    swapMatrix k * diagonal d =
      diagonal (![![d 1,d 0,d 2,d 3], ![d 2,d 1,d 0,d 3], ![d 0,d 2,d 1,d 3]] k) *
        swapMatrix k := by
  ext i j
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases k <;> fin_cases i <;> fin_cases j <;> simp [swapMatrix]

theorem swap_torus (U : Subgroup Fˣ) (k : Fin 3) (a : Fin 3 → U) :
    swap k * torusHom U a * (swap k)⁻¹ = torusHom U (swapEntries k a) := by
  change QuotientGroup.mk' _ (swapSL (F := F) k) *
    QuotientGroup.mk' _ (Matrix.PSL4.OddSplitTorus.torusFour F (fun i => (a i).val)) *
    (QuotientGroup.mk' _ (swapSL (F := F) k))⁻¹ =
    QuotientGroup.mk' _ (Matrix.PSL4.OddSplitTorus.torusFour F
      (fun i => (swapEntries k a i).val))
  rw [← map_inv, ← map_mul, ← map_mul]
  apply congrArg
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Subtype.ext
  change swapMatrix k * diagonal _ = diagonal _ * swapMatrix k
  rw [swapMatrix_diagonal]
  congr 2
  funext i
  fin_cases k <;> fin_cases i <;>
    simp [swapEntries, mul_comm, mul_left_comm, mul_assoc]

theorem exists_coordinate_swap (U : Subgroup Fˣ) (i j : Fin 3) (hij : i ≠ j) :
    ∃ s : PSL(4,F), ∀ u : U,
      s * torusHom U (Pi.mulSingle i u) * s⁻¹ = torusHom U (Pi.mulSingle j u) ∧
      s * torusHom U (Pi.mulSingle j u) * s⁻¹ = torusHom U (Pi.mulSingle i u) := by
  fin_cases i <;> fin_cases j <;> try exact False.elim (hij rfl)
  all_goals solve
  | refine ⟨swap 0, ?_⟩
    intro u
    constructor <;> rw [swap_torus] <;> congr 1 <;> ext l <;>
      fin_cases l <;> simp [swapEntries]
  | refine ⟨swap 1, ?_⟩
    intro u
    constructor <;> rw [swap_torus] <;> congr 1 <;> ext l <;>
      fin_cases l <;> simp [swapEntries]
  | refine ⟨swap 2, ?_⟩
    intro u
    constructor <;> rw [swap_torus] <;> congr 1 <;> ext l <;>
      fin_cases l <;> simp [swapEntries]

/-- Signed coordinate swaps force the full torus preimage to be abelian. -/
theorem abelian_preimage (U : Subgroup Fˣ) [Finite U] (ho : Odd (Nat.card U))
    {E : Type*} [Group E] (f : PerfectCentralCovering.Cover E PSL(4,F)) :
    IsMulCommutative ((torus U).comap f.toMonoidHom) := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := U)
  apply PerfectCentralCovering.isMulCommutative_comap_of_swapped_generators
    f.toMonoidHom f.surjective f.ker_le_center (torus U)
    (fun i : Fin 3 => torusHom U (Pi.mulSingle i u))
    (PerfectCentralCovering.closure_coordinate_generators (torusHom U) u hu)
  · intro i j
    exact (Commute.all _ _).map (torusHom U)
  · intro i j hij
    obtain ⟨s, hs⟩ := exists_coordinate_swap U i j hij
    exact ⟨s, hs u⟩
  · exact ho.coprime_two_right
  · intro i
    rw [← map_pow, ← Pi.mulSingle_pow, pow_card_eq_one', Pi.mulSingle_one, map_one]

theorem cycle_not_mem_torus (U : Subgroup Fˣ) : (cycle : PSL(4,F)) ∉ torus U := by
  rintro ⟨a, ha⟩
  have hh : QuotientGroup.mk' (center SL(4,F))
      (Matrix.PSL4.OddSplitTorus.torusFour F (fun i => (a i).val) * cycleSL⁻¹) = 1 := by
    rw [map_mul, map_inv]
    change torusHom U a * cycle⁻¹ = 1
    rw [ha, mul_inv_cancel]
  obtain ⟨v, _, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp
    ((QuotientGroup.eq_one_iff _).mp hh)
  have hm : Matrix.scalar (Fin 4) v * (cycleSL : SL(4,F)).val =
      (Matrix.PSL4.OddSplitTorus.torusFour F (fun i => (a i).val)).val := by
    rw [he, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
  have hz := congrArg (fun m : Matrix (Fin 4) (Fin 4) F => m 0 0) hm
  simp [cycleSL, Matrix.scalar, Matrix.PSL4.OddSplitTorus.torusFour,
    Matrix.mul_apply, Fin.sum_univ_succ] at hz
  exact (a 0).val.ne_zero hz.symm

/-- The literal three-cycle multiplies the torus order by three. -/
theorem card_cycle_join [Finite F] (U : Subgroup Fˣ) :
    Nat.card ↥(torus U ⊔ zpowers (cycle (F := F))) = Nat.card (torus U) * 3 := by
  have hcne : (cycle : PSL(4,F)) ≠ 1 := by
    intro h
    exact cycle_not_mem_torus U (h ▸ (torus U).one_mem)
  have hc : orderOf (cycle : PSL(4,F)) = 3 := orderOf_eq_prime cycle_cube hcne
  have hdis : Disjoint (torus U) (zpowers (cycle (F := F))) :=
    (torus U).disjoint_zpowers_of_prime_order_not_mem cycle hc (cycle_not_mem_torus U)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
    (zpowers_le.mpr (cycle_normalizes U)) hdis, Nat.card_zpowers, hc]

/-- Adjoining the actual cycle removes exactly one factor of three from the index. -/
theorem cycle_join_index [Finite F] (U : Subgroup Fˣ) :
    3 * (torus U ⊔ zpowers (cycle (F := F))).index = (torus U).index := by
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := torus U))
  rw [← mul_assoc, ← card_cycle_join U,
    (torus U ⊔ zpowers (cycle (F := F))).card_mul_index, (torus U).card_mul_index]

variable [Finite F]

/-- The scalar center is retained explicitly in the projective index formula. -/
theorem torus_index_mul_center {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p)
    (U : Subgroup Fˣ) (ho : Odd (Nat.card U)) :
    (torus U).index * Nat.gcd 4 (p-1) =
      U.index^3 * (p^6 * (p+1)^2 * (p^2+1) * (p^2+p+1)) := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hpos : 0 < p-1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  have hcard := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  simp only [hF, Fin.prod_univ_succ] at hcard
  norm_num at hcard
  have h41 : p^4-p = p*(p^3-1) := by rw [Nat.mul_sub]; ring_nf
  have h42 : p^4-p^2 = p^2*(p^2-1) := by rw [Nat.mul_sub]; ring_nf
  have h43 : p^4-p^3 = p^3*(p-1) := by rw [Nat.mul_sub]; ring_nf
  have h2 : p^2-1 = (p-1)*(p+1) := by
    apply Nat.sub_eq_of_eq_add
    nlinarith [Nat.sub_add_cancel hp]
  have h3 : p^3-1 = (p-1)*(p^2+p+1) := by
    apply Nat.sub_eq_of_eq_add
    set a := p-1
    have he : p = a+1 := (Nat.sub_add_cancel hp).symm
    change p^3 = a*(p^2+p+1)+1
    rw [he]
    ring
  have h4 : p^4-1 = (p-1)*(p+1)*(p^2+1) := by
    calc p^4-1 = (p^2)^2-1^2 := by ring_nf
         _ = (p^2-1)*(p^2+1) := by rw [Nat.sq_sub_sq]; ac_rfl
         _ = _ := by rw [h2]
  rw [h41,h42,h43,h2,h3,h4] at hcard
  have hpsl : Nat.card PSL(4,F) * Nat.gcd 4 (p-1) =
      (p-1)^3 * (p^6 * (p+1)^2 * (p^2+1) * (p^2+p+1)) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    calc
      _ = _ := hcard
      _ = _ := by ring
  have hU : Nat.card U * U.index = p-1 := by
    rw [U.card_mul_index, Nat.card_units, hF]
  apply Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.card_pos (α := U)) 3)
  calc
    _ = (Nat.card (torus U) * (torus U).index) * Nat.gcd 4 (p-1) := by
      rw [card_torus U ho]; ring
    _ = _ := by rw [(torus U).card_mul_index, hpsl, ← hU]; ring

theorem not_dvd_torus_index {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hF : Nat.card F = p) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hd : r ∣ p-1)
    (U : Sylow r Fˣ) (ho : Odd (Nat.card U)) : ¬ r ∣ (torus (U : Subgroup Fˣ)).index := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  have hq : (p : ZMod r) = 1 := by
    have hh := (CharP.cast_eq_zero_iff (ZMod r) r (p-1)).mpr hd
    rw [Nat.cast_sub hp, Nat.cast_one] at hh
    exact sub_eq_zero.mp hh
  have hpoly : ¬ r ∣ p^6 * (p+1)^2 * (p^2+1) * (p^2+p+1) := by
    intro hh
    have hz := (CharP.cast_eq_zero_iff (ZMod r) r _).mpr hh
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, hq, one_pow] at hz
    have h24 : r ∣ 2^3 * 3 := (CharP.cast_eq_zero_iff (ZMod r) r _).mp (by convert hz using 1; norm_num)
    rcases (Fact.out : r.Prime).dvd_mul.mp h24 with h | h
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_two).mp
        ((Fact.out : r.Prime).dvd_of_dvd_pow h))
    · exact hr3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : r.Prime) Nat.prime_three).mp h)
  intro hi
  have hh := dvd_mul_of_dvd_left hi (Nat.gcd 4 (p-1))
  rw [torus_index_mul_center hF _ ho] at hh
  exact ((Fact.out : r.Prime).not_dvd_mul
    (fun hh => U.not_dvd_index ((Fact.out : r.Prime).dvd_of_dvd_pow hh)) hpoly) hh

theorem nine_not_dvd_torus_index {p : ℕ} [Fact p.Prime]
    (hF : Nat.card F = p) (hd : 3 ∣ p-1)
    (U : Sylow 3 Fˣ) (ho : Odd (Nat.card U)) : ¬ 9 ∣ (torus (U : Subgroup Fˣ)).index := by
  have hq : p % 3 = 1 := by
    have hp := (Fact.out : p.Prime).two_le
    obtain ⟨k,hk⟩ := hd
    omega
  have hpoly : ¬ 9 ∣ p^6 * (p+1)^2 * (p^2+1) * (p^2+p+1) := by
    intro hh
    have hz := (CharP.cast_eq_zero_iff (ZMod 9) 9 _).mpr hh
    have hres : ∃ a : Fin 9, a.val % 3 = 1 ∧ (p : ZMod 9) = a := by
      refine ⟨⟨p % 9, Nat.mod_lt _ (by decide)⟩, ?_, ?_⟩
      · simpa [Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 9)] using hq
      · rfl
    obtain ⟨a,ha,hqa⟩ := hres
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, hqa] at hz
    have hcalc : ∀ a : Fin 9, a.val % 3 = 1 →
        (a : ZMod 9)^6 * (a+1)^2 * (a^2+1) * (a^2+a+1) ≠ 0 := by decide +kernel
    exact hcalc a ha hz
  have hc : Nat.Coprime 9 ((U : Subgroup Fˣ).index^3) :=
    ((Nat.prime_three.coprime_iff_not_dvd.mpr U.not_dvd_index).pow_left 2).pow_right 3
  intro hi
  have hh := dvd_mul_of_dvd_left hi (Nat.gcd 4 (p-1))
  rw [torus_index_mul_center hF _ ho] at hh
  exact hpoly (hc.dvd_mul_left.mp hh)

/-- The Sylow part of the split torus, with its cubic supplement, has index prime to r. -/
theorem not_dvd_cycle_join_index {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hF : Nat.card F = p) (hr2 : r ≠ 2) (hd : r ∣ p-1)
    (U : Sylow r Fˣ) (ho : Odd (Nat.card U)) :
    ¬ r ∣ (torus (U : Subgroup Fˣ) ⊔ zpowers (cycle (F := F))).index := by
  by_cases hr3 : r = 3
  · subst r
    intro hi
    apply nine_not_dvd_torus_index hF hd U ho
    rw [← cycle_join_index (U : Subgroup Fˣ)]
    exact Nat.mul_dvd_mul_left 3 hi
  · exact fun hi => not_dvd_torus_index hF hr2 hr3 hd U ho
      (hi.trans (index_dvd_of_le le_sup_left))

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining.LinearQuadratic.Split
namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining
open LinearQuadratic

/-- Every odd split-torus prime is absent from the kernel of every finite perfect
central cover of the literal PSL₄. The prime three is included. -/
public theorem linear_not_dvd_kernel_of_dvd_sub_one {F : Type*} [Field F] [Finite F]
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hF : Nat.card F = p)
    (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hrp : r ≠ p) (hminus : r ∣ p-1)
    {E : Type*} [Group E] [Finite E]
    (f : PerfectCentralCovering.Cover E PSL(4,F)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  -- Retain the common source interface; these two restrictions are not needed locally.
  have _ := hp2
  have _ := hrp
  let U : Sylow r Fˣ := default
  obtain ⟨k,hk⟩ := U.isPGroup'.exists_card_eq
  have ho : Odd (Nat.card U) := by
    rw [hk]
    exact ((Fact.out : r.Prime).odd_of_ne_two hr2).pow
  exact not_dvd_kernel_of_abelian_preimage_of_index f (U : Subgroup Fˣ) ho
    (Split.abelian_preimage _ ho f)
    (Split.not_dvd_cycle_join_index hF hr2 hminus U ho)

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining
