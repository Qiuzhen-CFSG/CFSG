module

public import Theory.SpecificGroups.GL2.FiniteQuadraticTorus
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary.TorusCriterion
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Nonsplit product tori in even symplectic four-space

The norm-one subgroup of the actual quadratic extension has order q+1.
Its regular two-dimensional matrices have determinant one: that determinant
has order dividing both q+1 and q−1. The quadratic Frobenius reflection
also has determinant one, since it has order two and F's units have odd
order. It inverts the norm-one torus.

Embed two copies of SL₂(F) on the two orthogonal hyperbolic planes in the
repository's ordered-half matrix convention. The two norm-one factors
embed faithfully, and the first reflection inverts just the first factor.
For odd p dividing q+1, the product of the two cyclic Sylow p-subgroups
is Sylow in Sp₄(F), as verified from the actual subgroup index. Its
inverted-generator witness supplies the abelian full preimage needed
by central Sylow transfer. All constructions include q=4.

The block embedding extends the one-plane matrix calculation in
`Sylow.SolvableRootOrbit`. Source: the elementary torus argument for
Aschbacher–Smith I.1.2–I.1.3, printed p.407, citing GLS98 §6.1.
-/

open Matrix Subgroup
open scoped IsMulCommutative
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary
variable {F : Type*} [Field F]
local notation "SL" => SpecialLinearGroup (Fin 2) F

private def pairMatrix (A B : SL) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  fromBlocks !![A 0 0, 0; 0, B 0 0] !![A 0 1, 0; 0, B 0 1]
    !![A 1 0, 0; 0, B 1 0] !![A 1 1, 0; 0, B 1 1]

private theorem pairMatrix_mem (A B : SL) : pairMatrix A B ∈ Sp F := by
  have hA : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [det_fin_two] using A.property
  have hB : B 0 0 * B 1 1 - B 0 1 * B 1 0 = 1 := by
    simpa only [det_fin_two] using B.property
  rw [pairMatrix, SymplecticGroup.fromBlocks_mem_iff]
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, mul_comm, hA, hB]

private def pairHom : (SL × SL) →* Sp F where
  toFun A := ⟨pairMatrix A.1 A.2, pairMatrix_mem A.1 A.2⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pairMatrix]
  map_mul' A B := by
    apply Subtype.ext
    change pairMatrix (A.1 * B.1) (A.2 * B.2) = pairMatrix A.1 A.2 * pairMatrix B.1 B.2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pairMatrix, mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]

private theorem pairHom_injective : Function.Injective (pairHom (F := F)) := by
  intro A B h
  have he (x y : Fin 2 ⊕ Fin 2) := congrArg (fun g : Sp F => g.val x y) h
  apply Prod.ext
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact he (.inl 0) (.inl 0)
    · exact he (.inl 0) (.inr 0)
    · exact he (.inr 0) (.inl 0)
    · exact he (.inr 0) (.inr 0)
  · apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact he (.inl 1) (.inl 1)
    · exact he (.inl 1) (.inr 1)
    · exact he (.inr 1) (.inl 1)
    · exact he (.inr 1) (.inr 1)

variable [Finite F] [CharP F 2]

/-- The two actual norm-one factors, together with independent inversion. -/
public theorem exists_nonsplit_product :
    let C := rootsOfUnity (Nat.card F + 1) (FiniteField.Extension F 2 2)
    ∃ (ι : C × C →* Sp F) (w : Sp F),
      Nat.card C = Nat.card F + 1 ∧ Function.Injective ι ∧
      (∀ c : C, w * ι (c,1) * w⁻¹ = ι (c⁻¹,1)) ∧
      (∀ c : C, w * ι (1,c) * w⁻¹ = ι (1,c)) := by
  classical
  let : Fintype F := Fintype.ofFinite F
  let E := FiniteField.Extension F 2 2
  let C := rootsOfUnity (Nat.card F + 1) E
  have hcard : Nat.card C = Nat.card F + 1 := by
    dsimp [C]
    rw [rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker, Nat.card_units,
      FiniteField.natCard_extension]
    apply Nat.gcd_eq_right
    rw [show (Nat.card F)^2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) by
      simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1]
    exact dvd_mul_left _ _
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have heven : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.even_iff.mpr (FiniteField.even_card_of_char_two (ringChar.eq F 2))
  have hodd : Odd (Nat.card F - 1) := Nat.Even.sub_odd hq heven (by decide)
  have hcop : Nat.Coprime (Nat.card F + 1) (Nat.card F - 1) := by
    rw [show Nat.card F + 1 = (Nat.card F - 1) + 2 by omega,
      Nat.coprime_self_add_left]
    exact hodd.coprime_two_left
  obtain ⟨ρ, w, hi, hw, _, hconj, _⟩ := GeneralLinearGroup.exists_finite_quadratic_torus F 2
  let r : C →* GL (Fin 2) F := ρ.comp C.subtype
  have hd (c : C) : GeneralLinearGroup.det (r c) = 1 := by
    apply orderOf_eq_one_iff.mp
    have hd1 : orderOf (GeneralLinearGroup.det (r c)) ∣ Nat.card F + 1 := by
      rw [← hcard]
      exact (orderOf_map_dvd (GeneralLinearGroup.det.comp r) c).trans (orderOf_dvd_natCard c)
    have hd2 : orderOf (GeneralLinearGroup.det (r c)) ∣ Nat.card F - 1 := by
      simpa only [Nat.card_units] using orderOf_dvd_natCard (GeneralLinearGroup.det (r c))
    exact Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
  have hwd : GeneralLinearGroup.det w = 1 := by
    apply orderOf_eq_one_iff.mp
    have h2 : (GeneralLinearGroup.det w)^2 = 1 := by rw [← map_pow, hw, map_one]
    have hq : orderOf (GeneralLinearGroup.det w) ∣ Nat.card F - 1 := by
      simpa only [Nat.card_units] using orderOf_dvd_natCard (GeneralLinearGroup.det w)
    exact Nat.eq_one_of_dvd_coprimes hodd.coprime_two_left (orderOf_dvd_of_pow_eq_one h2) hq
  let s : C →* SL := {
    toFun c := ⟨(r c).val, congrArg Units.val (hd c)⟩
    map_one' := Subtype.ext (congrArg Units.val r.map_one)
    map_mul' c d := Subtype.ext (congrArg Units.val (r.map_mul c d)) }
  let v : SL := ⟨w.val, congrArg Units.val hwd⟩
  have hs : Function.Injective s := by
    intro c d h
    apply Subtype.ext
    exact hi (Units.ext (congrArg Subtype.val h))
  have hv (c : C) : v * s c * v⁻¹ = s c⁻¹ := by
    apply SpecialLinearGroup.toGL_injective
    have hvGL : SpecialLinearGroup.toGL v = w := Units.ext rfl
    have hsGL (d : C) : SpecialLinearGroup.toGL (s d) = r d := Units.ext rfl
    simp only [map_mul, map_inv, hvGL, hsGL]
    change w * ρ c.val * w⁻¹ = (ρ c.val)⁻¹
    rw [hconj, ← map_inv]
    apply congrArg ρ
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact (mem_rootsOfUnity _ _).mp c.property
  let ι := pairHom.comp (s.prodMap s)
  refine ⟨ι, pairHom (v,1), hcard, pairHom_injective.comp (Prod.map_injective.mpr ⟨hs, hs⟩), ?_, ?_⟩
  · intro c
    change pairHom (v,1) * pairHom (s c,s 1) * (pairHom (v,1))⁻¹ = pairHom (s c⁻¹,s 1)
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg pairHom
    apply Prod.ext
    · exact hv c
    · simp
  · intro c
    change pairHom (v,1) * pairHom (s 1,s c) * (pairHom (v,1))⁻¹ = pairHom (s 1,s c)
    rw [← map_inv, ← map_mul, ← map_mul]
    apply congrArg pairHom
    apply Prod.ext <;> simp


/-- For an odd divisor of q+1, the product torus contains a full Sylow subgroup
with two cyclic generators and the required ambient inverter. -/
public theorem exists_inverted_sylow_of_dvd_add_one
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hd : p ∣ Nat.card F + 1) :
    ∃ P : Sylow p (Sp F), Nonempty (PerfectCentralCovering.InvertedGenerators (P : Subgroup (Sp F))) := by
  classical
  let C := rootsOfUnity (Nat.card F + 1) (FiniteField.Extension F 2 2)
  obtain ⟨ι, w, hc, hι, hinv, hfix⟩ := exists_nonsplit_product (F := F)
  have hp : p.Prime := Fact.out
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hf2 : (Nat.card F)^2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq (Nat.card F) 1
  have hf4 : (Nat.card F)^4 - 1 = ((Nat.card F)^2 - 1) * ((Nat.card F)^2 + 1) := by
    have h := Nat.sq_sub_sq ((Nat.card F)^2) 1
    simpa only [show ((Nat.card F)^2)^2 = (Nat.card F)^4 by ring,
      one_pow, mul_comm] using h
  have hcardT : Nat.card ι.range = (Nat.card F + 1)^2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, Nat.card_prod, hc, pow_two]
  have hi : ι.range.index = (Nat.card F)^4 * (Nat.card F - 1)^2 * ((Nat.card F)^2 + 1) := by
    apply Nat.eq_of_mul_eq_mul_left (pow_pos (Nat.succ_pos (Nat.card F)) 2)
    rw [← hcardT, Subgroup.card_mul_index, card_sp, hf4, hf2, hcardT]
    ring
  have hnot2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left hp.ne_one)
  have hnotq : ¬ p ∣ Nat.card F := by
    intro h
    have hh := Nat.dvd_sub hd h
    rw [Nat.add_sub_cancel_left] at hh
    exact hp.not_dvd_one hh
  have hnotminus : ¬ p ∣ Nat.card F - 1 := by
    intro h
    have hh := Nat.dvd_sub hd h
    rw [show Nat.card F + 1 - (Nat.card F - 1) = 2 by omega] at hh
    exact hnot2 hh
  have hnotquad : ¬ p ∣ (Nat.card F)^2 + 1 := by
    intro h
    have hd' : p ∣ (Nat.card F)^2 - 1 := by rw [hf2]; exact dvd_mul_of_dvd_right hd _
    have hh := Nat.dvd_sub h hd'
    rw [show (Nat.card F)^2 + 1 - ((Nat.card F)^2 - 1) = 2 by
      have : 1 ≤ (Nat.card F)^2 := Nat.one_le_pow _ _ hq
      omega] at hh
    exact hnot2 hh
  have hpindex : ¬ p ∣ ι.range.index := by
    rw [hi]
    exact hp.not_dvd_mul
      (hp.not_dvd_mul (fun h => hnotq (hp.dvd_of_dvd_pow h))
        (fun h => hnotminus (hp.dvd_of_dvd_pow h))) hnotquad
  let R : Sylow p C := default
  let D : Subgroup (C × C) := (R : Subgroup C).prod (R : Subgroup C)
  have hDp : IsPGroup p D := by
    obtain ⟨m, hm⟩ := R.isPGroup'.exists_card_eq
    apply IsPGroup.of_card (n := m+m)
    rw [Nat.card_congr (Subgroup.prodEquiv (R : Subgroup C) (R : Subgroup C)).toEquiv,
      Nat.card_prod, hm, pow_add]
  let Q : Subgroup (Sp F) := D.map ι
  have hQp : IsPGroup p Q := hDp.map ι
  have hQi : ¬ p ∣ Q.index := by
    rw [Subgroup.index_map_of_injective _ hι, Subgroup.index_prod]
    exact hp.not_dvd_mul (hp.not_dvd_mul R.not_dvd_index R.not_dvd_index) hpindex
  let P : Sylow p (Sp F) := hQp.toSylow hQi
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := R)
  have hx : ι ((a : C),1) ∈ Q := ⟨((a : C),1), ⟨a.property, (R : Subgroup C).one_mem⟩, rfl⟩
  have hy : ι (1,(a : C)) ∈ Q := ⟨(1,(a : C)), ⟨(R : Subgroup C).one_mem, a.property⟩, rfl⟩
  refine ⟨P, ⟨{
    left := ⟨ι ((a : C),1), hx⟩
    right := ⟨ι (1,(a : C)), hy⟩
    commute := (Commute.all ((a : C),1) (1,(a : C))).map ι
    normalForm := ?_
    inverter := w
    invert_left := (hinv a).trans (by
      simpa only [Prod.inv_mk, inv_one] using ι.map_inv ((a : C),1))
    fix_right := hfix a }⟩⟩
  intro z
  obtain ⟨⟨c,d⟩, hcd, he⟩ := z.property
  change c ∈ (R : Subgroup C) ∧ d ∈ (R : Subgroup C) at hcd
  obtain ⟨i, hi⟩ := ha ⟨c, hcd.1⟩
  obtain ⟨j, hj⟩ := ha ⟨d, hcd.2⟩
  refine ⟨i, j, ?_⟩
  change (z : Sp F) = ι ((a : C),1)^i * ι (1,(a : C))^j
  rw [← he, ← map_zpow, ← map_zpow, ← map_mul]
  apply congrArg ι
  apply Prod.ext
  · simpa using (congrArg (fun x : R => (x : C)) hi).symm
  · simpa using (congrArg (fun x : R => (x : C)) hj).symm

/-- Nonsplit rank-two torus primes do not divide any perfect central kernel. -/
public theorem not_dvd_card_kernel_of_dvd_add_one
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hd : p ∣ Nat.card F + 1)
    (f : E →* Sp F) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ¬ p ∣ Nat.card f.ker := by
  obtain ⟨P, ⟨hP⟩⟩ := exists_inverted_sylow_of_dvd_add_one hp2 hd
  exact PerfectCentralCovering.not_dvd_card_kernel_of_inverted_sylow hp2 P hP f hf hk

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrimary
