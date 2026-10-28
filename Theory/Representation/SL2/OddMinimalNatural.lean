module
public import Theory.Representation.SL2.PrimeFieldParameters.Unsigned
public import Theory.Representation.SL2.BinaryNaturalTripleRecognition
public import Theory.Representation.IrreducibleFixedPoints
public import Theory.SpecificGroups.SL2.CubicFixedVectors
public import Theory.Representation.SubspaceQuotient

/-!
# Minimum binary degree over an odd-degree defining field

An irreducible binary SL₂(2ᵐ)-module of dimension 2m, with m odd,
is the actual natural module. The highest-weight period divides m,
so its repetition count is odd. Equality in the degree bound forces
one block, Schur degree m, and a single nonzero binary digit.
The existing pure-weight descent then constructs an intertwining
isomorphism for the original matrix group and defining field.

This identifies the two hypothetical constituents of C/W in DGS85,
Groups and Graphs, proof of (12.9), pp.189--190. That application has
m = 2n+1. No natural-action recognition hypothesis is added. The odd-degree orbit
bounds also show that an irreducible module with order between q³ and q⁴
has order exactly q⁴, supplying the subsequent exact core orders.
-/

public noncomputable section
open scoped MatrixGroups MonoidAlgebra TensorProduct
namespace Representation.SL2

private theorem binary_endField_finrank_eq_of_minimal
    {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,K) V) [ρ.IsIrreducible]
    (hρ : ∃ g, ρ g ≠ 1) {m : ℕ} (hm : Odd m) (hcard : Nat.card K = 2 ^ m)
    (hdim : Module.finrank (ZMod 2) V = 2*m) :
    Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule) = m := by
  let s := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule)
  obtain ⟨hs,n,hn,hsdiv,hperiod,hd⟩ :=
    Unsigned.exists_primeField_highestWeight_parameters 2 ρ hρ m hcard
  obtain ⟨t,hmt⟩ := hsdiv
  have ht : Odd t := Odd.of_dvd_nat hm ⟨s,by simpa [mul_comm] using hmt⟩
  have htpos : 0 < t := ht.pos
  obtain ⟨b,hb,hprod,_⟩ := Nat.exists_digit_product_pow_of_period 2 s t n.val
    (by decide) hs htpos hn (by rw [←hmt,←hcard]; exact n.isLt)
    (by rw [←hmt,←hcard]; exact hperiod)
  have heq : s*b^t = 2*(s*t) := by
    rw [hdim,hmt,hprod] at hd
    exact hd.symm
  have htone := (orbit_dimension_minimal_parameters hs ht hb heq).1
  simpa only [htone,mul_one] using hmt.symm

private def digitProd (m n : ℕ) : ℕ := ∏ i : Fin m, (n / 2 ^ (i : ℕ) % 2 + 1)
private theorem digitProd_succ (m n : ℕ) :
    digitProd (m+1) n = (n%2+1)*digitProd m (n/2) := by
  rw [digitProd,Fin.prod_univ_succ]
  simp only [Fin.val_zero,pow_zero,Nat.div_one]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fin.val_succ,pow_succ,Nat.div_div_eq_div_mul,mul_comm]
private theorem eq_zero_of_prod_one (m n : ℕ) (hn : n < 2^m)
    (h : digitProd m n = 1) : n=0 := by
  induction m generalizing n with
  | zero => simpa using hn
  | succ m ih =>
    rw [digitProd_succ] at h
    have hp : 0 < digitProd m (n/2) := Finset.prod_pos (fun _ _ => Nat.zero_lt_succ _)
    have hle := Nat.le_mul_of_pos_left (digitProd m (n/2)) (Nat.zero_lt_succ (n%2))
    rw [h] at hle
    have hq : digitProd m (n/2)=1 := by omega
    have hr : n%2=0 := by rw [hq] at h; omega
    have hn' : n/2 < 2^m := Nat.div_lt_of_lt_mul (by simpa [pow_succ,mul_comm] using hn)
    have hz := ih (n/2) hn' hq
    omega
private theorem pow_of_prod_two (m n : ℕ) (hn : n < 2^m)
    (h : digitProd m n = 2) : ∃ j<m, n=2^j := by
  induction m generalizing n with
  | zero => simp [digitProd] at h
  | succ m ih =>
    rw [digitProd_succ] at h
    have hn' : n/2 < 2^m := Nat.div_lt_of_lt_mul (by simpa [pow_succ,mul_comm] using hn)
    by_cases hr : n%2=0
    · have hq : digitProd m (n/2)=2 := by simpa [hr] using h
      obtain ⟨j,hj,he⟩ := ih (n/2) hn' hq
      refine ⟨j+1,by omega,?_⟩
      rw [pow_succ]
      omega
    · have hr1 : n%2=1 := by omega
      have hq : digitProd m (n/2)=1 := by rw [hr1] at h; omega
      have hz := eq_zero_of_prod_one m (n/2) hn' hq
      exact ⟨0,by omega,by simp; omega⟩

/-- Minimum-degree irreducible binary modules over an odd-degree field have literal natural coordinates. -/
theorem isNatural_of_minimal_odd_binary_degree
    {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,K) V) [ρ.IsIrreducible]
    {m : ℕ} (hm : Odd m) (hm2 : 2 ≤ m)
    (hcard : Nat.card K = 2^m) (hdim : Module.finrank (ZMod 2) V = 2*m) :
    BinarySmall.IsNatural ρ := by
  have hρ : ∃ g, ρ g ≠ 1 := by
    by_contra! hh
    have hfixed := OneCohomology.fixed_eq_bot_of_irreducible_finrank ρ (by omega)
    let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
    obtain ⟨v,hv⟩ := exists_ne (0 : V)
    apply hv
    apply hfixed.le
    intro g
    rw [hh g]
    rfl
  have hs := binary_endField_finrank_eq_of_minimal ρ hρ hm hcard hdim
  let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
  let F := AlgebraicClosure E
  let : CharP E 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap (algebraMap E F).injective 2
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Finite ρ.asModule := Module.finite_iff_finite.mp
    (inferInstance : Module.Finite (ZMod 2) ρ.asModule)
  let : Module.Finite E ρ.asModule := Module.Finite.of_finite
  let : IsAbsolutelyIrreducible ρ.endFieldRep := endFieldRep_isAbsolutelyIrreducible ρ
  let : IsIrreducible (extendScalars F ρ.endFieldRep) :=
    IsAbsolutelyIrreducible.irreducible_of_extension ρ.endFieldRep F
  let e : K →+* F := (IsAlgClosed.lift (R := ZMod 2) (S := K) (M := F)).toRingHom
  obtain ⟨n,⟨φ⟩⟩ := exists_highestWeightSpan_equiv e 2 (extendScalars F ρ.endFieldRep)
  have hE : Module.finrank E ρ.asModule = 2 := by
    have hh := Module.finrank_mul_finrank (ZMod 2) E ρ.asModule
    rw [ρ.asModuleEquiv.finrank_eq,hdim] at hh
    change Module.finrank (ZMod 2) E * _ = _ at hh
    rw [hs] at hh
    nlinarith
  have hd : digitProd m n.val = 2 := by
    change (∏ i : Fin m, (n.val / 2^(i:ℕ)%2+1)) = 2
    rw [←highestWeightSpan_finrank_eq_prod_digits e 2 Nat.prime_two n.val m hcard
      (by simpa only [←hcard] using n.isLt),←φ.toLinearEquiv.finrank_eq,
      Module.finrank_baseChange,hE]
  obtain ⟨j,hjm,hj⟩ := pow_of_prod_two m n.val (by simpa only [←hcard] using n.isLt) hd
  apply BinarySmall.isNatural_of_highestWeight_pow_two ρ m hm2 hcard hs j hjm e
  rw [←hj]
  exact ⟨φ⟩

/-- In an odd-degree field, two minimum-degree irreducible factors are natural
and each cubic actor is fixed-point-free on the extension. -/
theorem natural_factors_and_cubic_fixed_of_card
    {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) SL(2,K) V) (U : Subrepresentation ρ)
    [U.toRepresentation.IsIrreducible] [U.quotientRepresentation.IsIrreducible]
    {m : ℕ} (hm : Odd m) (hm2 : 2 ≤ m) (hcard : Nat.card K = 2^m)
    (hu : Nat.card U.toSubmodule = Nat.card K ^ (2 : ℕ))
    (hq : Nat.card (V ⧸ U.toSubmodule) = Nat.card K ^ (2 : ℕ)) :
    BinarySmall.IsNatural U.toRepresentation ∧
      BinarySmall.IsNatural U.quotientRepresentation ∧
      ∀ g : SL(2,K), orderOf g = 3 → ∀ v, ρ g v = v → v = 0 := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hdu : Module.finrank (ZMod 2) U.toSubmodule = 2*m := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hcard,←pow_mul] at hu
    exact (Nat.pow_right_injective (by decide : 1 < 2) hu).trans (Nat.mul_comm _ _)
  have hdq : Module.finrank (ZMod 2) (V ⧸ U.toSubmodule) = 2*m := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hcard,←pow_mul] at hq
    exact (Nat.pow_right_injective (by decide : 1 < 2) hq).trans (Nat.mul_comm _ _)
  have hNU := isNatural_of_minimal_odd_binary_degree U.toRepresentation hm hm2 hcard hdu
  have hNQ := isNatural_of_minimal_odd_binary_degree U.quotientRepresentation hm hm2 hcard hdq
  refine ⟨hNU,hNQ,?_⟩
  intro g hg v hv
  obtain ⟨eu⟩ := hNU
  obtain ⟨eq⟩ := hNQ
  have hqzero : U.toSubmodule.mkQ v = 0 := by
    apply eq.injective
    rw [map_zero]
    apply Matrix.SL2.cubic_fixed_eq_zero g hg
    have he := LinearMap.congr_fun (eq.isIntertwining' g) (U.toSubmodule.mkQ v)
    change eq (U.quotientRepresentation g (U.toSubmodule.mkQ v)) =
      BinarySmall.natural g (eq (U.toSubmodule.mkQ v)) at he
    rw [Subrepresentation.quotientRepresentation_mk,hv] at he
    exact he.symm
  have hvm : v ∈ U.toSubmodule := (Submodule.Quotient.mk_eq_zero _).mp hqzero
  have huzero : (⟨v,hvm⟩ : U.toSubmodule) = 0 := by
    apply eu.injective
    rw [map_zero]
    apply Matrix.SL2.cubic_fixed_eq_zero g hg
    have he := LinearMap.congr_fun (eu.isIntertwining' g) (⟨v,hvm⟩ : U.toSubmodule)
    have heu : U.toRepresentation g ⟨v,hvm⟩ = ⟨v,hvm⟩ := Subtype.ext hv
    change eu (U.toRepresentation g ⟨v,hvm⟩) = BinarySmall.natural g (eu ⟨v,hvm⟩) at he
    rw [heu] at he
    exact he.symm
  exact congrArg Subtype.val huzero

private theorem digitProd_one_or_even (m n : ℕ) :
    digitProd m n = 1 ∨ Even (digitProd m n) := by
  induction m generalizing n with
  | zero => left; simp [digitProd]
  | succ m ih =>
    rw [digitProd_succ]
    by_cases hr : n%2 = 0
    · simpa [hr] using ih (n/2)
    · have hr1 : n%2 = 1 := by omega
      rw [hr1]
      right
      exact even_two.mul_right _

/-- An irreducible odd-degree binary SL₂ module between q³ and q⁴ has order q⁴. -/
theorem card_eq_four_of_odd_irreducible_bounds
    {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) SL(2,K) V) [ρ.IsIrreducible]
    {m : ℕ} (hm : Odd m) (hm2 : 2 ≤ m) (hcard : Nat.card K = 2^m)
    (hlo : Nat.card K ^ (3 : ℕ) ≤ Nat.card V)
    (hup : Nat.card V ≤ Nat.card K ^ (4 : ℕ)) :
    Nat.card V = Nat.card K ^ (4 : ℕ) := by
  have hdlo : 3*m ≤ Module.finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),Nat.card_zmod,hcard,←pow_mul] at hlo
    have hh := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hlo
    omega
  have hdup : Module.finrank (ZMod 2) V ≤ 4*m := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),Nat.card_zmod,hcard,←pow_mul] at hup
    have hh := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hup
    omega
  have hρ : ∃ g, ρ g ≠ 1 := by
    by_contra! hh
    have hfixed := OneCohomology.fixed_eq_bot_of_irreducible_finrank ρ (by omega)
    let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
    obtain ⟨v,hv⟩ := exists_ne (0 : V)
    apply hv
    apply hfixed.le
    intro g
    rw [hh g]
    rfl
  let s := Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule)
  obtain ⟨hs,n,hn,hsdiv,hperiod,hd⟩ :=
    Unsigned.exists_primeField_highestWeight_parameters 2 ρ hρ m hcard
  obtain ⟨t,hmt⟩ := hsdiv
  have ht : Odd t := Odd.of_dvd_nat hm ⟨s,by simpa [mul_comm] using hmt⟩
  obtain ⟨b,hb,hprod,_⟩ := Nat.exists_digit_product_pow_of_period 2 s t n.val
    (by decide) hs ht.pos hn (by rw [←hmt,←hcard]; exact n.isLt)
    (by rw [←hmt,←hcard]; exact hperiod)
  have hbEven : Even b := by
    have he : Even (b^t) := by
      rcases digitProd_one_or_even (s*t) n.val with he | he
      · have hh : b^t=1 := hprod.symm.trans he
        have hgt := Nat.one_lt_pow ht.pos.ne' (by omega : 1 < b)
        omega
      · exact hprod ▸ he
    exact (Nat.even_pow.mp he).1
  have hd' : Module.finrank (ZMod 2) V = s*b^t := by
    rw [hd,hmt,hprod]
  have hdfour : Module.finrank (ZMod 2) V = 4*m := by
    have htri := orbit_dimension_trichotomy (s := s) ht hb hbEven
    rw [←hmt,←hd'] at htri
    rcases htri with htwo | ⟨hthree,_⟩ | hfour <;> omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),Nat.card_zmod,hdfour,hcard,←pow_mul]
  congr 1
  omega

end Representation.SL2
