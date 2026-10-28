module

public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.Torus
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual
public import Mathlib.Data.Fintype.Perm
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.LinearAlgebra.Dimension.Constructions
/-!
# The natural SU₃(8) module has no Borel-invariant binary plane

Work with the genuine special unitary matrices over a field of order 64,
with Hermitian fixed field of order 8. A norm-one torus generator has order
nine. Its cube has no nonzero fixed vector in the three-dimensional matrix
module. An action of this generator on four vectors has cube equal to the
identity, since its permutation order divides both nine and 24.

Odd-order torus elements lie in the two-residual of every subgroup containing
the torus. The same obstruction holds for conjugate tori. This is stronger
than the binary-plane assertion and needs no choice of binary coordinates.
The natural module has dimension six over the fixed field and eighteen over
F₂. No action of the projective quotient on this natural module is asserted.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.8.20, printed p.955, paragraph beginning “We next observe”. Matrix
coordinates and unitary membership are supplied by Huppert II.10.12.
-/

public section
open Matrix BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.UnitaryEightSeed
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0,0,1; 0,1,0; 1,0,0])

private noncomputable def setAction (B : Subgroup J.specialSubgroup) (S : Set (Fin 3 → E))
    (hs : ∀ b : B, ∀ v ∈ S, b.val.val.val *ᵥ v ∈ S) : B →* Equiv.Perm S where
  toFun b :=
    { toFun := fun v => ⟨b.val.val.val *ᵥ v.val, hs b v.val v.property⟩
      invFun := fun v => ⟨b⁻¹.val.val.val *ᵥ v.val, hs b⁻¹ v.val v.property⟩
      left_inv := by
        intro v
        apply Subtype.ext
        change (b.val.val⁻¹).val *ᵥ (b.val.val.val *ᵥ v.val) = v.val
        rw [mulVec_mulVec, Units.inv_mul, one_mulVec]
      right_inv := by
        intro v
        apply Subtype.ext
        change b.val.val.val *ᵥ ((b.val.val⁻¹).val *ᵥ v.val) = v.val
        rw [mulVec_mulVec, Units.mul_inv, one_mulVec] }
  map_one' := by
    apply Equiv.ext
    intro v
    apply Subtype.ext
    exact one_mulVec v.val
  map_mul' a b := by
    apply Equiv.ext
    intro v
    apply Subtype.ext
    change (a.val.val.val * b.val.val.val) *ᵥ v.val =
      a.val.val.val *ᵥ (b.val.val.val *ᵥ v.val)
    exact (mulVec_mulVec v.val a.val.val.val b.val.val.val).symm

/-- The cube of an order-nine norm-one torus generator fixes only zero. -/
theorem torus_cube_fixed_eq_zero (k : EvenInner.normOne J)
    (hk : orderOf k = 9) (v : Fin 3 → E)
    (hv : (hermitianTorusSU J hJ k.val ^ 3).val.val *ᵥ v = v) : v = 0 := by
  have hk3 : (k.val : E)^3 ≠ 1 := by
    intro he
    have he' : k^3 = 1 := Subtype.ext (Units.ext he)
    have := hk ▸ orderOf_dvd_of_pow_eq_one he'
    norm_num at this
  have hk6 : (k.val : E)^6 ≠ 1 := by
    intro he
    have he' : k^6 = 1 := Subtype.ext (Units.ext he)
    have := hk ▸ orderOf_dvd_of_pow_eq_one he'
    norm_num at this
  rw [← map_pow] at hv
  have hc : J.conj (k.val : E) = (k.val : E)⁻¹ := k.property
  change hermitianTorusMatrix J (k.val ^ 3) *ᵥ v = v at hv
  have he0 : (k.val : E)^3 * v 0 = v 0 := by
    simpa [hermitianTorusMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hc]
      using congrFun hv 0
  have he1 : ((k.val : E)⁻¹ ^ 3 * (k.val : E)⁻¹ ^ 3) * v 1 = v 1 := by
    simpa [hermitianTorusMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hc]
      using congrFun hv 1
  have he2 : (k.val : E)^3 * v 2 = v 2 := by
    simpa [hermitianTorusMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
      using congrFun hv 2
  have hmid : (k.val : E)⁻¹ ^ 3 * (k.val : E)⁻¹ ^ 3 ≠ 1 := by
    rw [← pow_add, inv_pow]
    intro he
    exact hk6 (by simpa using congrArg (fun x : E => x⁻¹) he)
  funext i
  fin_cases i
  · exact by_contradiction fun hn => hk3 (mul_right_cancel₀ hn (he0.trans (one_mul _).symm))
  · exact by_contradiction fun hn => hmid (mul_right_cancel₀ hn (he1.trans (one_mul _).symm))
  · exact by_contradiction fun hn => hk3 (mul_right_cancel₀ hn (he2.trans (one_mul _).symm))

private theorem no_four_set_of_element [Finite E]
    (B : Subgroup J.specialSubgroup) (t : B) (ht9 : t^9 = 1)
    (hfix : ∀ v, (t.val^3).val.val *ᵥ v = v → v = 0)
    (S : Set (Fin 3 → E)) (hS : Nat.card S = 4)
    (hs : ∀ b : (pResidual 2 B).map B.subtype, ∀ v ∈ S,
      b.val.val.val *ᵥ v ∈ S) : False := by
  have htmem : t ∈ pResidual 2 B :=
    Subgroup.mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 9).of_dvd_right (orderOf_dvd_of_pow_eq_one ht9))
  let tr : (pResidual 2 B).map B.subtype := ⟨t.val, ⟨t, htmem, rfl⟩⟩
  let f := setAction J ((pResidual 2 B).map B.subtype) S hs
  have htr9 : tr^9 = 1 := Subtype.ext (congrArg B.subtype ht9)
  have hf9 : (f tr)^9 = 1 := by rw [← map_pow, htr9, map_one]
  have hf24 : orderOf (f tr) ∣ 24 := by
    have hd := orderOf_dvd_natCard (f tr)
    rwa [Nat.card_perm, hS] at hd
  have hf3 : (f tr)^3 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hf9) hf24
  have hz (v : S) : v.val = 0 := by
    apply hfix
    have hh := congrArg (fun p : Equiv.Perm S => (p v).val) hf3
    rw [← map_pow] at hh
    exact hh
  have : Subsingleton S := ⟨fun v w => Subtype.ext ((hz v).trans (hz w).symm)⟩
  have hc := Nat.card_le_card_of_injective (fun _ : S => ())
    (fun _ _ _ => Subsingleton.elim _ _)
  simp [hS] at hc
/-- The two-residual of a subgroup containing the standard torus preserves no four-element set. -/
theorem no_four_set [Finite E] (hcard : Nat.card E = 64)
    (hfixed : Nat.card {x : E // J.conj x = x} = 8)
    (B : Subgroup J.specialSubgroup)
    (htorus : (hermitianTorusSU J hJ).range ≤ B)
    (S : Set (Fin 3 → E)) (hS : Nat.card S = 4)
    (hs : ∀ b : (pResidual 2 B).map B.subtype, ∀ v ∈ S,
      b.val.val.val *ᵥ v ∈ S) : False := by
  have hnorm : Nat.card (EvenInner.normOne J) = 9 :=
    EvenInner.normOne_card J (q := 8) (by simpa using hcard)
      (huppert_II_10_4_conj_eq_frobenius J 8 (by simpa using hcard) hfixed)
  obtain ⟨k, hk⟩ := IsCyclic.exists_generator (α := EvenInner.normOne J)
  have horder : orderOf k = 9 := (orderOf_eq_card_of_forall_mem_zpowers hk).trans hnorm
  let t : B := ⟨hermitianTorusSU J hJ k.val, htorus ⟨k.val, rfl⟩⟩
  have ht9 : t^9 = 1 := by
    apply Subtype.ext
    change hermitianTorusSU J hJ k.val ^ 9 = 1
    rw [← map_pow]
    have hk9 : k.val ^ 9 = 1 := congrArg Subtype.val (horder ▸ pow_orderOf_eq_one k)
    rw [hk9, map_one]
  exact no_four_set_of_element J B t ht9
    (torus_cube_fixed_eq_zero J hJ k horder) S hS hs

/-- The same obstruction for every conjugate of the actual diagonal torus. -/
theorem no_four_set_conjugate_torus [Finite E] (hcard : Nat.card E = 64)
    (hfixed : Nat.card {x : E // J.conj x = x} = 8)
    (B : Subgroup J.specialSubgroup) (c : J.specialSubgroup)
    (htorus : (hermitianTorusSU J hJ).range.map (MulAut.conj c).toMonoidHom ≤ B)
    (S : Set (Fin 3 → E)) (hS : Nat.card S = 4)
    (hs : ∀ b : (pResidual 2 B).map B.subtype, ∀ v ∈ S,
      b.val.val.val *ᵥ v ∈ S) : False := by
  have hnorm : Nat.card (EvenInner.normOne J) = 9 :=
    EvenInner.normOne_card J (q := 8) (by simpa using hcard)
      (huppert_II_10_4_conj_eq_frobenius J 8 (by simpa using hcard) hfixed)
  obtain ⟨k, hk⟩ := IsCyclic.exists_generator (α := EvenInner.normOne J)
  have horder : orderOf k = 9 := (orderOf_eq_card_of_forall_mem_zpowers hk).trans hnorm
  let u := hermitianTorusSU J hJ k.val
  have hu9 : u^9 = 1 := by
    dsimp [u]
    rw [← map_pow]
    have hk9 : k.val ^ 9 = 1 := congrArg Subtype.val (horder ▸ pow_orderOf_eq_one k)
    rw [hk9, map_one]
  let t : B := ⟨MulAut.conj c u, htorus ⟨u, ⟨k.val, rfl⟩, rfl⟩⟩
  have ht9 : t^9 = 1 := by
    apply Subtype.ext
    change (MulAut.conj c u)^9 = 1
    rw [← map_pow, hu9, map_one]
  apply no_four_set_of_element J B t ht9 ?_ S hS hs
  intro v hv
  have he : t.val^3 = c * u^3 * c⁻¹ := by
    change (MulAut.conj c u)^3 = _
    rw [← map_pow]
    rfl
  rw [he] at hv
  have hh := congrArg (fun w => (c.val⁻¹).val *ᵥ w) hv
  have hw : (u^3).val.val *ᵥ ((c.val⁻¹).val *ᵥ v) = (c.val⁻¹).val *ᵥ v := by
    change (c.val⁻¹).val *ᵥ ((c.val * (u^3).val * c.val⁻¹).val *ᵥ v) = _ at hh
    rw [mulVec_mulVec] at hh
    have hm : (c.val⁻¹).val * (c.val * (u^3).val * c.val⁻¹).val =
        ((u^3).val * c.val⁻¹).val := by
      change (c.val⁻¹ * (c.val * (u^3).val * c.val⁻¹)).val = _
      congr 1
      group
    rw [hm, Units.val_mul, ← mulVec_mulVec] at hh
    exact hh
  have hz := torus_cube_fixed_eq_zero J hJ k horder _ hw
  have hh0 := congrArg (fun w => c.val.val *ᵥ w) hz
  simpa only [mulVec_mulVec, Units.mul_inv, one_mulVec, mulVec_zero] using hh0

/-- Restriction from F₆₄ to its Hermitian fixed field has dimension six. -/
theorem natural_fixed_finrank [Finite E] (hcard : Nat.card E = 64)
    (hfixed : Nat.card {x : E // J.conj x = x} = 8) :
    Module.finrank (FixedBy.subfield E J.conj) (Fin 3 → E) = 6 := by
  rw [Module.finrank_pi_fintype]
  simp [huppert_II_10_4_fixedField_finrank_two J 8 (by simpa using hcard) hfixed]

/-- Restriction of the natural matrix module to F₂ has dimension eighteen. -/
theorem natural_binary_finrank [Finite E] [Algebra (ZMod 2) E] (hcard : Nat.card E = 64) :
    Module.finrank (ZMod 2) (Fin 3 → E) = 18 := by
  have he : Module.finrank (ZMod 2) E = 6 := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E)
    rw [hcard, Nat.card_zmod] at hc
    exact (Nat.pow_right_injective (by decide : 1 < 2)) hc.symm
  rw [Module.finrank_pi_fintype]
  simp [he]

end BenderSuzuki.MatrixGroups.HermitianForm.UnitaryEightSeed
