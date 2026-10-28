module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Words
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientOrder.Packed

/-!
# Arithmetic and subgroup bridges for the obstruction certificates

Matrix entries distinguish actual elements of the certified quotient subgroup.
Packed multiplication certifies products and inverses. A nonidentity element
whose order divides a number coprime to 2304 has nonidentity 2304th power.
The line criterion uses the inverse right action from Geometry.lean.

This is the finite calculation used in the J₄ case of Aschbacher–Smith,
Proposition 1.3.4, printed p.511/PDF p.528, citing Aschbacher (1986).
-/

@[expose] public section
open Subgroup
open scoped Pointwise
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound LowerBound.QuotientOrderCertificate

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate

def value : quotientSubgroup →* QuotientMatrix :=
  (Units.coeHom QuotientMatrix).comp quotientSubgroup.subtype

theorem value_injective : Function.Injective value := by
  intro x y h
  exact Subtype.ext (Units.ext h)

theorem eq_one_of_value (g : quotientSubgroup) (h : value g = 1) : g = 1 :=
  value_injective (h.trans (map_one value).symm)

theorem coprime_power_obstruction (g : quotientSubgroup) (p : ℕ)
    (hp : p.Coprime 2304) (hpow : g ^ p = 1) (hne : g ≠ 1) :
    g ^ 2304 ≠ 1 := by
  intro h
  apply hne
  apply orderOf_eq_one_iff.mp
  apply Nat.dvd_one.mp
  have hd := Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hpow)
    (orderOf_dvd_iff_pow_eq_one.mpr h)
  simpa only [hp.gcd_eq_one] using hd

theorem secondGenerator_mem (i : Fin 3) :
    involutionMatrixSecondGenerator i ∈ involutionMatrixSecondSubgroup :=
  Subgroup.subset_closure ⟨i, rfl⟩

theorem sylow_mem_join (j : Fin 110) (i : Fin 4) :
    sylowGenerator i ∈ baseSubgroup ⊔ Subgroup.zpowers (representative j) :=
  (le_sup_left : baseSubgroup ≤ baseSubgroup ⊔ Subgroup.zpowers (representative j))
    (sylowGenerator_mem i)

theorem representative_mem_join (j : Fin 110) :
    representative j ∈ baseSubgroup ⊔ Subgroup.zpowers (representative j) :=
  (le_sup_right : Subgroup.zpowers (representative j) ≤
    baseSubgroup ⊔ Subgroup.zpowers (representative j)) (Subgroup.mem_zpowers (representative j))

def identityRows : Vector ℕ 12 := #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

theorem decode_identity : quotientDecode identityRows = 1 := by decide +kernel

theorem inverse_value (g : quotientSubgroup) (xs ys : Vector ℕ 12)
    (hg : value g = quotientDecode xs)
    (h : ∀ i : Fin 12, packedRow (xs.get i) ys = identityRows.get i) :
    value g⁻¹ = quotientDecode ys := by
  apply left_inv_eq_right_inv (show value g⁻¹ * value g = 1 from
    (map_mul value g⁻¹ g).symm.trans (by rw [inv_mul_cancel, map_one]))
  rw [hg, mul_eq_of_packed xs ys identityRows h, decode_identity]

theorem power_step (g : quotientSubgroup) (m n : ℕ) (xs ys zs : Vector ℕ 12)
    (hm : value (g ^ m) = quotientDecode xs)
    (hn : value (g ^ n) = quotientDecode ys)
    (h : ∀ i : Fin 12, packedRow (xs.get i) ys = zs.get i) :
    value (g ^ (m + n)) = quotientDecode zs := by
  rw [pow_add, map_mul, hm, hn]
  exact mul_eq_of_packed xs ys zs h

theorem ne_one_of_value (g : quotientSubgroup) (xs : Vector ℕ 12)
    (hg : value g = quotientDecode xs)
    (h : quotientDecode xs ≠ 1) : g ≠ 1 := by
  intro heq
  apply h
  rw [← hg, heq, map_one]

theorem line_mem_of_inverse (g : quotientSubgroup) (ys : Vector ℕ 12)
    (a b c : BitVec 12)
    (hg : value g⁻¹ = quotientDecode ys)
    (h23 : packedRow 23 ys = a.toNat)
    (h1024 : packedRow 1024 ys = b.toNat)
    (h1047 : packedRow 1047 ys = c.toNat)
    (hset : {involutionMatrixVector a.toNat, involutionMatrixVector b.toNat,
      involutionMatrixVector c.toNat} = involutionMatrixLine) :
    g ∈ involutionMatrixLineStabilizer := by
  change OuterImageComparison.rowAction (g : U) • involutionMatrixLine = involutionMatrixLine
  have hv (a b : BitVec 12) (hab : packedRow a.toNat ys = b.toNat) :
      OuterImageComparison.rowAction (g : U) (involutionMatrixVector a.toNat) =
        involutionMatrixVector b.toNat := by
    change Matrix.vecMul (row a) (value g⁻¹) = row b
    rw [hg]
    exact vecMul_eq_of_packed a b ys hab
  rw [involutionMatrixLine, Set.smul_set_insert, Set.smul_set_insert, Set.smul_set_singleton]
  change {OuterImageComparison.rowAction (g : U) (involutionMatrixVector 23),
    OuterImageComparison.rowAction (g : U) (involutionMatrixVector 1024),
    OuterImageComparison.rowAction (g : U) (involutionMatrixVector 1047)} = _
  have h₁ := hv 23 a h23
  have h₂ := hv 1024 b h1024
  have h₃ := hv 1047 c h1047
  change OuterImageComparison.rowAction (g : U) (involutionMatrixVector 23) = _ at h₁
  change OuterImageComparison.rowAction (g : U) (involutionMatrixVector 1024) = _ at h₂
  change OuterImageComparison.rowAction (g : U) (involutionMatrixVector 1047) = _ at h₃
  rw [h₁, h₂, h₃]
  exact hset

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate
