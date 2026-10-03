module

public import Theory.SpecificGroups.MacWilliams.UnitaryQuadraticCoordinates
public import Mathlib.Data.BitVec

/-!
# Packed coordinates for the unitary quadratic certificate

Two-bit digits encode the ten coefficients of a quadratic map. Four-bit and
two-bit vectors encode the source and target. The decoding maps are bijective;
in particular the finite fibre counts retain their mathematical meaning.

This supports the finite normal form used in MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace MacWilliamsSylow.QuadraticCertificate

@[expose] public def central (n : Fin 4) : BinaryCoordinates 2 :=
  Multiplicative.ofAdd fun i => if (BitVec.ofFin n).getLsb i then 1 else 0

@[expose] public def vector (n : Fin 16) : BinaryCoordinates 4 :=
  Multiplicative.ofAdd fun i => if (BitVec.ofFin n).getLsb i then 1 else 0

public theorem central_bijective : Function.Bijective central := by decide +kernel
public theorem vector_bijective : Function.Bijective vector := by decide +kernel

@[simp] public theorem central_zero : central 0 = 1 := by decide +kernel
@[simp] public theorem vector_zero : vector 0 = 1 := by decide +kernel

@[expose] public def digit (n : Fin 1048576) (i : Fin 10) : Fin 4 :=
  ⟨n.val / 4 ^ i.val % 4, Nat.mod_lt _ (by decide)⟩

@[expose] public def coefficients (n : Fin 1048576) : QuadraticCoefficients :=
  fun i => central (digit n i)

@[expose] public def pack (d : Fin 10 → Fin 4) : Fin 1048576 :=
  ⟨∑ i : Fin 10, (d i).val * 4^i.val, by
    calc
      ∑ i : Fin 10, (d i).val * 4^i.val ≤ ∑ i : Fin 10, 3 * 4^i.val := by
        gcongr with i
        omega
      _ < 1048576 := by norm_num [Fin.sum_univ_succ]⟩

public theorem digit_pack (d : Fin 10 → Fin 4) (i : Fin 10) :
    digit (pack d) i = d i := by
  have h0 := (d 0).isLt
  have h1 := (d 1).isLt
  have h2 := (d 2).isLt
  have h3 := (d 3).isLt
  have h4 := (d 4).isLt
  have h5 := (d 5).isLt
  have h6 := (d 6).isLt
  have h7 := (d 7).isLt
  have h8 := (d 8).isLt
  have h9 := (d 9).isLt
  apply Fin.ext
  fin_cases i <;> norm_num [digit, pack, Fin.sum_univ_succ, Fin.succ,
    Fin.reduceFinMk] <;> simp only [Fin.reduceFinMk] <;> omega

public theorem coefficients_surjective : Function.Surjective coefficients := by
  intro c
  choose d hd using fun i => central_bijective.2 (c i)
  refine ⟨pack d, ?_⟩
  funext i
  simp only [coefficients, digit_pack, hd]

end MacWilliamsSylow.QuadraticCertificate
