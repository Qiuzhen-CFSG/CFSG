module

public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.SmallPrimes.Certificates
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.LargePrimes.Orbit

/-!
# Involution pairs in the small-prime centralizers of J₁

The complete matrix family of involutions is reused from `LargePrimes.Orbit`.
The new finite checks place involutions centralizing `b` in a five-entry list,
and those centralizing `x * y` in a three-entry list. Distinct entries of either
list do not commute, so neither centralizer contains a four-group.

This is the precise local input needed by `SmallPrimes.Reduction` for the
small-prime normalizer bounds of GLS3 Table 5.3f, as used on Aschbacher–Smith,
*The Classification of Quasithin Groups*, printed p.510. All identities use
the actual ATLAS matrix model; see `Source/README.md` for provenance.
-/

namespace Janko1.LocalStructure.SmallPrimes
open OrderCertificate LargePrimes.Packed Certificate

private theorem three_mem (t : Model) (ht : orderOf t = 2) (hc : Commute t b) :
    ∃ j : Fin 5, matrixValue t = decode (code (indices3 j)) := by
  obtain ⟨i, hi⟩ := LargePrimes.involution_mem_family t ht
  have he := (hc.map matrixValue).eq
  change matrixValue t * matrixB = matrixB * matrixValue t at he
  rw [hi, ← decode_generatorB] at he
  obtain ⟨j, rfl⟩ := (allowed3_iff i).mp ((covered i).1 (check_complete _ _ _ _ he))
  exact ⟨j, hi⟩

private theorem five_mem (t : Model) (ht : orderOf t = 2) (hc : Commute t (x * y)) :
    ∃ j : Fin 3, matrixValue t = decode (code (indices5 j)) := by
  obtain ⟨i, hi⟩ := LargePrimes.involution_mem_family t ht
  have he := (hc.map matrixValue).eq
  rw [hi, ← decode_r5] at he
  obtain ⟨j, rfl⟩ := (allowed5_iff i).mp ((covered i).2 (check_complete _ _ _ _ he))
  exact ⟨j, hi⟩

private theorem eq_of_list {n : ℕ} (indices : Fin n → Fin 1463)
    (hpairs : ∀ i j : Fin n, i ≠ j →
      check (code (indices i)) (code (indices j))
        (code (indices j)) (code (indices i)) = false)
    (s t : Model)
    (hs : ∃ i, matrixValue s = decode (code (indices i)))
    (ht : ∃ i, matrixValue t = decode (code (indices i)))
    (hst : Commute s t) : s = t := by
  obtain ⟨i, hi⟩ := hs
  obtain ⟨j, hj⟩ := ht
  have he := (hst.map matrixValue).eq
  rw [hi, hj] at he
  have hij : i = j := by
    by_contra hn
    exact check_false _ _ (hpairs i j hn) he
  apply matrixValue_injective
  rw [hi, hj, hij]

/-- Two commuting involutions centralizing the order-three representative coincide. -/
public theorem involution_pair_three (s t : Model) (hs : orderOf s = 2) (ht : orderOf t = 2)
    (hsb : Commute s b) (htb : Commute t b) (hst : Commute s t) : s = t :=
  eq_of_list indices3 pairs3 s t (three_mem s hs hsb) (three_mem t ht htb) hst

/-- Two commuting involutions centralizing the order-five representative coincide. -/
public theorem involution_pair_five (s t : Model) (hs : orderOf s = 2) (ht : orderOf t = 2)
    (hsr : Commute s (x * y)) (htr : Commute t (x * y)) (hst : Commute s t) : s = t :=
  eq_of_list indices5 pairs5 s t (five_mem s hs hsr) (five_mem t ht htr) hst

end Janko1.LocalStructure.SmallPrimes
