module

public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.CentralRootSquare.Coordinates

/-!
# A nonidentity square in the central triality radical

The second and third short-root elements at parameter one lie in both root
radicals. The checked arms multiplication formula makes their product square
to the highest-root element at parameter one, which survives the genuine
central quotient. Thus the central radical is not elementary, including at
q = 2. For q > 2 its commutator with the actual central Levi is the whole
radical, so a subgroup satisfying the square hypothesis cannot contain that
Levi. This does not settle arbitrary subnormal actors or the binary C₃ case.

Source: the trace commutator formulas of GLS3 §2.4
(`refs/KGroup/GLS3/chapter2.tex`); central local structure in
Aschbacher–Smith F.1.12(I)(4), printed pp.263–264 (`refs/quasithin.pdf`).
-/

public section
noncomputable section

open Subgroup
open Triality.Standard.RadicalCoordinates
open Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.RadicalCoordinates.LeviCommutators

namespace Triality.Standard.Parabolics.CentralRootSquare

theorem short_pair_square (P : Parameters) (hp : P.prime = 2) :
    (short P hp 1 1 * short P hp 2 1) ^ 2 = long P hp 2 1 := by
  let v : ArmsParameters P := (![1, 1], 0)
  have hs : armsCocycle P v v = 1 := by
    simpa [armsCocycle, v, armsPairing] using cubicTrace_fixed P hp (1 : fixedField P)
  have hv : (armsEquiv P hp v).val = short P hp 1 1 * short P hp 2 1 := by
    change toCarrier P (rootElement P hp .arms v) = _
    rw [rootElement_factorization]
    simp [v, extendOrbit]
  have he := congrArg Subtype.val (armsEquiv_square P hp v)
  change (armsEquiv P hp v).val ^ 2 = _ at he
  rw [hv, hs] at he
  refine he.trans ?_
  change toCarrier P (rootElement P hp .arms (centralParameters P 1)) = _
  rw [rootElement_factorization]
  simp [centralParameters, extendOrbit]

theorem radical_exists_square_ne_one (P : Parameters) (hp : P.prime = 2) :
    ∃ r ∈ radical P .central, (r : Carrier P) ^ 2 ≠ 1 := by
  let v : ArmsParameters P := (![1, 1], 0)
  have hs : armsCocycle P v v = 1 := by
    simpa [armsCocycle, v, armsPairing] using cubicTrace_fixed P hp (1 : fixedField P)
  have hne : (armsEquiv P hp v) ^ 2 ≠ 1 := by
    rw [armsEquiv_square, hs]
    intro h
    exact one_ne_zero ((armsEquiv_central_eq_one_iff P hp 1).mp h)
  have hv : (armsEquiv P hp v).val = short P hp 1 1 * short P hp 2 1 := by
    change toCarrier P (rootElement P hp .arms v) = _
    rw [rootElement_factorization]
    simp [v, extendOrbit]
  refine ⟨(armsEquiv P hp v).val, ?_, ?_⟩
  · rw [hv]
    apply (radical P .central).mul_mem
    · exact descendedRootSubgroup_le_radical P hp .central (short_mem P hp .central 1 trivial 1)
    · exact descendedRootSubgroup_le_radical P hp .central (short_mem P hp .central 2 trivial 1)
  · intro h
    apply hne
    exact Subtype.ext h

theorem not_levi_le_of_commutator_squares (P : Parameters) (hp : P.prime = 2)
    (hq : 2 < P.q) (X : Subgroup (Carrier P))
    (hsq : ∀ z ∈ ⁅radical P .central, X⁆, (z : Carrier P) ^ 2 = 1) :
    ¬ levi P .central ≤ X := by
  intro hX
  obtain ⟨r, hr, hne⟩ := radical_exists_square_ne_one P hp
  apply hne
  apply hsq
  have hc := commutator_mono (le_refl (radical P .central)) hX
  rw [commutator_radical_levi_eq P hp hq .central] at hc
  exact hc hr

end Triality.Standard.Parabolics.CentralRootSquare

end
