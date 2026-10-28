module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.TraceGeometry.Generators
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.PowerFusion.Coverage
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.ClassBound

/-!
# Odd-order conjugacy coverage by the local Hall--Janko trace witnesses

The exhaustive twenty-one-class coverage and checked even-order exclusions
leave ten odd-order representatives. Explicit carrier conjugators identify them
with the identity, four elements of the marked C₅ × C₅, the two cubics c and r²,
the standard septic ab, and two elements c*x^i of order fifteen. All identities
are checked on the certified four-point base of the literal degree-100 carrier.
The existing fusion of the septic representative's powers supplies square and
inverse conjugacy for ab.

Source application: Aschbacher--Smith K.4.5, printed p.460, and Hiss--Malle,
corrected Table 2, degree-six characteristic-two J₂ entry. Permutation source:
R. A. Wilson et al., ATLAS J2G1-p100B0; attribution is retained in
AtlasCarriers/source/. The adjacent OddClasses/source/ contains untrusted
witness discovery data. Exhaustiveness comes from the proved coverage theorem,
not the external computation.
-/

namespace Sporadic.LeechRelated.J2.TraceGeometry
open GeneratorPair GeneratorPair.SecondOrbitCertificate PowerFusionCertificate
open Theory.GroupTheory
open Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate

set_option maxRecDepth 20000 in
private theorem x_normalForm : x = element (84, 51, 16, 2) := by
  apply carrier_ext_base
  have h : inclusion x = evalWord ![generatorA, generatorB, generatorB⁻¹] xWord := rfl
  simp only [h, inclusion_element, generatorA_eq_table, generatorB_eq_table]
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem y_normalForm : y = element (36, 42, 19, 0) := by
  apply carrier_ext_base
  have h : inclusion y = evalWord ![generatorA, generatorB, generatorB⁻¹] yWord := rfl
  simp only [h, inclusion_element, generatorA_eq_table, generatorB_eq_table]
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem r_normalForm : r = element (60, 2, 15, 2) := by
  apply carrier_ext_base
  have h : inclusion r = evalWord ![generatorA, generatorB, generatorB⁻¹] rWord := rfl
  simp only [h, inclusion_element, generatorA_eq_table, generatorB_eq_table]
  apply allFin
  decide +kernel

set_option maxRecDepth 20000 in
private theorem c_normalForm : c = element (7, 7, 21, 3) := by
  apply carrier_ext_base
  have h : inclusion c = evalWord ![generatorA, generatorB, generatorB⁻¹] cWord := rfl
  simp only [h, inclusion_element, generatorA_eq_table, generatorB_eq_table]
  apply allFin
  decide +kernel

private theorem ab_normalForm : a * b = element (10, 31, 14, 3) := by
  apply carrier_ext_base
  simp only [map_mul, show inclusion a = tableA from generatorA_eq_table,
    show inclusion b = tableB from generatorB_eq_table, inclusion_element]
  apply allFin
  decide +kernel

private def localElement (j : Fin 10) : Carrier :=
  match j.val with
  | 0 => 1
  | 1 => c
  | 2 => x ^ 0 * y ^ 1
  | 3 => x ^ 0 * y ^ 2
  | 4 => c * x ^ 2
  | 5 => c * x ^ 1
  | 6 => r ^ 2
  | 7 => x ^ 1 * y ^ 1
  | 8 => x ^ 1 * y ^ 2
  | _ => a * b

private def localConjugator (j : Fin 10) : Index :=
  match j.val with
  | 0 => (0, 0, 0, 0)
  | 1 => (76, 55, 17, 2)
  | 2 => (17, 24, 9, 2)
  | 3 => (5, 34, 23, 3)
  | 4 => (21, 47, 14, 3)
  | 5 => (72, 29, 18, 2)
  | 6 => (52, 7, 23, 3)
  | 7 => (83, 0, 17, 2)
  | 8 => (79, 31, 12, 0)
  | _ => (45, 55, 15, 3)

set_option maxRecDepth 20000 in
private theorem local_check : ∀ j : Fin 10, ∀ k : Fin 4,
    inclusion (element (localConjugator j))
        (inclusion (representative (oddIndex j)) (k.castLE (by decide))) =
      inclusion (localElement j)
        (inclusion (element (localConjugator j)) (k.castLE (by decide))) := by
  simp only [localElement, x_normalForm, y_normalForm, r_normalForm, c_normalForm]
  simp only [ab_normalForm]
  apply allFin
  decide +kernel

private theorem local_conjugacy (j : Fin 10) :
    IsConj (representative (oddIndex j)) (localElement j) :=
  isConj_of_base _ _ (element (localConjugator j)) (local_check j)

/-- Every odd-order element is conjugate inside the literal carrier to one of
the displayed local trace witnesses. This includes both classes of order fifteen. -/
public theorem odd_order_conjugacy (g : Carrier) (hg : ¬2 ∣ orderOf g) :
    (∃ i j : Fin 5, IsConj g (x ^ i.val * y ^ j.val)) ∨
    IsConj g c ∨ IsConj g (r ^ 2) ∨ IsConj g (a * b) ∨
    (∃ i : Fin 5, IsConj g (c * x ^ i.val)) := by
  obtain ⟨j, hj⟩ := odd_cover representativeCoverage g hg
  have h := hj.symm.trans (local_conjugacy j)
  fin_cases j
  · exact Or.inl ⟨0, 0, by simpa [localElement] using h⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inl ⟨0, 1, h⟩
  · exact Or.inl ⟨0, 2, h⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨2, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨1, h⟩)))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inl ⟨1, 1, h⟩
  · exact Or.inl ⟨1, 2, h⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

/-- The standard product ab has order seven in the literal carrier. -/
public theorem orderOf_ab : orderOf (a * b) = 7 := by
  have h : IsConj (representative 19) (a * b) := local_conjugacy 9
  obtain ⟨z, hz⟩ := h
  exact (hz.orderOf_eq (↑z : Carrier)).symm.trans representative_nineteen_order

/-- The standard septic is conjugate to its square inside J₂. -/
public theorem ab_isConj_square : IsConj (a * b) ((a * b) ^ 2) := by
  have h : IsConj (representative 19) (a * b) := local_conjugacy 9
  exact h.symm.trans ((representative_nineteen_power_fusion 1).trans (h.pow 2))

/-- The standard septic is conjugate to its inverse inside J₂. -/
public theorem ab_isConj_inv : IsConj (a * b) (a * b)⁻¹ := by
  have h : IsConj (representative 19) (a * b) := local_conjugacy 9
  have he : (a * b) ^ 6 = (a * b)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ]
    exact ab_pow_seven
  rw [← he]
  exact h.symm.trans ((representative_nineteen_power_fusion 5).trans (h.pow 6))

end Sporadic.LeechRelated.J2.TraceGeometry
