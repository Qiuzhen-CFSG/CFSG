module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.OddLocal.ThreeCentralizers.Geometry
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.OddLocal.ThreeCentralizers.Transport
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.OddLocal.ThreeCentralizers.UnitaryWitness

/-!
# Assembly of the Ree order-three centralizer theorem

Identify the centralizer of one order-three element with the full SU₃ over
GF(q²), where q = 2^(2m+1). Finite conjugacy transports this equivalence to a
generator of any subgroup of order three. The same conjugacy theorem produces
an element inverting the generator. Finally, a noncentral order-three element
in SU₃ prevents the cyclic subgroup from being normal, so its normalizer is
proper. These arguments supply both normalizer clauses without ambient
simplicity, subgroup exhaustion or a splitting theorem.

This assembly is conditional on `RepresentativeCentralizerModels` and
`ThreeElementConjugacy`. Constructing these two exceptional-group inputs is
still required before asserting the unconditional `threeCentralizers`.
The shared `ThreeCentralizers` and the parent odd-local assembly are unchanged.

Sources: GLS3, Theorem/Table 4.7.3A (printed pp.225–229), the exceptional
component interchange (p.232), and finite-class descent (pp.233–234),
`refs/KGroup/GLS3/chapter4.tex`; Example 2.6.3 (p.82),
`refs/KGroup/GLS3/chapter2.tex`. The SU₃ central kernel is retained throughout.
-/

public section

namespace ReeF4.MaximalSubgroups.AbelianCharacteristic.OddLocal

open Subgroup BenderSuzuki.MatrixGroups
open ReeF4.MaximalSubgroups.SimpleNormal.Construction

/-- The two geometric inputs imply the full order-three centralizer theorem.
All subgroup transport and normalizer assertions are discharged here. -/
theorem threeCentralizers_of_representative_and_conjugacy
    (hmodel : RepresentativeCentralizerModels) (hconj : ThreeElementConjugacy) :
    ThreeCentralizers := by
  intro m hm A hA
  obtain ⟨t, ht, ⟨et⟩⟩ := hmodel m hm
  obtain ⟨a, ha, hpow⟩ := exists_generator_of_card_three A hA
  obtain ⟨e⟩ := centralizers_equiv_of_isConj (hconj m hm t a ht ha)
  let f : centralizer ({a} : Set (Model m)) ≃* (standardForm m).specialSubgroup :=
    e.symm.trans et
  obtain ⟨x, y, hx, hxy⟩ := Matrix.SU3.exists_noncentral_order_three
    (standardForm m) rfl
  have hnoncentral : ∃ u v : centralizer ({a} : Set (Model m)),
      orderOf u = 3 ∧ u * v ≠ v * u := by
    refine ⟨f.symm x, f.symm y, (f.symm.orderOf_eq x).trans hx, ?_⟩
    intro heq
    apply hxy
    simpa using congrArg f heq
  have hN := normalizer_ne_top_of_three_conjugacy a
    (fun b hb => hconj m hm a b ha hb) hnoncentral
  have hC := centralizer_ne_normalizer_of_inverse_conjugacy a ha
    (hconj m hm a a⁻¹ ha ((orderOf_inv a).trans ha))
  have hCA : centralizer (A : Set (Model m)) = centralizer ({a} : Set (Model m)) := by
    rw [← hpow, zpowers_eq_closure, centralizer_closure]
  refine ⟨by simpa only [hpow] using hN, by simpa only [hpow] using hC,
    StandardField m, inferInstance, inferInstance, standardForm m,
    standardField_card m, standardForm_conj m, ?_⟩
  exact ⟨(MulEquiv.subgroupCongr hCA).trans f⟩

end ReeF4.MaximalSubgroups.AbelianCharacteristic.OddLocal
