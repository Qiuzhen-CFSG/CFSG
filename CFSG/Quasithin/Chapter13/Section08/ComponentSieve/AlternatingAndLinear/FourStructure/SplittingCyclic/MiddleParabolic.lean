module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.MiddleParabolic.Generation
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.MiddleParabolic.Obstruction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.MiddleParabolic.FlagTransport
public import Theory.ElementaryAbelian.Basic

/-!
# The middle-node obstruction in GL₄(2)

For an incident flag L ≤ P ≤ F of dimensions 1,2,3, `middle L F` is the
actual line--hyperplane stabilizer and `borel L P F` is the full flag
stabilizer. This module proves the three intrinsic facts used by the
cyclic-case contradiction in Aschbacher--Smith 13.8.25, printed p.962
(PDF p.979 of the combined manuscript of 1 March 2004):

* the middle parabolic has no relatively normal elementary four-group;
* it centralizes the ambient image of the full flag stabilizer's center;
* the full flag stabilizer normally generates the middle parabolic.

The obstruction and generation proofs use explicit binary block actions;
an adapted basis transports them to the given flag. The center calculation
uses the two end-node radicals. No group-shape or classification hypothesis
is used, and the normalizer conditions are relative to the middle parabolic.
-/

public section

namespace BinaryLinear.MiddleParabolic

/-- An elementary abelian subgroup of order four cannot be normal in the
middle minimal parabolic of an incident 1,2,3 flag in GL₄(2). -/
theorem no_normal_elementary_four
    {L P F : Submodule (ZMod 2) V} (hLP : L ≤ P) (hPF : P ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hF : Module.finrank (ZMod 2) F = 3)
    (E : Subgroup (BinaryLinear.GL V)) [IsElementaryAbelian 2 E]
    (hcard : Nat.card E = 4) (hEH : E ≤ middle L F)
    (hHE : middle L F ≤ Subgroup.normalizer E) : False := by
  obtain ⟨e, heH, _⟩ := exists_flag_conjugation L P F hLP hPF hL hP hF
  let a := MulAut.conj e
  have hmem (x : BinaryLinear.GL V) : a x ∈ middle L F ↔ x ∈ middle line hyperplane := by
    rw [← heH, Subgroup.mem_map_equiv]
    change a.symm (a x) ∈ middle line hyperplane ↔ x ∈ middle line hyperplane
    rw [a.symm_apply_apply]
  let E' := E.comap a.toMonoidHom
  apply standard_no_normal_four E'
  · intro x hx
    apply a.injective
    simpa only [map_pow, map_one] using elemPow_eq_one_of_isElementaryAbelian (a x) hx
  · change Nat.card (E.comap a.toMonoidHom) = 4
    have heq : E.comap a.toMonoidHom = E.map a.symm.toMonoidHom :=
      Subgroup.comap_equiv_eq_map_symm a E
    exact (Nat.card_congr (MulEquiv.subgroupCongr heq).toEquiv).trans
      ((Nat.card_congr (a.symm.subgroupMap E).toEquiv).symm.trans hcard)
  · intro x hx
    exact (hmem x).mp (hEH hx)
  · intro x hx
    apply Subgroup.le_normalizer_comap a.toMonoidHom
    exact hHE ((hmem x).mpr hx)

/-- The actual middle parabolic centralizes the ambient image of the
intrinsic center of the full flag stabilizer. -/
theorem centralizes_flag_center
    {L P F : Submodule (ZMod 2) V} (hLP : L ≤ P) (hPF : P ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hF : Module.finrank (ZMod 2) F = 3) :
    middle L F ≤ Subgroup.centralizer
      ((Subgroup.center (borel L P F)).map (borel L P F).subtype : Set (BinaryLinear.GL V)) := by
  apply middle_centralizes_borel_center hLP hPF hL
  rw [hF]
  simp [V]

/-- The full flag stabilizer normally generates the middle minimal parabolic;
the ambient subgroup N need only be normalized by that parabolic. -/
theorem normally_generates
    {L P F : Submodule (ZMod 2) V} (hLP : L ≤ P) (hPF : P ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hF : Module.finrank (ZMod 2) F = 3)
    (N : Subgroup (BinaryLinear.GL V)) (hTN : borel L P F ≤ N)
    (hHN : middle L F ≤ Subgroup.normalizer N) : middle L F ≤ N := by
  obtain ⟨e, heH, heT⟩ := exists_flag_conjugation L P F hLP hPF hL hP hF
  let a := MulAut.conj e
  have hgen : middle line hyperplane ≤ N.comap a.toMonoidHom := by
    apply standard_normally_generates
    · intro x hx
      apply hTN
      rw [← heT]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    · intro x hx
      apply Subgroup.le_normalizer_comap a.toMonoidHom
      apply hHN
      rw [← heH]
      exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  intro x hx
  rw [← heH] at hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  exact hgen hy

end BinaryLinear.MiddleParabolic

end
