module

public import CFSG.Quasithin.ClassicalModels
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.SpecificGroups.SU3.BinaryG2Comparison

/-!
# The four exceptional model identifications in K.2

The comparisons use the actual projective matrix groups and the actual
derived binary octonion group. Field and Hermitian-form transport extend
the concrete comparisons to every model in the source family. They apply
to L/Z(L), without replacing the covering group L or its ambient action.

The faithful-action comparisons and Fong recognition are proved in the
imported modules; no recognition by group order is used here. Attribution
and the ATLAS license for the reused ports are retained in those modules.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.2,
printed p.453 (PDF p.464).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.OddCharacteristic

open scoped MatrixGroups

variable {Q : Type*} [Group Q]

/-- K.2's four overlaps with the alternating and characteristic-two sections.
Every alternative carries an actual group isomorphism. -/
def IsCoincidence (Q : Type*) [Group Q] : Prop :=
  Nonempty (Q ≃* alternatingGroup (Fin 5)) ∨
  Nonempty (Q ≃* PSL(3, ZMod 2)) ∨
  Nonempty (Q ≃* alternatingGroup (Fin 6)) ∨
  Nonempty (Q ≃* commutator (Atlas.G2.Model (ZMod 2)))

/-- The icosahedral comparison, including arbitrary five-element field models. -/
theorem altFive_of_psl2_five (h : ClassicalGroup.IsPSL Q 2 5) :
    Nonempty (Q ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let f : F ≃+* ZMod 5 := (ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hc)).symm
  exact ⟨(e.trans (Atlas.fieldEquivPSL 2 f)).trans
    Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some⟩

/-- The same branch in the characteristic-two form used in K.3. -/
theorem psl2Four_of_psl2_five (h : ClassicalGroup.IsPSL Q 2 5) :
    Nonempty (Q ≃* PSL(2, GaloisField 2 2)) := by
  obtain ⟨e⟩ := altFive_of_psl2_five h
  exact ⟨e.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩

/-- The two faithful eight-point actions identify the order-168 models. -/
theorem psl3Two_of_psl2_seven (h : ClassicalGroup.IsPSL Q 2 7) :
    Nonempty (Q ≃* PSL(3, ZMod 2)) := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
  exact ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card7EquivPsl3Two hc)⟩

/-- The projective-line and complementary-triple actions identify the A₆ branch. -/
theorem altSix_of_psl2_nine (h : ClassicalGroup.IsPSL Q 2 9) :
    Nonempty (Q ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
  exact ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hc)⟩

/-- Fong recognition and Hermitian transport identify every PSU₃(3) model
with the literal commutator subgroup of the split-octonion G₂(2). -/
theorem g2Derived_of_psu3_three (h : ClassicalGroup.IsPSU Q 3 3) :
    Nonempty (Q ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  obtain ⟨F, _, _, J, hc, hj, ⟨e⟩⟩ := h
  exact ⟨e.trans (J.projectiveEquivBinaryG2Derived hc hj)⟩

/-- Apply the three linear coincidences to the precise numerical output of
the odd-linear restriction, preserving the input quotient. -/
theorem coincidence_of_small_psl2 {q : ℕ} (hq : q = 5 ∨ q = 7 ∨ q = 9)
    (h : ClassicalGroup.IsPSL Q 2 q) : IsCoincidence Q := by
  rcases hq with rfl | rfl | rfl
  · exact Or.inl (altFive_of_psl2_five h)
  · exact Or.inr (Or.inl (psl3Two_of_psl2_seven h))
  · exact Or.inr (Or.inr (Or.inl (altSix_of_psl2_nine h)))

end CFSG.Quasithin.ChapterK.OddCharacteristic
