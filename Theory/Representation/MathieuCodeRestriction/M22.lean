module

public import Theory.Representation.MathieuCodeRestriction.M22.HexadGeometry

/-!
# The marked fixed line in the M22 code

The actual octad word gives a nonzero vector in the eleven-dimensional Golay
quotient and is fixed by the octad pointwise kernel. For an octad obtained by
augmenting an M22 hexad, its two distinguished coordinates are both 1, so
this vector lies in the ten-dimensional code hyperplane. If the earlier
M24 fixed-space theorem gives dimension one, that vector spans the entire
fixed space; the exact kernel comparison then transfers this line to M22.

The only earlier input is the one-dimensional M24 fixed space from H.16.2(1).
No M22 fixed-space dimension is assumed. Group and module markings can be
changed together by an explicit native conjugation operator.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), H.13.1,
printed p.395; H.16.2(1), p.402; the M22 restriction in H.16.4(1), p.403,
and its use in 13.8.21(2), p.956. This module proves the conditional
restriction step, not the earlier H.16.2 theorem or the final M22 exclusion.
-/

@[expose] public section

noncomputable section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
open scoped Pointwise
namespace MathieuCode

private theorem octad_word_mem (O : Octad) : wordOfSet O.val ∈ golay := by
  rw [golay_eq_span_octads]
  exact Submodule.subset_span ⟨O.val, O.property, rfl⟩

/-- The class of the actual octad word in the eleven-dimensional code. -/
def octadVector (O : Octad) : Code := codeLine.mkQ ⟨wordOfSet O.val, by exact octad_word_mem O⟩

theorem octadVector_ne_zero (O : Octad) : octadVector O ≠ 0 := by
  intro hz
  have hm := (Submodule.Quotient.mk_eq_zero codeLine).mp hz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  change c • BinaryPermutation.allOne (Fin 24) = wordOfSet O.val at hc
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by rw [m24Blocks_card _ O.property]; decide)
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show O.val.card < (Finset.univ : Finset (Fin 24)).card by
      rw [m24Blocks_card _ O.property]; decide)
  have hci := congrFun hc i
  have hcj := congrFun hc j
  simp [BinaryPermutation.allOne, wordOfSet, hi] at hci
  simp [BinaryPermutation.allOne, wordOfSet, hj] at hcj
  exact zero_ne_one (hcj.symm.trans hci)

/-- The octad word is fixed by its actual pointwise kernel. -/
theorem octadVector_fixed (O : Octad) :
    octadVector O ∈ fixedSpace codeRepresentation (octadPointwiseKernel O) := by
  intro g
  have hf := (mem_octadPointwiseKernel O g.val).mp g.property
  have hs : g.val ∈ MulAction.stabilizer M24 O.val := by
    apply MulAction.mem_stabilizer_finset'.mpr
    intro i hi
    rwa [hf i hi]
  have he : g.val • O.val = O.val := MulAction.mem_stabilizer_iff.mp hs
  change codeRepresentation g.val (octadVector O) = octadVector O
  unfold octadVector
  rw [codeRepresentation_mk]
  congr 1
  apply Subtype.ext
  change BinaryPermutation.representation (Fin 24) g.val.val (wordOfSet O.val) = _
  rw [permute_wordOfSet]
  exact congrArg wordOfSet he

/-- Both distinguished coordinates of the augmented octad are 1, so its class
lies in the M22 hyperplane. -/
theorem m22OctadVector_mem {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    octadVector (m22Octad hB) ∈ m22Hyperplane := by
  change pairFunctional (octadVector (m22Octad hB)) = 0
  rw [octadVector, pairFunctional_mk]
  have h0 : (0 : Fin 24) ∈ m22AugmentedOctad B :=
    (mem_m22AugmentedOctad B 0).mpr (Or.inl rfl)
  have h9 : (9 : Fin 24) ∈ m22AugmentedOctad B :=
    (mem_m22AugmentedOctad B 9).mpr (Or.inr (Or.inl rfl))
  change wordOfSet (m22AugmentedOctad B) 0 + wordOfSet (m22AugmentedOctad B) 9 = 0
  simp [wordOfSet, h0, h9]

/-- The nonzero marked hexad vector in the ten-dimensional code. -/
def m22HexadVector {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) : M22Code :=
  ⟨octadVector (m22Octad hB), m22OctadVector_mem hB⟩

theorem m22HexadVector_ne_zero {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    m22HexadVector hB ≠ 0 := by
  intro h
  exact octadVector_ne_zero _ (congrArg Subtype.val h)

/-- The fixed space on the hyperplane is the literal restriction of the
fixed space for the corresponding octad kernel. -/
theorem m22FixedSpace_eq_comap {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    fixedSpace m22CodeRepresentation (m22HexadPointwiseKernel B) =
      (fixedSpace codeRepresentation (octadPointwiseKernel (m22Octad hB))).comap
        m22CodeInclusion := by
  rw [← m22HexadPointwiseKernel_map hB]
  ext v
  constructor
  · intro hv
    rintro ⟨g, u, hu, rfl⟩
    exact congrArg Subtype.val (hv ⟨u, hu⟩)
  · intro hv u
    apply Subtype.ext
    exact hv ⟨m22Embedding u.val, Subgroup.mem_map_of_mem _ u.property⟩

/-- The marked nonzero vector is fixed under the original native hexad kernel. -/
theorem m22HexadVector_fixed {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    m22HexadVector hB ∈ fixedSpace m22CodeRepresentation (m22HexadPointwiseKernel B) := by
  rw [m22FixedSpace_eq_comap hB]
  exact octadVector_fixed (m22Octad hB)

/-- The precise earlier input used from H.16.2(1). It concerns the actual
11-dimensional quotient and the actual native octad restriction kernel. -/
def M24OctadFixedLine : Prop :=
  ∀ O : Octad, Module.finrank (ZMod 2)
    (fixedSpace codeRepresentation (octadPointwiseKernel O)) = 1

/-- A one-dimensional octad fixed space is retained entirely in the M22 code:
the actual nonzero octad vector spans it and pairs trivially with the fixed pair. -/
theorem octad_fixedSpace_le_m22Hyperplane {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hline : Module.finrank (ZMod 2)
      (fixedSpace codeRepresentation (octadPointwiseKernel (m22Octad hB))) = 1) :
    fixedSpace codeRepresentation (octadPointwiseKernel (m22Octad hB)) ≤ m22Hyperplane := by
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hline
    (octadVector_fixed _) (octadVector_ne_zero _)]
  exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (m22OctadVector_mem hB))

/-- The marked restriction conclusion used on printed p.956, conditional only
on the earlier M24 octad fixed-line theorem, not on an M22 fixed-space premise. -/
theorem m22Hexad_fixedSpace_finrank {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hline : Module.finrank (ZMod 2)
      (fixedSpace codeRepresentation (octadPointwiseKernel (m22Octad hB))) = 1) :
    Module.finrank (ZMod 2) (fixedSpace m22CodeRepresentation
      (m22HexadPointwiseKernel B)) = 1 := by
  rw [m22FixedSpace_eq_comap hB]
  exact (Submodule.comapSubtypeEquivOfLe
    (octad_fixedSpace_le_m22Hyperplane hB hline)).finrank_eq.trans hline

/-- The retained fixed space is exactly the line generated by the marked hexad vector. -/
theorem m22Hexad_fixedSpace_eq_span {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hline : Module.finrank (ZMod 2)
      (fixedSpace codeRepresentation (octadPointwiseKernel (m22Octad hB))) = 1) :
    fixedSpace m22CodeRepresentation (m22HexadPointwiseKernel B) =
      Submodule.span (ZMod 2) {m22HexadVector hB} :=
  eq_span_singleton_of_mem_of_finrank_eq_one (m22Hexad_fixedSpace_finrank hB hline)
    (m22HexadVector_fixed hB) (m22HexadVector_ne_zero hB)

/-- Uniform H.16.2(1) supplies the marked M22 conclusion for every native hexad. -/
theorem m22Hexad_fixedSpace_finrank_of_M24 (hline : M24OctadFixedLine)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Module.finrank (ZMod 2) (fixedSpace m22CodeRepresentation
      (m22HexadPointwiseKernel B)) = 1 :=
  m22Hexad_fixedSpace_finrank hB (hline (m22Octad hB))

/-- The action of a native conjugating element on the actual hyperplane. -/
def m22CodeConjugationEquiv (g : M22) : M22Code ≃ₗ[ZMod 2] M22Code where
  toLinearMap := m22CodeRepresentation g
  invFun := m22CodeRepresentation g⁻¹
  left_inv v := by
    change m22CodeRepresentation g⁻¹ (m22CodeRepresentation g v) = v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  right_inv v := by
    change m22CodeRepresentation g (m22CodeRepresentation g⁻¹ v) = v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

@[simp] theorem m22CodeConjugationEquiv_apply (g : M22) (v : M22Code) :
    m22CodeConjugationEquiv g v = m22CodeRepresentation g v := rfl

/-- Changing the group marking by native conjugation changes the module
marking by this explicit representation operator. -/
theorem m22CodeConjugationEquiv_intertwines (g a : M22) (v : M22Code) :
    m22CodeConjugationEquiv g (m22CodeRepresentation a v) =
      m22CodeRepresentation (MulAut.conj g a) (m22CodeConjugationEquiv g v) := by
  change m22CodeRepresentation g (m22CodeRepresentation a v) =
    m22CodeRepresentation (g * a * g⁻¹) (m22CodeRepresentation g v)
  simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The recognition predicate is compatible with every explicit native conjugation. -/
theorem m22Code_marking_conj (ρ : Representation (ZMod 2) G V)
    (e : G ≃* M22) (E : V ≃ₗ[ZMod 2] M22Code)
    (hE : ∀ a v, E (ρ a v) = m22CodeRepresentation (e a) (E v)) (g : M22) :
    ∀ a v, (E.trans (m22CodeConjugationEquiv g)) (ρ a v) =
      m22CodeRepresentation ((e.trans (MulAut.conj g)) a)
        ((E.trans (m22CodeConjugationEquiv g)) v) := by
  intro a v
  change m22CodeConjugationEquiv g (E (ρ a v)) = _
  rw [hE]
  exact m22CodeConjugationEquiv_intertwines g (e a) (E v)

end MathieuCode
