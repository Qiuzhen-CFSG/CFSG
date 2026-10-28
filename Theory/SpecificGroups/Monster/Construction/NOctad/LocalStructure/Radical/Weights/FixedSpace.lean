module

public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Radical.Translations

/-!
# The full fixed space of the even octad cocode subgroup

For distinct weight-eight Golay words `c` and `d`, choose one point in
`d` outside `c` and another outside both octads. Their two-point cocode is
even, annihilates `c`, and pairs to one with `d`. The signed generator laws
therefore give an element of the literal barred `E_c⁺` that negates the
whole `d` block. Invariance of the positive form makes every fixed vector
orthogonal to every other block. The orthonormal basis of `c` and the
full block decomposition then put the vector in `block c`.

Conversely, the central subgroup `Z` acts trivially, and every specified
cocode generator fixes `block c`. This is the equality in the entire
`NOctad.Space`, using `imageRepresentation` on the actual image in `N/K`.
The only hypotheses are the three signed-vector laws `GeneratorLaws`;
evenness, separation, and decomposition are discharged here.

Source: Aschbacher, *Sporadic Groups*, Lemma 29.13(2), printed p. 160
(PDF p. 86), using 29.12 and the decomposition in 29.13(1).
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad.LocalStructure.Radical
open LocalC.ShortFamilies TrialitySpin Atlas.Codes Atlas.Fischer
open scoped BigOperators

/-- Even cocodes annihilating one octad separate it from every other octad.
The witness is the literal quotient of a two-point binary word. -/
theorem evenCocode_separates_octads (c d : NOctad.Octad) (hcd : c ≠ d) :
    ∃ a : Cocode, EvenCocode a ∧ cocodePairing c.val a = 0 ∧
      cocodePairing d.val a = 1 := by
  classical
  have hc : (support c.val.val).card = 8 := c.prop
  have hd : (support d.val.val).card = 8 := d.prop
  obtain ⟨i, hi, hic⟩ : ∃ i ∈ support d.val.val, i ∉ support c.val.val := by
    apply Finset.not_subset.mp
    intro he
    have hs := Finset.eq_of_subset_of_card_le he (by omega)
    apply hcd
    apply Subtype.ext
    apply Subtype.ext
    exact binarySupportEquiv.injective hs.symm
  have hic' : c.val.val i = 0 := by simpa [support] using hic
  have hi' : d.val.val i = 1 := (bit_cases _).resolve_left (by simpa [support] using hi)
  obtain ⟨j, hj⟩ : ∃ j, j ∉ support c.val.val ∪ support d.val.val := by
    have hb := Finset.card_union_le (support c.val.val) (support d.val.val)
    have hu : (Finset.univ : Finset Omega).card = 24 := by decide
    have hlt : (support c.val.val ∪ support d.val.val).card <
        (Finset.univ : Finset Omega).card := by omega
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    exact ⟨j, hj⟩
  have hjc : c.val.val j = 0 := by simpa [support] using (not_or.mp (mt Finset.mem_union.mpr hj)).1
  have hjd : d.val.val j = 0 := by simpa [support] using (not_or.mp (mt Finset.mem_union.mpr hj)).2
  let w : BinaryWord := Pi.single i 1 + Pi.single j 1
  refine ⟨Submodule.Quotient.mk w, ?_, ?_, ?_⟩
  · change cocodeDualEquiv (Submodule.Quotient.mk w) golayOne = 0
    rw [cocodeDualEquiv_mk]
    simp [w, binaryDot, golayOne, allOnes, CharTwo.add_self_eq_zero]
  · change cocodeDualEquiv (Submodule.Quotient.mk w) c.val = 0
    rw [cocodeDualEquiv_mk]
    simp [w, binaryDot, hic', hjc]
  · change cocodeDualEquiv (Submodule.Quotient.mk w) d.val = 1
    rw [cocodeDualEquiv_mk]
    simp [w, binaryDot, hi', hjd]

/-- An even cocode acts as its octad-pairing sign on the whole source block. -/
theorem representation_cocode_block (h : GeneratorLaws) (a : Cocode)
    (ha : EvenCocode a) (c : NOctad.Octad) (v : Space) (hv : v ∈ block c) :
    representation ⟨psiAut1N (parkerCocodeStandard a), psiAut1N_mem_N1 _⟩ v =
      (if cocodePairing c.val a = 0 then (1 : ℝ) else -1) • v := by
  have hk : block c ≤ LinearMap.ker
      (representation ⟨psiAut1N (parkerCocodeStandard a), psiAut1N_mem_N1 _⟩ -
        (if cocodePairing c.val a = 0 then (1 : ℝ) else -1) • LinearMap.id) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    change representation ⟨psiAut1N (parkerCocodeStandard a), psiAut1N_mem_N1 _⟩
      (vector p) - (if cocodePairing c.val a = 0 then (1 : ℝ) else -1) • vector p = 0
    rw [h.standard _ ((evenCocode_iff a).mp ha), standardParameters_cocode,
      vector_sign_bit, hp, sub_self]
  exact sub_eq_zero.mp (hk hv)

private def blockFixer (c : NOctad.Octad) : Subgroup N1 where
  carrier := {g | ∀ v ∈ block c, representation g v = v}
  one_mem' := by intro v _; simp
  mul_mem' := by
    intro g k hg hk v hv
    rw [map_mul]
    change representation g (representation k v) = v
    rw [hk v hv, hg v hv]
  inv_mem' := by
    intro g hg v hv
    have he := congrArg (representation g⁻¹) (hg v hv)
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one] at he
    exact he.symm

private theorem representation_z1 (h : GeneratorLaws) :
    representation ⟨z1N, psi1N_mem_N1 loopPi⟩ = 1 := by
  apply LinearMap.ext_on_range span_vectors
  intro p
  change representation ⟨psi1N loopPi, _⟩ (vector p) = vector p
  rw [h.first]
  apply congrArg vector
  apply parameters_ext
  · change parkerSign (binaryDot p.J (0 : golay).val + golayHalfOverlap p.c.1 0) p.c = p.c
    simp
  · rfl

private theorem representation_z2 (h : GeneratorLaws) :
    representation ⟨z2N, psi2N_mem_N1 loopPi⟩ = 1 := by
  apply LinearMap.ext_on_range span_vectors
  intro p
  change representation ⟨psi2N loopPi, _⟩ (vector p) = vector p
  rw [h.second]
  apply congrArg vector
  apply parameters_ext
  · simp [psi2Parameters, loopPi]
  · change p.J + p.c.1.val * (0 : golay).val = p.J
    simp

/-- The actual central subgroup acts trivially on the whole octad space. -/
theorem representation_Z (h : GeneratorLaws) (g : N1) (hg : g.val ∈ Z) :
    representation g = 1 := by
  have hZ : Z ≤ representation.ker.map N1.subtype := by
    apply (Subgroup.closure_le _).mpr
    have h1 : z1N ∈ representation.ker.map N1.subtype :=
      ⟨⟨z1N, psi1N_mem_N1 loopPi⟩, representation_z1 h, rfl⟩
    have h2 : z2N ∈ representation.ker.map N1.subtype :=
      ⟨⟨z2N, psi2N_mem_N1 loopPi⟩, representation_z2 h, rfl⟩
    rintro z (rfl | rfl | rfl)
    · exact h1
    · exact h2
    · apply ((representation.ker.map N1.subtype).mul_mem_cancel_left
        ((representation.ker.map N1.subtype).mul_mem h1 h2)).mp
      rw [z1N_z2N_z3N]
      exact Subgroup.one_mem _
  obtain ⟨k, hk, he⟩ := hZ hg
  have he' : k = g := Subtype.ext he
  exact he' ▸ hk

/-- The source block is fixed by the literal barred even octad annihilator. -/
theorem block_le_fixedSpace (h : GeneratorLaws) (c : NOctad.Octad) :
    block c ≤ fixedSpace c := by
  have hE : EcPlus c ≤ (blockFixer c).map N1.subtype := by
    apply sup_le
    · intro z hz
      refine ⟨⟨z, R_le_N1 (Z_le_R hz)⟩, ?_, rfl⟩
      intro v _
      rw [representation_Z h _ hz]
      rfl
    · apply (Subgroup.closure_le _).mpr
      rintro _ ⟨a, ha, hac, rfl⟩
      refine ⟨⟨psiAut1N (parkerCocodeStandard a), psiAut1N_mem_N1 _⟩, ?_, rfl⟩
      intro v hv
      rw [representation_cocode_block h a ha c v hv, if_pos hac, one_smul]
  intro v hv
  apply (mem_fixedSpace c v).mpr
  rintro ⟨_, g, hg, rfl⟩
  rw [imageRepresentation_map]
  obtain ⟨k, hk, he⟩ := hE hg
  have he' : k = g := Subtype.ext he
  subst k
  exact hk v hv

/-- Orthogonality to the other blocks leaves exactly the selected block's
finite orthonormal expansion. Positivity rules out any remaining vector. -/
private theorem mem_block_of_orthogonal_other (c : NOctad.Octad) (v : Space)
    (hv : ∀ d : NOctad.Octad, d ≠ c → ∀ w ∈ block d, gamma w v = 0) :
    v ∈ block c := by
  classical
  let u : Space := ∑ a : SubsetClass c, gamma (classVector c 0 a) v • classVector c 0 a
  have hu : u ∈ block c := (block c).sum_mem fun a _ =>
    (block c).smul_mem _ (classVector_mem_block c 0 a)
  have horth : (⊤ : Submodule ℝ Space) ≤ (gamma.flip (v - u)).ker := by
    rw [← block_iSup]
    apply iSup_le
    intro d
    by_cases hd : d = c
    · subst d
      rw [← span_classVector c]
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      change gamma (classVector c 0 a) (v - u) = 0
      simp only [u, map_sub, map_sum, map_smul, gamma_classVector, smul_eq_mul,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, sub_self]
    · intro w hw
      change gamma w (v - u) = 0
      rw [map_sub, hv d hd w hw, block_orthogonal hd hw hu, sub_self]
  have hz : v - u = 0 := by
    by_contra hn
    exact (ne_of_gt (gamma_pos (v - u) hn)) (horth (Submodule.mem_top))
  exact (sub_eq_zero.mp hz).symm ▸ hu

/-- Aschbacher 29.13(2): the fixed submodule in the entire octad space equals
the source octad block, with the actual quotient action and even cocodes. -/
theorem fixedSpace_eq_block (h : GeneratorLaws) (c : NOctad.Octad) :
    fixedSpace c = block c := by
  apply le_antisymm ?_ (block_le_fixedSpace h c)
  intro v hv
  apply mem_block_of_orthogonal_other c v
  intro d hdc w hw
  obtain ⟨a, ha, hac, had⟩ := evenCocode_separates_octads c d hdc.symm
  let g : N1 := ⟨psiAut1N (parkerCocodeStandard a), psiAut1N_mem_N1 _⟩
  have hg : n1ImageMap g ∈ barredEcPlus c := by
    refine ⟨g, ?_, rfl⟩
    exact (show Subgroup.closure (octadCocodeGenerators c) ≤ EcPlus c from le_sup_right)
      (Subgroup.subset_closure ⟨a, ha, hac, rfl⟩)
  have hfix : representation g v = v := by
    simpa only [imageRepresentation_map] using (mem_fixedSpace c v).mp hv ⟨_, hg⟩
  have hneg : representation g w = -w := by
    rw [representation_cocode_block h a ha d w hw, if_neg (by rw [had]; exact one_ne_zero),
      neg_one_smul]
  have he := representation_gamma g w v
  rw [hfix, hneg, map_neg, LinearMap.neg_apply] at he
  linarith

end Sporadic.Monster.Construction.NOctad.LocalStructure.Radical
