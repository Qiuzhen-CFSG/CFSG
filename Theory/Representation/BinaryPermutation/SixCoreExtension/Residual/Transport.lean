module

public import Theory.Representation.BinaryPermutation.SixCoreExtension.Residual

/-!
# Transporting the six-letter core-square calculation

Every nonconstant even binary word has two exceptional coordinates: it is an
A6-image of the marked weight-two or weight-four word. A small checked
six-coordinate certificate selects those coordinates; double transitivity
provides the actual even permutation. The two marked words have the same
centralizer and the same coset of the distinguished constant line.

Conjugation carries the literal embedded residual core and its squares to the
corresponding subgroups. Consequently the two marked subgroup identities in
Residual imply the unique-square assertion for every nonconstant core vector.
Those identities remain explicit premises and are not claimed here.

Source: Aschbacher–Smith, I.2.2(6b), printed pp.410 and 412, combined
manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace BinaryPermutation.SixCoreExtension
noncomputable section

private def rareValue (x : Full (Fin 6)) : ZMod 2 :=
  if (∑ i, (x i).val) = 2 then 1 else 0

private def firstIndex (x : Full (Fin 6)) (c : ZMod 2) : Fin 6 :=
  if x 0 = c then 0 else if x 1 = c then 1 else if x 2 = c then 2 else
    if x 3 = c then 3 else if x 4 = c then 4 else 5

private def secondIndex (x : Full (Fin 6)) (c : ZMod 2) (i : Fin 6) : Fin 6 :=
  if 0 ≠ i ∧ x 0 = c then 0 else if 1 ≠ i ∧ x 1 = c then 1 else
    if 2 ≠ i ∧ x 2 = c then 2 else if 3 ≠ i ∧ x 3 = c then 3 else
      if 4 ≠ i ∧ x 4 = c then 4 else 5

private theorem binary_pair_certificate : ∀ x : Full (Fin 6),
    (∑ i, x i) = 0 → x ≠ 0 → x ≠ allOne (Fin 6) →
      let i := firstIndex x (rareValue x)
      let j := secondIndex x (rareValue x) i
      i ≠ j ∧ (x = Pi.single i 1 + Pi.single j 1 ∨
        x = Pi.single i 1 + Pi.single j 1 + allOne (Fin 6)) := by decide

private theorem binary_pair_or_complement (x : Full (Fin 6))
    (hx : (∑ i, x i) = 0) (h0 : x ≠ 0) (h1 : x ≠ allOne (Fin 6)) :
      ∃ i j : Fin 6, i ≠ j ∧
        (x = Pi.single i 1 + Pi.single j 1 ∨
          x = Pi.single i 1 + Pi.single j 1 + allOne (Fin 6)) :=
  ⟨_, _, binary_pair_certificate x hx h0 h1⟩

private theorem pair_word : pair.val = Pi.single 0 1 + Pi.single 1 1 := by decide

private theorem permute_single (g : Equiv.Perm (Fin 6)) (i : Fin 6) :
    representation (Fin 6) g (Pi.single i (1 : ZMod 2)) = Pi.single (g i) 1 := by
  ext j
  simp [Pi.single_apply, Equiv.symm_apply_eq]

theorem action_constant (g : A) : coreRepresentation (Fin 6) g.val constant = constant := by
  apply Subtype.ext
  funext i
  change constant.val (g.val.symm i) = constant.val i
  have hc (j : Fin 6) : constant.val j = 1 := by fin_cases j <;> rfl
  rw [hc, hc]

theorem constant_natural : coreToNatural (Fin 6) constant = 0 := by
  apply Subtype.ext
  apply (Submodule.Quotient.mk_eq_zero (constants (Fin 6))).mpr
  have he : constant.val = allOne (Fin 6) := by decide
  change constant.val ∈ constants (Fin 6)
  rw [he]
  exact Submodule.subset_span (Set.mem_singleton _)

/-- The actual two orbits of A6 on the nonconstant augmentation-core vectors. -/
theorem exists_pair_or_four_transport (v : V) (hv : coreToNatural (Fin 6) v ≠ 0) :
    ∃ g : A, coreRepresentation (Fin 6) g.val pair = v ∨
      coreRepresentation (Fin 6) g.val four = v := by
  have h0 : v.val ≠ 0 := by
    intro h
    have : v = 0 := Subtype.ext h
    exact hv (by simp [this])
  have h1 : v.val ≠ allOne (Fin 6) := by
    intro h
    have : v = constant := Subtype.ext (h.trans (by decide))
    exact hv (this ▸ constant_natural)
  obtain ⟨i, j, hij, he⟩ := binary_pair_or_complement v.val v.property h0 h1
  have := alternatingGroup.isMultiplyPretransitive (Fin 6)
  have ht : MulAction.IsMultiplyPretransitive A (Fin 6) 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card (Fin 6) - 2)
      (by simp) (Nat.sub_le _ _)
  obtain ⟨g, hgi, hgj⟩ := (MulAction.is_two_pretransitive_iff.mp ht)
    (by decide : (0 : Fin 6) ≠ 1) hij
  have hg : (coreRepresentation (Fin 6) g.val pair).val = Pi.single i 1 + Pi.single j 1 := by
    change representation (Fin 6) g.val pair.val = _
    rw [pair_word, map_add, permute_single, permute_single]
    rw [show g.val 0 = i from hgi, show g.val 1 = j from hgj]
  refine ⟨g, ?_⟩
  rcases he with he | he
  · exact Or.inl (Subtype.ext (hg.trans he.symm))
  · right
    rw [← pair_add_constant, map_add, action_constant]
    apply Subtype.ext
    change (coreRepresentation (Fin 6) g.val pair).val + constant.val = v.val
    rw [hg, he]
    rw [show constant.val = allOne (Fin 6) by decide]

/-- The distinguished kernel line is central in the entire model. -/
theorem centralLine_le_center : centralLine ≤ center Model := by
  rintro _ ⟨v, hv, rfl⟩
  apply mem_center_iff.mpr
  intro x
  apply mem_centralizer_singleton_iff.mp
  apply (mem_centralizer_vector x v.toAdd).mpr
  have hz : coreToNatural (Fin 6) v.toAdd = 0 := hv
  have hc : v.toAdd.val ∈ constants (Fin 6) :=
    (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hz)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hc
  apply Subtype.ext
  change representation (Fin 6) x.right.val v.toAdd.val = v.toAdd.val
  rw [← hc, map_smul, permute_allOne]

instance : centralLine.Normal where
  conj_mem z hz g := by
    have he := mem_center_iff.mp (centralLine_le_center hz) g
    simpa only [he, mul_inv_cancel_right] using hz

/-- The coordinate action is implemented by conjugation with the literal complement. -/
theorem conj_vector (g : A) (v : V) :
    MulAut.conj (SemidirectProduct.inr g : Model) (vector (Multiplicative.ofAdd v)) =
      vector (Multiplicative.ofAdd (coreRepresentation (Fin 6) g.val v)) := by
  change SemidirectProduct.inr g * SemidirectProduct.inl (Multiplicative.ofAdd v) *
      (SemidirectProduct.inr g)⁻¹ = _
  rw [← map_inv, ← SemidirectProduct.inl_aut]
  rfl

theorem centralizer_four_eq_pair :
    centralizer ({vector (Multiplicative.ofAdd four)} : Set Model) =
      centralizer ({vector (Multiplicative.ofAdd pair)} : Set Model) := by
  ext x
  rw [mem_centralizer_vector, mem_centralizer_vector,
    ← pair_add_constant, map_add, action_constant, add_left_inj]

theorem residualCore_four_eq_pair :
    centralizerResidualCore (vector (Multiplicative.ofAdd four)) =
      centralizerResidualCore (vector (Multiplicative.ofAdd pair)) := by
  unfold centralizerResidualCore centralizerTwoResidual
  rw [centralizer_four_eq_pair]

private theorem fiber_four_iff_pair (w : Model) :
    (vector (Multiplicative.ofAdd four))⁻¹ * w ∈ centralLine ↔
      (vector (Multiplicative.ofAdd pair))⁻¹ * w ∈ centralLine := by
  have hf : (vector (Multiplicative.ofAdd pair))⁻¹ *
      vector (Multiplicative.ofAdd four) ∈ centralLine :=
    (vector_fiber pair four).mpr four_natural_eq_pair.symm
  simpa only [mul_assoc, mul_inv_cancel_left] using
    (centralLine.mul_mem_cancel_left hf (y :=
      (vector (Multiplicative.ofAdd four))⁻¹ * w)).symm

private theorem unique_square_conj (g : Model) (t : Model)
    (ht : ∃! w : Model, t⁻¹ * w ∈ centralLine ∧
      ∃ x ∈ centralizerResidualCore t, x ^ 2 = w) :
    ∃! w : Model, (MulAut.conj g t)⁻¹ * w ∈ centralLine ∧
      ∃ x ∈ centralizerResidualCore (MulAut.conj g t), x ^ 2 = w := by
  let e := MulAut.conj g
  have hline : centralLine.map e.toMonoidHom = centralLine := Normal.map_conj_eq centralLine g
  have hcore := map_centralizerResidualCore e t
  have hmem (y : Model) : e y ∈ centralLine ↔ y ∈ centralLine := by
    conv_lhs => rw [← hline]
    exact (mem_map_equiv (f := e)).trans (by simp)
  obtain ⟨w, ⟨hw, x, hx, hsq⟩, huniq⟩ := ht
  refine ⟨e w, ⟨?_, e x, ?_, ?_⟩, ?_⟩
  · rw [← map_inv, ← map_mul]
    exact (hmem _).mpr hw
  · rw [← hcore]
    exact mem_map_of_mem e.toMonoidHom hx
  · rw [← map_pow, hsq]
  · rintro y ⟨hy, z, hz, hzy⟩
    have hz' : e.symm z ∈ centralizerResidualCore t := by
      rw [← hcore] at hz
      exact (mem_map_equiv (f := e)).mp hz
    have hf : t⁻¹ * e.symm y ∈ centralLine := by
      apply (hmem _).mp
      simpa only [map_mul, map_inv, e.apply_symm_apply] using hy
    have hsq' : e.symm z ^ 2 = e.symm y := by rw [← map_pow, hzy]
    have hu := huniq (e.symm y) ⟨hf, e.symm z, hz', hsq'⟩
    exact (e.apply_symm_apply y).symm.trans (congrArg e hu)

/-- The marked calculation suffices for every nonconstant core vector. -/
theorem unique_square_all_of_pair
    (hp : ∃! w : Model, (vector (Multiplicative.ofAdd pair))⁻¹ * w ∈ centralLine ∧
      ∃ x ∈ centralizerResidualCore (vector (Multiplicative.ofAdd pair)), x ^ 2 = w)
    (v : V) (hv : coreToNatural (Fin 6) v ≠ 0) :
    ∃! w : Model, (vector (Multiplicative.ofAdd v))⁻¹ * w ∈ centralLine ∧
      ∃ x ∈ centralizerResidualCore (vector (Multiplicative.ofAdd v)), x ^ 2 = w := by
  have hf : ∃! w : Model, (vector (Multiplicative.ofAdd four))⁻¹ * w ∈ centralLine ∧
      ∃ x ∈ centralizerResidualCore (vector (Multiplicative.ofAdd four)), x ^ 2 = w := by
    simpa only [residualCore_four_eq_pair, fiber_four_iff_pair] using hp
  obtain ⟨g, h | h⟩ := exists_pair_or_four_transport v hv
  · have he := unique_square_conj (SemidirectProduct.inr g) _ hp
    rwa [conj_vector, h] at he
  · have he := unique_square_conj (SemidirectProduct.inr g) _ hf
    rwa [conj_vector, h] at he

/-- Full model calculation, conditional only on the two explicit subgroup identities. -/
theorem unique_square_of_identities
    (hres : centralizerTwoResidual (vector (Multiplicative.ofAdd pair)) = pairResidual)
    (hcore : pairResidual.pCoreIn 2 = pairCore)
    (v : V) (hv : coreToNatural (Fin 6) v ≠ 0) :
    ∃! w : Model, (vector (Multiplicative.ofAdd v))⁻¹ * w ∈ centralLine ∧
      ∃ x ∈ centralizerResidualCore (vector (Multiplicative.ofAdd v)), x ^ 2 = w :=
  unique_square_all_of_pair (unique_square_pair_of_identities hres hcore) v hv

end
end BinaryPermutation.SixCoreExtension
