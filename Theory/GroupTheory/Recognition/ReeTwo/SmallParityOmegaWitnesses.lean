module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityRepresentatives
public import Theory.GroupTheory.CentricRadicalCertificates
/-!
# Omega Frattini witnesses for the five small parity candidates

The candidates with diagnostic labels 463, 882, 887, 890 and 891 have explicit
outside normalizer elements. In fact these elements centralize every involution
in the candidate, hence its first omega subgroup, and every displacement on the
whole candidate has square one. Thus the first Frattini displacement is the
identity and the second already lies in omega.

Binary coordinate normal forms certify membership and generation. Closure under
left multiplication by each generator and its inverse proves that these forms
cover the entire subgroup. All finite identities are checked by the Lean kernel
in the verified Sylow model; the conjugation tests use both orientations.

Source: Shinoda (1975), (2.3), pp. 81–82, via `ReeTwo.Core`, `RootAction` and
`Sylow`. The root-word representatives and diagnostic labels are those of
`SmallParityRepresentatives`.
-/

namespace ReeTwo.SylowModel

private def generators (i : Fin 5) : Fin 7 → SylowModel :=
  ![![root 2 * root 4 * root 8, rootOne ^ 3, rootOne ^ 2, root 4, root 7, root 9, root 8],
  ![rootOne ^ 3, root 4 * root 8, root 9, rootOne ^ 2, root 8, root 8, root 8],
  ![rootOne ^ 3 * root 3 * root 4, root 4 * root 8, root 9, rootOne ^ 2 * root 4 * root 8, root 8, root 8, root 8],
  ![root 2 * root 4 * root 8, rootOne ^ 3, rootOne ^ 2, root 8 * root 9, root 8, root 8, root 8],
  ![root 2 * root 8, rootOne ^ 3, rootOne ^ 2, root 8 * root 9, root 8, root 8, root 8]] i

private theorem range_seven {α : Type*} (a b c d e f g : α) :
  Set.range ![a, b, c, d, e, f, g] = {a, b, c, d, e, f, g} := by
  ext x
  simp [eq_comm, or_comm, or_left_comm]

private theorem range_five {α : Type*} (a b c d e : α) :
  Set.range ![a, b, c, d, e, e, e] = {a, b, c, d, e} := by
  ext x
  simp [eq_comm, or_comm, or_left_comm]

private theorem candidate_eq (i : Fin 5) :
  smallParityOddCandidate i = Subgroup.closure (Set.range (generators i)) := by
  fin_cases i
  · exact congrArg Subgroup.closure (range_seven _ _ _ _ _ _ _).symm
  · exact congrArg Subgroup.closure (range_five _ _ _ _ _).symm
  · exact congrArg Subgroup.closure (range_five _ _ _ _ _).symm
  · exact congrArg Subgroup.closure (range_five _ _ _ _ _).symm
  · exact congrArg Subgroup.closure (range_five _ _ _ _ _).symm

/-- Binary indices for the 128-element and four 32-element normal forms. -/
private def Params (i : Fin 5) : Type :=
  ![Fin 128, Fin 32, Fin 32, Fin 32, Fin 32] i

private instance : (i : Fin 5) → Fintype (Params i)
  | 0 => inferInstanceAs (Fintype (Fin 128))
  | 1 => inferInstanceAs (Fintype (Fin 32))
  | 2 => inferInstanceAs (Fintype (Fin 32))
  | 3 => inferInstanceAs (Fintype (Fin 32))
  | 4 => inferInstanceAs (Fintype (Fin 32))

private def bit {n : ℕ} (v : Fin n) (j : ℕ) : ZMod 2 := (v.val / 2 ^ j : ℕ)

private def element : (i : Fin 5) → Params i → SylowModel
  | 0, v => ⟨⟨0, 0, bit v 0, 0, bit v 1, 0, 0, bit v 2, bit v 3, bit v 4⟩,
      Multiplicative.ofAdd ((bit v 5).val + 2 * (bit v 6).val)⟩
  | 1, v => ⟨⟨0, 0, 0, 0, bit v 0, 0, 0, 0, bit v 1, bit v 2⟩,
      Multiplicative.ofAdd ((bit v 3).val + 2 * (bit v 4).val)⟩
  | 2, v => ⟨⟨0, 0, 0, bit v 3, bit v 0, 0, 0, 0, bit v 1, bit v 2⟩,
      Multiplicative.ofAdd ((bit v 3).val + 2 * (bit v 4).val)⟩
  | 3, v => ⟨⟨0, 0, bit v 0, 0, bit v 0, 0, 0, 0, bit v 1, bit v 2⟩,
      Multiplicative.ofAdd ((bit v 3).val + 2 * (bit v 4).val)⟩
  | 4, v => ⟨⟨0, 0, bit v 0, 0, 0, 0, 0, 0, bit v 1, bit v 2⟩,
      Multiplicative.ofAdd ((bit v 3).val + 2 * (bit v 4).val)⟩

private def coordinates : (i : Fin 5) → SylowModel → Params i
  | 0, x => ⟨(x.left.b2.val + 2 * x.left.b4.val + 4 * x.left.b7.val + 8 * x.left.b8.val +
  16 * x.left.b9.val + 32 * x.right.toAdd.val) % 128, Nat.mod_lt _ (by decide)⟩
  | 1, x => ⟨(x.left.b4.val + 2 * x.left.b8.val + 4 * x.left.b9.val + 8 * x.right.toAdd.val) % 32, Nat.mod_lt _ (by decide)⟩
  | 2, x => ⟨(x.left.b4.val + 2 * x.left.b8.val + 4 * x.left.b9.val + 8 * x.right.toAdd.val) % 32, Nat.mod_lt _ (by decide)⟩
  | 3, x => ⟨(x.left.b2.val + 2 * x.left.b8.val + 4 * x.left.b9.val + 8 * x.right.toAdd.val) % 32, Nat.mod_lt _ (by decide)⟩
  | 4, x => ⟨(x.left.b2.val + 2 * x.left.b8.val + 4 * x.left.b9.val + 8 * x.right.toAdd.val) % 32, Nat.mod_lt _ (by decide)⟩
/-- Exponents expressing each coordinate form in the original generators. -/
private def exponents : (i : Fin 5) → Params i → Fin 7 → ZMod 2
  | 0, v => ![bit v 0, bit v 5, bit v 6, bit v 0 + bit v 1, bit v 2, bit v 4, bit v 0 + bit v 3 + bit v 2 * bit v 5]
  | 1, v => ![bit v 3, bit v 0, bit v 2, bit v 4, bit v 0 + bit v 1, 0, 0]
  | 2, v => ![bit v 3, bit v 0 + bit v 4, bit v 2, bit v 4, bit v 0 + bit v 1, 0, 0]
  | 3, v => ![bit v 0, bit v 3, bit v 4, bit v 2, bit v 0 + bit v 1 + bit v 2, 0, 0]
  | 4, v => ![bit v 0, bit v 3, bit v 4, bit v 2, bit v 0 + bit v 1 + bit v 2, 0, 0]

private def word (i : Fin 5) (v : Params i) : SylowModel :=
  (List.ofFn fun j : Fin 7 => generators i j ^ (exponents i v j).val).prod
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem element_word : ∀ i v, word i v = element i v := by
  intro i; fin_cases i <;> decide +kernel

private theorem element_mem (i : Fin 5) (v : Params i) :
    element i v ∈ smallParityOddCandidate i := by
  rw [← element_word]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  apply Subgroup.pow_mem
  rw [candidate_eq]
  exact Subgroup.subset_closure ⟨j, rfl⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem left_step : ∀ i v j,
  element i (coordinates i (generators i j * element i v)) = generators i j * element i v ∧
  element i (coordinates i ((generators i j)⁻¹ * element i v)) = (generators i j)⁻¹ * element i v := by
  intro i; fin_cases i <;> decide +kernel

private theorem normal_form (i : Fin 5) (x : SylowModel)
    (hx : x ∈ smallParityOddCandidate i) : element i (coordinates i x) = x := by
  rw [candidate_eq] at hx
  induction hx using Subgroup.closure_induction_left with
  | one => exact (by decide +kernel : ∀ i, element i (coordinates i 1) = 1) i
  | mul_left x hx y hy ih =>
    obtain ⟨j, rfl⟩ := hx
    simpa only [ih] using (left_step i (coordinates i y) j).1
  | inv_mul_cancel x hx y hy ih =>
    obtain ⟨j, rfl⟩ := hx
    simpa only [ih] using (left_step i (coordinates i y) j).2

/-- Witnesses in the order 463, 882, 887, 890, 891. -/
private def witness (i : Fin 5) : SylowModel :=
  ![root 3, root 4 * root 7 * root 8, rootOne ^ 3,
    root 4 * root 7 * root 8, root 4 * root 7 * root 8] i
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem conjugation_test : ∀ i v,
  element i (coordinates i (witness i * element i v * (witness i)⁻¹)) =
    witness i * element i v * (witness i)⁻¹ ∧
  element i (coordinates i ((witness i)⁻¹ * element i v * witness i)) =
    (witness i)⁻¹ * element i v * witness i := by
  intro i; fin_cases i <;> decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem involution_test : ∀ i v, element i v ^ 2 = 1 →
  witness i * element i v = element i v * witness i := by
  intro i; fin_cases i <;> decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
private theorem displacement_test : ∀ i v,
  ((element i v)⁻¹ * (witness i * element i v * (witness i)⁻¹)) ^ 2 = 1 := by
  intro i; fin_cases i <;> decide +kernel

private theorem outside_test : ∀ i,
  element i (coordinates i (witness i)) ≠ witness i := by
  intro i; fin_cases i <;> decide +kernel

private theorem witness_normalizes (i : Fin 5) :
  witness i ∈ Subgroup.normalizer (smallParityOddCandidate i : Set SylowModel) := by
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    have he := (conjugation_test i (coordinates i x)).1
    rw [normal_form i x hx] at he
    rw [← he]
    exact element_mem _ _
  · intro hx
    have he := (conjugation_test i (coordinates i (witness i * x * (witness i)⁻¹))).2
    rw [normal_form i _ hx] at he
    simp only [← mul_assoc, inv_mul_cancel, one_mul, inv_mul_cancel_right] at he
    rw [← he]
    exact element_mem _ _

/-- Centralizing involutions and having involutory displacements suffice. -/
private theorem witness_of_tests {G : Type*} [Group G] (U : Subgroup G)
    (g : Subgroup.normalizer (U : Set G)) (hout : (g : G) ∉ U)
    (hinv : ∀ x : U, x ^ 2 = 1 → U.normalizerMonoidHom g x = x)
    (hdisp : ∀ x : U, (x⁻¹ * U.normalizerMonoidHom g x) ^ 2 = 1) :
    Subgroup.HasOmegaFrattiniWitness 2 U := by
  refine ⟨g, hout, ?_, ?_⟩
  · have hc : omega₁ U (p := 2) ≤
        (U.normalizerMonoidHom g).toMonoidHom.eqLocus (MonoidHom.id U) := by
      apply (Subgroup.closure_le _).mpr
      intro x hx
      exact hinv x (by simpa only [pow_one, Set.mem_ofPred_eq] using hx)
    intro x
    have he : U.normalizerMonoidHom g (x : U) = (x : U) := hc x.property
    rw [he, inv_mul_cancel]
    exact Subgroup.one_mem _
  · intro x
    apply (le_sup_left : omega₁ U (p := 2) ≤ omega₁ U (p := 2) ⊔ frattini U)
    exact Subgroup.subset_closure (by simpa only [pow_one, Set.mem_ofPred_eq] using hdisp x)

/-- Each of the five exceptional parity candidates admits an outside omega
Frattini witness. -/
public theorem smallParityOddCandidate_hasOmegaFrattiniWitness (i : Fin 5) :
  Subgroup.HasOmegaFrattiniWitness 2 (smallParityOddCandidate i) := by
  apply witness_of_tests (smallParityOddCandidate i) ⟨witness i, witness_normalizes i⟩
  · intro h
    exact outside_test i (normal_form i _ h)
  · intro x hx
    apply Subtype.ext
    change witness i * (x : SylowModel) * (witness i)⁻¹ = x
    have he := involution_test i (coordinates i x)
    rw [normal_form i x x.property] at he
    have hx' : (x : SylowModel) ^ 2 = 1 := congrArg Subtype.val hx
    rw [he hx', mul_inv_cancel_right]
  · intro x
    apply Subtype.ext
    change ((x : SylowModel)⁻¹ * (witness i * x * (witness i)⁻¹)) ^ 2 = 1
    simpa only [normal_form i x x.property] using displacement_test i (coordinates i x)

end ReeTwo.SylowModel
