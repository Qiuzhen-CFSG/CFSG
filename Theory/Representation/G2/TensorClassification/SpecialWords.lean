module

public import Theory.Representation.G2.TensorClassification.SimpleDistinct

/-!
# Trivial and single-natural words in the G₂ tensor classification

The unipotent fixed-line theorem implies that a trivial tensor action has
dimension one. The product formula therefore forces every letter to be trivial;
the converse uses the actual tensor-unit intertwiner. In particular a
nontrivial action has product dimension different from one.

For a word with one natural letter, the tensor-unit intertwiners remove all
other letters. The resulting equivalence identifies the tensor with the scalar
extension of the trace-zero octonion quotient, precomposed with the actual field
Frobenius at that position. Dimension alone is not used to identify the action.

Source: GLS3, 2.8.6 and 2.8.10(g), used in Aschbacher--Smith G.9.3(10),
printed pp.354,356--357.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct
namespace Atlas.G2.TensorClassification
open Restricted
variable (F : Type*) [Field F] [CharP F 2] [Finite F]
  (K : Type*) [Field K] [Algebra F K]

/-- Product dimension one singles out precisely the all-trivial word. -/
theorem tensorDegree_eq_one_iff {n : ℕ} (w : Fin n → Factor) :
    (∏ i, (w i).dimension) = 1 ↔ ∀ i, w i = .trivial := by
  have hd : (∏ i, (w i).dimension) = wordDegree (List.ofFn w) := by
    simp [wordDegree, List.map_ofFn, List.prod_ofFn]
  rw [hd, wordDegree_eq_one_iff]
  simp only [List.mem_ofFn, forall_exists_index, forall_apply_eq_imp_iff]

/-- Triviality is a statement about the actual action, and occurs exactly for
the all-trivial word. -/
theorem tensorRep_eq_trivial_iff [CharP K 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (w : Fin n → Factor) :
    tensorRep F K w = Representation.trivial K (Model F) (TensorSpace F K w) ↔
      ∀ i, w i = .trivial := by
  constructor
  · intro h
    have hdim : Module.finrank K (TensorSpace F K w) = 1 := by
      apply (finrank_eq_one_iff_of_nonzero' (tensorHighestVector F K w)
        (tensorHighestVector_ne_zero F K w)).mpr
      intro v
      obtain ⟨c, hc⟩ := tensor_fixed_unipotent F K hF w v (by
        intro g hg
        rw [h]
        rfl)
      exact ⟨c, hc.symm⟩
    rw [finrank_tensorSpace] at hdim
    exact (tensorDegree_eq_one_iff w).mp hdim
  · intro hw
    let e := tensorTrivialEquiv F K w hw
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    apply e.toLinearEquiv.injective
    exact LinearMap.congr_fun (e.isIntertwining' g) v

/-- A nontrivial action cannot have product dimension one. This includes the
case in which faithfulness supplies nontriviality in a consumer. -/
theorem tensorDegree_ne_one_of_nontrivial [CharP K 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (w : Fin n → Factor)
    (h : tensorRep F K w ≠ Representation.trivial K (Model F) (TensorSpace F K w)) :
    (∏ i, (w i).dimension) ≠ 1 := by
  intro hd
  exact h ((tensorRep_eq_trivial_iff F K hF w).mpr ((tensorDegree_eq_one_iff w).mp hd))

private theorem ofFn_one_natural {n : ℕ} (w : Fin n → Factor) (i : Fin n)
    (hi : w i = .natural) (hw : ∀ j, j ≠ i → w j = .trivial) :
    List.ofFn w = List.replicate i.val .trivial ++
      .natural :: List.replicate (n - i.val - 1) .trivial := by
  apply List.ext_getElem
  · simp
    omega
  · intro j hj hk
    simp only [List.getElem_ofFn]
    by_cases hji : j < i.val
    · rw [List.getElem_append_left (by simpa using hji), List.getElem_replicate]
      exact hw _ (by intro he; have hh : j = i.val := congrArg Fin.val he; omega)
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hji)]
      by_cases he : j = i.val
      · subst j
        simpa only [List.length_replicate, Nat.sub_self, List.getElem_cons_zero] using hi
      · have hpos : 0 < j - i.val := by omega
        simp only [List.length_replicate]
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
        simp only [hk, List.getElem_cons_succ, List.getElem_replicate]
        exact hw _ (by intro hh; exact he (congrArg Fin.val hh))

/-- A word with exactly one natural letter is genuinely equivalent to the
scalar extension of the octonion quotient action, precomposed with Frobenius
at that letter's position. -/
def tensorOneNaturalEquiv {n : ℕ} (w : Fin n → Factor) (i : Fin n)
    (hi : w i = .natural) (hw : ∀ j, j ≠ i → w j = .trivial) :
    (tensorRep F K w).Equiv
      ((Representation.extendScalars K (Atlas.G2.Natural.action F)).comp
        (Restricted.frobeniusAutomorphism F i.val).toMonoidHom) := by
  let T (l : List Factor) :=
    (Representation.extendScalars K (wordRep F 0 l)).Equiv
      ((Representation.extendScalars K (Atlas.G2.Natural.action F)).comp
        (Restricted.frobeniusAutomorphism F i.val).toMonoidHom)
  change T (List.ofFn w)
  rw [ofFn_one_natural w i hi hw]
  exact oneNaturalExtendEquiv F K i.val (n - i.val - 1)

end Atlas.G2.TensorClassification

end
