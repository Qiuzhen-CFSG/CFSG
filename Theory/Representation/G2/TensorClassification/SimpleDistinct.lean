module

public import Theory.Representation.G2.TensorClassification.SimpleDistinct.Boundary
public import Theory.Representation.G2.TensorClassification.SimpleDistinct.Cyclicity
public import Theory.Representation.G2.TensorClassification.SimpleDistinct.FixedLine

/-!
# Simplicity and distinctness of the concrete G₂ Frobenius tensors

A nonzero invariant subspace has a nonzero fixed vector for the positive
unipotent two-group. The fixed space is the specified highest line by
`FixedLine`, and its orbit spans by the invariant-pairing argument in
`Cyclicity`. Hence that subspace is the entire tensor module.

An intertwiner must identify the highest lines. Their coroot characters recover
the positive binary weights; the actual Weyl reflections distinguish zero from
q−1. Binary expansion then recovers every restricted factor, including the
all-trivial word and every boundary weight.

The final theorems discharge every fixed-line and orbit-span premise for the
literal tensor action. They hold over every coefficient-field extension;
algebraic closure and `n ≥ 2` are unnecessary. The earlier conditional APIs
are retained. Exhaustion and Frobenius rotation belong to the classification
assembly.

Source: GLS3, 2.8.2, 2.8.5–6, 2.8.9 and 2.8.10(g), used in
Aschbacher--Smith G.9.3(10), printed pp.354, 356–357.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false
namespace Atlas.G2.TensorClassification
open Restricted

/-- Each restricted simple-coroot coordinate is a binary digit. -/
theorem weightBit_le_one (s : Bool) (a : Factor) : weightBit s a ≤ 1 := by
  cases s <;> cases a <;> decide

/-- Each tensor highest-weight coordinate lies in the restricted range. -/
theorem wordWeight_lt_two_pow_length (s : Bool) (w : List Factor) :
    wordWeight s w < 2 ^ w.length := by
  induction w with
  | nil => simp [wordWeight]
  | cons a w ih =>
    have hb := weightBit_le_one s a
    simp only [wordWeight, List.length_cons, pow_succ]
    omega

/-- The two binary highest weights recover the whole word of a fixed length. -/
theorem wordWeight_pair_injective (a b : List Factor) (hlen : a.length = b.length)
    (h : ∀ s, wordWeight s a = wordWeight s b) : a = b := by
  induction a generalizing b with
  | nil =>
    have hb : b = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
    exact hb.symm
  | cons x a ih =>
    cases b with
    | nil => simp at hlen
    | cons y b =>
      have hs := h false
      have hl := h true
      simp only [wordWeight] at hs hl
      have hxs := weightBit_le_one false x
      have hys := weightBit_le_one false y
      have hxl := weightBit_le_one true x
      have hyl := weightBit_le_one true y
      have hbs : weightBit false x = weightBit false y := by omega
      have hbl : weightBit true x = weightBit true y := by omega
      have hxy : x = y := by
        cases x <;> cases y <;>
          simp_all [weightBit, Factor.shortWeight, Factor.longWeight]
      have hab : a = b := ih b (by simpa using hlen) (by
        intro s
        cases s <;> omega)
      rw [hxy, hab]

variable {F : Type*} [Field F] [CharP F 2] [Finite F]
  {K : Type*} [Field K] [Algebra F K]
  {n : ℕ}

/-- The all-trivial word is irreducible over every coefficient extension. -/
theorem tensorRep_irreducible_of_all_trivial (w : Fin n → Factor)
    (hw : ∀ i, w i = .trivial) : Representation.IsIrreducible (tensorRep F K w) := by
  let e := (tensorTrivialEquiv F K w hw).trans (trivialExtendEquiv F K).symm
  exact (Representation.RepEquiv.irreducible_euqiv
    (Representation.RepEquiv.ofRepresentationEquiv e)).mpr
      (Restricted.irreducible_extendScalars F .trivial K)

/-- One-dimensional unipotent fixed space plus highest-vector cyclicity implies
simplicity of the actual tensor representation. -/
theorem tensorRep_irreducible_of_fixedLine_and_span [CharP K 2]
    (hF : Nat.card F = 2 ^ n) (w : Fin n → Factor)
    (hfixed : ∀ v : TensorSpace F K w,
      (∀ g ∈ (unipotent : Subgroup (Model F)), tensorRep F K w g v = v) →
        ∃ c : K, v = c • tensorHighestVector F K w)
    (hspan : Submodule.span K (Set.range fun g : Model F =>
      tensorRep F K w g (tensorHighestVector F K w)) = ⊤) :
    Representation.IsIrreducible (tensorRep F K w) := by
  let : Nontrivial (TensorSpace F K w) :=
    ⟨⟨tensorHighestVector F K w, 0, tensorHighestVector_ne_zero F K w⟩⟩
  apply IsSimpleOrder.of_forall_eq_top
  intro S hS
  have hn : S.toSubmodule ≠ ⊥ := fun h => hS (Subrepresentation.toSubmodule_injective h)
  let : Nontrivial S.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hn
  have hp : IsPGroup (ringChar K) (unipotent (K := F)) := by
    rw [ringChar.eq K 2]
    apply IsPGroup.of_card (n := n * 6)
    rw [card_unipotent, hF, pow_mul]
  obtain ⟨v, hv, hfix⟩ := Representation.pGroup_fix_nonzero_vector
    (F := K) (G := unipotent (K := F)) (V := S.toSubmodule)
    (by rw [ringChar.eq K 2]; decide) hp (S.toRepresentation.comp unipotent.subtype)
  obtain ⟨c, hc⟩ := hfixed v.val (fun g hg => congrArg Subtype.val (hfix ⟨g, hg⟩))
  have hc0 : c ≠ 0 := by
    intro h
    apply hv
    apply Subtype.ext
    change v.val = (0 : TensorSpace F K w)
    simpa only [h, zero_smul] using hc
  have hseed : tensorHighestVector F K w ∈ S := by
    apply (S.toSubmodule.smul_mem_iff hc0).mp
    rw [← hc]
    exact v.property
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  exact S.apply_mem_toSubmodule g hseed

private theorem tensorEquiv_apply_action {a b : Fin n → Factor}
    (e : (tensorRep F K a).Equiv (tensorRep F K b)) (g : Model F)
    (v : TensorSpace F K a) :
    e (tensorRep F K a g v) = tensorRep F K b g (e v) :=
  LinearMap.congr_fun (e.isIntertwining' g) v

/-- Unipotent highest-line uniqueness forces a genuine equivalence to carry the
specified highest vector to a nonzero scalar multiple. -/
theorem tensorEquiv_highestVector_scalar {a b : Fin n → Factor}
    (hfixed : ∀ v : TensorSpace F K b,
      (∀ g ∈ (unipotent : Subgroup (Model F)), tensorRep F K b g v = v) →
        ∃ c : K, v = c • tensorHighestVector F K b)
    (e : (tensorRep F K a).Equiv (tensorRep F K b)) :
    ∃ c : K, c ≠ 0 ∧ e (tensorHighestVector F K a) = c • tensorHighestVector F K b := by
  obtain ⟨c, hc⟩ := hfixed (e (tensorHighestVector F K a)) (by
    intro g hg
    rw [← tensorEquiv_apply_action, tensorHighestVector_fixed_unipotent F K a g hg])
  refine ⟨c, ?_, hc⟩
  intro hc0
  rw [hc0, zero_smul] at hc
  exact tensorHighestVector_ne_zero F K a (e.toLinearEquiv.map_eq_zero_iff.mp hc)

/-- With highest-line uniqueness, actual intertwining preserves both the torus
character and whether each integral weight is zero. -/
theorem tensorEquiv_weight_data {a b : Fin n → Factor}
    (hfixed : ∀ v : TensorSpace F K b,
      (∀ g ∈ (unipotent : Subgroup (Model F)), tensorRep F K b g v = v) →
        ∃ c : K, v = c • tensorHighestVector F K b)
    (e : (tensorRep F K a).Equiv (tensorRep F K b)) (s : Bool) :
    (∀ t : Fˣ, (t : F) ^ wordWeight s (List.ofFn a) =
      (t : F) ^ wordWeight s (List.ofFn b)) ∧
    (wordWeight s (List.ofFn a) = 0 ↔ wordWeight s (List.ofFn b) = 0) := by
  obtain ⟨c, hc0, hc⟩ := tensorEquiv_highestVector_scalar hfixed e
  constructor
  · intro t
    have hh := tensorEquiv_apply_action e (simpleCoroot F s t) (tensorHighestVector F K a)
    rw [tensorHighestVector_simpleCoroot, map_smul, hc, map_smul,
      tensorHighestVector_simpleCoroot, smul_smul, smul_smul] at hh
    have hs := smul_left_injective K (tensorHighestVector_ne_zero F K b) hh
    have he := mul_right_cancel₀ hc0 (by simpa only [mul_comm c] using hs)
    apply (algebraMap F K).injective
    simpa only [map_pow] using he
  · rw [← tensorHighestVector_reflection_iff F K a s,
      ← tensorHighestVector_reflection_iff F K b s]
    have hinj : Function.Injective e := e.toLinearEquiv.injective
    rw [← hinj.eq_iff, tensorEquiv_apply_action, hc, map_smul]
    exact smul_right_injective (TensorSpace F K b) hc0 |>.eq_iff

/-- The concrete words are distinct as soon as their unipotent fixed spaces
are proved to be the specified highest lines. No simplicity or class count is
assumed here, and Weyl action separates all boundary weights. -/
theorem tensorRep_equiv_imp_eq_of_fixedLine (hF : Nat.card F = 2 ^ n)
    (hfixed : ∀ (w : Fin n → Factor) (v : TensorSpace F K w),
      (∀ g ∈ (unipotent : Subgroup (Model F)), tensorRep F K w g v = v) →
        ∃ c : K, v = c • tensorHighestVector F K w)
    {a b : Fin n → Factor}
    (he : Nonempty ((tensorRep F K a).Equiv (tensorRep F K b))) : a = b := by
  obtain ⟨e⟩ := he
  have hweight (s : Bool) : wordWeight s (List.ofFn a) = wordWeight s (List.ofFn b) := by
    obtain ⟨hchars, hzero⟩ := tensorEquiv_weight_data (hfixed b) e s
    have ha : wordWeight s (List.ofFn a) < Nat.card F := by
      simpa only [List.length_ofFn, hF] using wordWeight_lt_two_pow_length s (List.ofFn a)
    have hb : wordWeight s (List.ofFn b) < Nat.card F := by
      simpa only [List.length_ofFn, hF] using wordWeight_lt_two_pow_length s (List.ofFn b)
    by_cases ha0 : wordWeight s (List.ofFn a) = 0
    · rw [ha0, hzero.mp ha0]
    have hb0 : wordWeight s (List.ofFn b) ≠ 0 := fun h => ha0 (hzero.mpr h)
    obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := Fˣ)
    have ho : orderOf t = Nat.card F - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers ht, Nat.card_units]
    have heq : t ^ wordWeight s (List.ofFn a) = t ^ wordWeight s (List.ofFn b) :=
      Units.ext (by simpa only [Units.val_pow_eq_pow_val] using hchars t)
    have heq' : t ^ (wordWeight s (List.ofFn a) - 1) =
        t ^ (wordWeight s (List.ofFn b) - 1) := by
      apply mul_right_cancel (b := t)
      simpa only [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ wordWeight s (List.ofFn a)),
        Nat.sub_add_cancel (by omega : 1 ≤ wordWeight s (List.ofFn b))] using heq
    have h := pow_injOn_Iio_orderOf (x := t)
      (show wordWeight s (List.ofFn a) - 1 < orderOf t by rw [ho]; omega)
      (show wordWeight s (List.ofFn b) - 1 < orderOf t by rw [ho]; omega) heq'
    omega
  exact List.ofFn_injective (wordWeight_pair_injective (List.ofFn a) (List.ofFn b)
    (by simp) hweight)

/-- The highest vector generates every concrete G₂ Frobenius tensor, including
all-trivial words and all boundary weights. -/
theorem tensorHighestVector_orbit_span [CharP K 2]
    (hF : Nat.card F = 2 ^ n) (w : Fin n → Factor) :
    Submodule.span K (Set.range fun g : Model F =>
      tensorRep F K w g (tensorHighestVector F K w)) = ⊤ :=
  tensorHighestVector_orbit_span_of_fixedLine hF w
    (tensor_fixed_unipotent F K hF w)

/-- Every concrete G₂ Frobenius tensor is irreducible over every coefficient
extension in characteristic two. No restriction on the word or its degree,
algebraic-closure assumption, or class-count bound is needed. -/
theorem tensorRep_irreducible [CharP K 2]
    (hF : Nat.card F = 2 ^ n) (w : Fin n → Factor) :
    Representation.IsIrreducible (tensorRep F K w) :=
  tensorRep_irreducible_of_fixedLine_and_span hF w
    (tensor_fixed_unipotent F K hF w) (tensorHighestVector_orbit_span hF w)

/-- Genuine equivalence of the concrete G₂ Frobenius tensors recovers every
restricted factor. Weyl action distinguishes zero from `q - 1`, so the result
includes all boundary weights and the all-trivial word. -/
theorem tensorRep_equiv_imp_eq (hF : Nat.card F = 2 ^ n)
    {a b : Fin n → Factor}
    (he : Nonempty ((tensorRep F K a).Equiv (tensorRep F K b))) : a = b :=
  tensorRep_equiv_imp_eq_of_fixedLine hF (tensor_fixed_unipotent F K hF) he

end Atlas.G2.TensorClassification
end
