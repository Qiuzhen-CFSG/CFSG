module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.Model
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.TensorWindow.HalfTensor.SchurDescent

/-!
# Recognition of the half-field natural G₂ tensor

A faithful irreducible binary representation of degree `18*r` has Schur degree
`s` with `r = 2*s`, and its extension over the Schur field has dimension 36.
The actual tensor classification and its Frobenius-period theorem identify
its restricted word as two copies of a length-`s` block. The block degree is
six, so it contains exactly one natural letter.

Tensor associativity and the tensor-unit intertwiners remove the trivial
letters. Base change then gives the exact published `pairRep`, with twists
at positions `i` and `i+s`, where `i<s`. No group automorphism or additional
recognition premise is inserted. This discharges the pair-realization input
of the parent half-tensor displacement assembly; the operator estimate is
separate.

The local single-letter lemmas follow the proofs in `TensorDescent` and
`TensorClassification.SpecialWords`, keeping those shared modules unchanged.
Source: Guralnick–Malle, Classification of 2F-modules II, §3.5 and Lemma 8.5,
manuscript pp.20,55–56; see `G2CubicDegree/Source.md`.
-/

open scoped TensorProduct MonoidAlgebra
public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
open Atlas.G2 Atlas.G2.Restricted Atlas.G2.TensorClassification

private theorem one_natural_of_degree_six {n : ℕ} (w : Fin n → Factor)
    (hw : (∏ i, (w i).dimension) = 6) :
    ∃ i, w i = .natural ∧ ∀ j, j ≠ i → w j = .trivial := by
  classical
  have hd (i : Fin n) : (w i).dimension ∣ 6 := by
    rw [← hw]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hi (i : Fin n) : w i = .trivial ∨ w i = .natural := by
    have h := hd i
    cases hwi : w i <;> simp_all [Factor.dimension]
  have hn : ∃ i, w i = .natural := by
    by_contra! h
    have ht : ∀ i, w i = .trivial := fun i => (hi i).resolve_right (h i)
    have hh := (tensorDegree_eq_one_iff w).mpr ht
    omega
  obtain ⟨i, hwi⟩ := hn
  refine ⟨i, hwi, ?_⟩
  have he : (∏ j ∈ Finset.univ.erase i, (w j).dimension) = 1 := by
    have h := Finset.prod_erase_mul (s := Finset.univ) (f := fun j => (w j).dimension)
      (Finset.mem_univ i)
    rw [hwi, Factor.dimension, hw] at h
    omega
  intro j hji
  have hj : (w j).dimension ∣ 1 := by
    rw [← he]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  cases hwj : w j <;> simp_all [Factor.dimension]

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

private theorem ofFn_eq_double {n s : ℕ} (hn : 0 < n) (hns : n = 2 * s)
    (w : Fin n → Factor)
    (hp : ∀ j, periodicWord hn w (j + s) = periodicWord hn w j) :
    List.ofFn w = List.ofFn (fun i : Fin s => periodicWord hn w i) ++
      List.ofFn (fun i : Fin s => periodicWord hn w i) := by
  apply List.ext_getElem
  · simp [hns, two_mul]
  · intro j hj hk
    have hjn : j < n := by simpa only [List.length_ofFn] using hj
    by_cases hjs : j < s
    · rw [List.getElem_append_left (by simpa using hjs)]
      simp only [List.getElem_ofFn, periodicWord, Nat.mod_eq_of_lt hjn]
    · rw [List.getElem_append_right (by simpa using Nat.le_of_not_gt hjs)]
      simp only [List.length_ofFn, List.getElem_ofFn]
      have h := hp (j - s)
      rw [Nat.sub_add_cancel (by omega : s ≤ j)] at h
      simpa only [periodicWord, Nat.mod_eq_of_lt hjn] using h

private theorem half_word_shape {n s : ℕ} (hn : 0 < n) (hns : n = 2 * s)
    (w : Fin n → Factor)
    (hp : ∀ j, periodicWord hn w (j + s) = periodicWord hn w j)
    (hd : (∏ i, (w i).dimension) = 36) :
    ∃ i : ℕ, i < s ∧
      let l := List.replicate i Factor.trivial ++
        Factor.natural :: List.replicate (s - i - 1) Factor.trivial
      List.ofFn w = l ++ l := by
  let b : Fin s → Factor := fun i => periodicWord hn w i
  have he : List.ofFn w = List.ofFn b ++ List.ofFn b := ofFn_eq_double hn hns w hp
  have hdeg : wordDegree (List.ofFn w) = 36 := by
    simpa only [wordDegree, List.map_ofFn, List.prod_ofFn, Function.comp_apply] using hd
  have hb : (∏ i, (b i).dimension) = 6 := by
    rw [he, wordDegree, List.map_append, List.prod_append,
      List.map_ofFn, List.prod_ofFn] at hdeg
    simp only [Function.comp_apply] at hdeg
    apply Nat.pow_left_injective (by decide : 2 ≠ 0)
    simpa only [pow_two, Nat.reduceMul] using hdeg
  obtain ⟨i, hi, ht⟩ := one_natural_of_degree_six b hb
  refine ⟨i.val, i.isLt, ?_⟩
  rw [he, ofFn_one_natural b i hi ht]

variable (F : Type*) [Field F] [Finite F] [CharP F 2]
  (K : Type*) [Field K] [Algebra F K]

private def wordAppendEquiv (r : ℕ) (l m : List Factor) :
    (wordRep F r (l ++ m)).Equiv
      ((wordRep F r l).tprod (wordRep F (r + l.length) m)) := by
  induction l generalizing r with
  | nil => exact (Representation.TensorProduct.lid F (wordRep F r m)).symm
  | cons a l ih =>
    change ((factorRep F r a).tprod (wordRep F (r + 1) (l ++ m))).Equiv
      (((factorRep F r a).tprod (wordRep F (r + 1) l)).tprod
        (wordRep F (r + (l.length + 1)) m))
    exact (tensorEquiv (Representation.Equiv.refl _) (ih (r + 1))).trans
      (by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 l.length] using
        (Representation.TensorProduct.assoc (factorRep F r a)
          (wordRep F (r + 1) l) (wordRep F (r + 1 + l.length) m)).symm)

private def naturalWordExtendEquiv (r i j : ℕ) :
    (Representation.extendScalars K (wordRep F r
      (List.replicate i .trivial ++ .natural :: List.replicate j .trivial))).Equiv
        (naturalTwist F K (r + i)) := by
  let e := extendEquiv F K ((oneFactorEquiv F r i j .natural).trans
    (naturalFactorEquiv F (r + i)))
  exact .mk e.toLinearEquiv (fun g => e.isIntertwining' g)

private def doubleNaturalEquiv (s i : ℕ) (hi : i < s) :
    let l := List.replicate i Factor.trivial ++
      Factor.natural :: List.replicate (s - i - 1) Factor.trivial
    (Representation.extendScalars K (wordRep F 0 (l ++ l))).Equiv (pairRep F K i s) := by
  let l := List.replicate i Factor.trivial ++
    Factor.natural :: List.replicate (s - i - 1) Factor.trivial
  have hlen : l.length = s := by
    simp only [l, List.length_append, List.length_replicate, List.length_cons]
    omega
  let e := (extendEquiv F K (wordAppendEquiv F 0 l l)).trans
    (tensorBaseChangeEquiv F K (wordRep F 0 l) (wordRep F (0 + l.length) l))
  have e1 : (Representation.extendScalars K (wordRep F 0 l)).Equiv
      (naturalTwist F K i) := by
    simpa only [Nat.zero_add] using naturalWordExtendEquiv F K 0 i (s - i - 1)
  have e2 : (Representation.extendScalars K (wordRep F (0 + l.length) l)).Equiv
      (naturalTwist F K (i + s)) := by
    have hpos : 0 + l.length + i = i + s := by omega
    simpa only [hpos] using naturalWordExtendEquiv F K (0 + l.length) i (s - i - 1)
  exact e.trans (tensorEquiv e1 e2)

attribute [local instance] ZMod.algebra
variable {F} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (σ : Representation (ZMod 2) (Atlas.G2.Model F) V) [Representation.IsIrreducible σ]
  [IsAlgClosed K] [CharP K 2]
  [Algebra (Module.End (ZMod 2)[Atlas.G2.Model F] σ.asModule) K]

/-- Recognition of the actual half-field natural pair over any algebraically closed
coefficient field with the two given scalar structures. The intertwiner preserves
the group element and the Frobenius positions `i` and `i+s`. -/
theorem exists_pairRep_equiv {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 18 * r) :
    ∃ i : ℕ, i < Representation.schurDegree 2 σ ∧
      Nonempty ((Representation.extendScalars K σ.endFieldRep).Equiv
        (pairRep F K i (Representation.schurDegree 2 σ))) := by
  let : Representation.IsAbsolutelyIrreducible σ.endFieldRep :=
    Representation.endFieldRep_isAbsolutelyIrreducible σ
  let : Representation.IsIrreducible (Representation.extendScalars K σ.endFieldRep) :=
    Representation.IsAbsolutelyIrreducible.irreducible_of_extension σ.endFieldRep K
  obtain ⟨w, ⟨e⟩⟩ := exists_tensorRep_equiv hF
    (Representation.extendScalars K σ.endFieldRep) inferInstance
  have hn : 0 < r := by omega
  have hp : ∀ j, periodicWord hn w (j + Representation.schurDegree 2 σ) =
      periodicWord hn w j := by
    have h := (tensorModel_frobenius_equiv_iff_degree_period F K hF hn w e
      (Representation.schurDegree 2 σ)).mp
      ((Representation.endFieldRep_frobenius_equiv_iff 2 σ K _).mpr (dvd_refl _))
    exact fun j => Factor.dimension_injective (h j)
  have hdeg : (∏ i, (w i).dimension) = 36 := by
    rw [← finrank_tensorSpace F K w, ← e.toLinearEquiv.finrank_eq]
    exact split_finrank σ hr hF hf hd K
  obtain ⟨i, hi, hw⟩ := half_word_shape hn (twice_schurDegree σ hr hF hf hd) w hp hdeg
  refine ⟨i, hi, ⟨e.trans ?_⟩⟩
  change (Representation.extendScalars K (wordRep F 0 (List.ofFn w))).Equiv _
  rw [hw]
  exact doubleNaturalEquiv F K (Representation.schurDegree 2 σ) i hi

end CFSG.Quasithin.ChapterK.Exceptional.G2CubicDegree.TensorWindow.HalfTensor
