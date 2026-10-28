module

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.RootFrame
public import Mathlib.Algebra.CharP.Two

/-!
# Rigidity of the labelled G₂ root frame in characteristic two

An abstract automorphism preserving the six positive root groups and the two
negative simple root groups is torus times field. First use the two independent
torus characters to fix the simple root elements at parameter one. Rank-one
words and a single matrix entry then force the Weyl generators to be fixed.
The mixed short-long root relation, read in the unique six-parameter unipotent
chart, forces the additive root maps to be one common multiplicative map.
Generation identifies the resulting automorphism with coefficient transport.

No prescribed parameter action is a hypothesis: only the eight subgroup
invariances are assumed. Conjugating an arbitrary automorphism into this root
frame is the separate remaining geometric step in full inner-field coverage.
This coordinate result holds over every field of characteristic two.

Source: the automorphism input used by Aschbacher--Smith F.1.12, printed
pp.263--264, and the root-character convention described in RootDiagonal.
The rank-one and mixed-root identities are from the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Atlas.SplitOctonion Atlas.G2.Explicit
namespace Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
open RootDiagonal
open scoped CharTwo
variable {F : Type*} [Field F] [CharP F 2]

private theorem neg_one_unit : (-1 : Fˣ) = 1 := by
  apply Units.ext
  exact CharTwo.neg_eq (1 : F)

theorem long_word_one :
    rootE (1 : F) * root 6 1 * rootE 1 = weylR := by
  change rootE (1 : F) * (weylR * rootE 1 * weylR⁻¹) * rootE 1 = weylR
  have h := long_rank_one_word (1 : Fˣ)
  simpa only [inv_one, Units.val_one, CharTwo.neg_eq, neg_one_unit,
    torus_identity, one_mul] using h

theorem short_word_one :
    rootF (1 : F) * root 7 1 * rootF 1 = weylS := by
  change rootF (1 : F) * (weylS * rootF 1 * weylS⁻¹) * rootF 1 = weylS
  have h := short_rank_one_word (1 : Fˣ)
  simpa only [inv_one, Units.val_one, CharTwo.neg_eq, neg_one_unit,
    torus_identity, one_mul] using h

private theorem long_word_parameter (b : F)
    (h : (rootE 1 * root 6 b * rootE 1) * rootE 1 *
      (rootE 1 * root 6 b * rootE 1) = root 6 b) : b = 1 := by
  have hh := congrArg (fun g : Model F => g.val (basisVector 2) 1) h
  simp [root, rootE, rootEEquiv, rootELinear, rootEApply,
    weylR, weylREquiv, weylRLinear, weylRApply, basisVector,
    CharTwo.neg_eq, CharTwo.sub_eq_add] at hh
  have he : (b + 1) ^ 2 = 0 := by
    linear_combination (norm := ring_nf) hh
  have hz := (eq_zero_of_pow_eq_zero he)
  have h1 := eq_neg_of_add_eq_zero_left hz
  simpa only [CharTwo.neg_eq] using h1

private theorem short_word_parameter (b : F)
    (h : (rootF 1 * root 7 b * rootF 1) * rootF 1 *
      (rootF 1 * root 7 b * rootF 1) = root 7 b) : b = 1 := by
  have hh := congrArg (fun g : Model F => g.val (basisVector 1) 0) h
  simp [root, rootF, rootFEquiv, rootFLinear, rootFApply,
    weylS, weylSEquiv, weylSLinear, weylSApply, basisVector,
    CharTwo.neg_eq, CharTwo.sub_eq_add] at hh
  have he : (b + 1) ^ 2 = 0 := by
    linear_combination (norm := ring_nf) hh
  have hz := (eq_zero_of_pow_eq_zero he)
  have h1 := eq_neg_of_add_eq_zero_left hz
  simpa only [CharTwo.neg_eq] using h1

theorem normalized_fixes_weyl (a : MulAut (Model F)) (ha : PreservesRootGroups a)
    (hE : a (rootE 1) = rootE 1) (hF : a (rootF 1) = rootF 1) :
    a weylR = weylR ∧ a weylS = weylS := by
  have hR : a weylR = rootE 1 * root 6 (rootParameter a ha 6 1) * rootE 1 := by
    rw [← long_word_one, map_mul, map_mul, hE, apply_rootParameter a ha]
  have hS : a weylS = rootF 1 * root 7 (rootParameter a ha 7 1) * rootF 1 := by
    rw [← short_word_one, map_mul, map_mul, hF, apply_rootParameter a ha]
  constructor
  · have h := congrArg a (show weylR * rootE 1 * weylR = root 6 (1 : F) by
      change _ = weylR * rootE 1 * weylR⁻¹
      rw [weylR_inverse])
    rw [map_mul, map_mul, hR, hE, apply_rootParameter a ha] at h
    rw [long_word_parameter _ h] at hR
    exact hR.trans long_word_one
  · have h := congrArg a (show weylS * rootF 1 * weylS = root 7 (1 : F) by
      change _ = weylS * rootF 1 * weylS⁻¹
      rw [weylS_inverse])
    rw [map_mul, map_mul, hS, hF, apply_rootParameter a ha] at h
    rw [short_word_parameter _ h] at hS
    exact hS.trans short_word_one

omit [CharP F 2] in
private theorem parameters_conjugate (a : MulAut (Model F)) (ha : PreservesRootGroups a)
    (w : Model F) (hw : a w = w) (i j : Fin 8)
    (hij : ∀ t : F, w * root i t * w⁻¹ = root j t) (t : F) :
    rootParameter a ha i t = rootParameter a ha j t := by
  have h := congrArg a (hij t)
  rw [map_mul, map_mul, map_inv, hw, apply_rootParameter a ha,
    apply_rootParameter a ha, hij] at h
  exact root_injective j h

/-- The mixed-root commutator forces the two product laws needed to recover
multiplication in the field, even in characteristic two. -/
theorem parameter_products (a : MulAut (Model F)) (ha : PreservesRootGroups a)
    (s t : F) :
    rootParameter a ha 3 (s * t) = rootParameter a ha 4 s * rootParameter a ha 5 t ∧
    rootParameter a ha 2 (s * t ^ 2) =
      rootParameter a ha 4 s * (rootParameter a ha 5 t) ^ 2 := by
  let f := rootParameter a ha
  have hA (t : F) : a (rootA t) = rootA (f 0 t) := apply_rootParameter a ha 0 t
  have hB (t : F) : a (rootB t) = rootB (f 1 t) := apply_rootParameter a ha 1 t
  have hC (t : F) : a (rootC t) = rootC (f 2 t) := apply_rootParameter a ha 2 t
  have hD (t : F) : a (rootD t) = rootD (f 3 t) := apply_rootParameter a ha 3 t
  have hE (t : F) : a (rootE t) = rootE (f 4 t) := apply_rootParameter a ha 4 t
  have hF (t : F) : a (rootF t) = rootF (f 5 t) := apply_rootParameter a ha 5 t
  have h := congrArg a (rootF_conjugate_rootE s t)
  simp only [map_mul, hA, hB, hC, hD, hE, hF, CharTwo.neg_eq] at h
  have h' := rootF_conjugate_rootE (f 4 s) (f 5 t)
  simp only [CharTwo.neg_eq] at h'
  have hp : unipotentProduct ![f 0 (s ^ 2 * t ^ 3), f 1 (s * t ^ 3),
      f 2 (s * t ^ 2), f 3 (s * t), f 4 s, 0] =
      unipotentProduct ![(f 4 s) ^ 2 * (f 5 t) ^ 3, f 4 s * (f 5 t) ^ 3,
        f 4 s * (f 5 t) ^ 2, f 4 s * f 5 t, f 4 s, 0] := by
    simpa [unipotentProduct] using h.symm.trans h'
  have he := unipotentProduct_injective hp
  exact ⟨congrFun he 3, congrFun he 2⟩

/-- A root-frame automorphism fixing the two simple root elements at parameter
one is the actual coefficientwise action of a field automorphism. -/
theorem normalized_eq_field (a : MulAut (Model F)) (ha : PreservesRootGroups a)
    (hE : a (rootE 1) = rootE 1) (hF : a (rootF 1) = rootF 1) :
    ∃ σ : F ≃+* F, a = fieldAction σ := by
  obtain ⟨hR, hS⟩ := normalized_fixes_weyl a ha hE hF
  let f := rootParameter a ha
  have h41 : f 4 1 = 1 := rootE_injective ((apply_rootParameter a ha 4 1).symm.trans hE)
  have h51 : f 5 1 = 1 := rootF_injective ((apply_rootParameter a ha 5 1).symm.trans hF)
  have h01 (t : F) : f 0 t = f 1 t :=
    parameters_conjugate a ha weylR hR 0 1 weylR_rootA t
  have h14 (t : F) : f 1 t = f 4 t :=
    parameters_conjugate a ha weylS hS 1 4 weylS_rootB t
  have h35 (t : F) : f 3 t = f 5 t :=
    parameters_conjugate a ha weylR hR 3 5 weylR_rootD t
  have hm (s t : F) : f 5 (s * t) = f 4 s * f 5 t :=
    (h35 (s * t)).symm.trans (parameter_products a ha s t).1
  have h54 (t : F) : f 5 t = f 4 t := by
    simpa only [mul_one, h51] using hm t 1
  have h24 (t : F) : f 2 t = f 4 t := by
    have h := (parameter_products a ha t 1).2
    change f 2 (t * 1 ^ 2) = f 4 t * (f 5 1) ^ 2 at h
    simpa only [h51, one_pow, mul_one] using h
  let σ : F ≃+* F :=
    { (f 4).toEquiv with
      map_add' := (f 4).map_add
      map_mul' := fun s t => by
        change f 4 (s * t) = f 4 s * f 4 t
        simpa only [h54] using hm s t }
  refine ⟨σ, ?_⟩
  apply MulEquiv.toMonoidHom_injective
  apply RootDiagonal.hom_ext
  intro i t
  change a (root i t) = fieldAction σ (root i t)
  rw [fieldAction_root]
  have hall (j : Fin 8) (hj : j.val < 6) : f j t = σ t := by
    fin_cases j
    · exact (h01 t).trans (h14 t)
    · exact h14 t
    · exact h24 t
    · exact (h35 t).trans (h54 t)
    · rfl
    · exact h54 t
    · norm_num at hj
    · norm_num at hj
  fin_cases i
  · exact (apply_rootParameter a ha 0 t).trans (congrArg (root 0) (hall 0 (by decide)))
  · exact (apply_rootParameter a ha 1 t).trans (congrArg (root 1) (hall 1 (by decide)))
  · exact (apply_rootParameter a ha 2 t).trans (congrArg (root 2) (hall 2 (by decide)))
  · exact (apply_rootParameter a ha 3 t).trans (congrArg (root 3) (hall 3 (by decide)))
  · exact apply_rootParameter a ha 4 t
  · exact (apply_rootParameter a ha 5 t).trans (congrArg (root 5) (hall 5 (by decide)))
  · change a (weylR * rootE t * weylR⁻¹) = weylR * rootE (σ t) * weylR⁻¹
    have he : a (rootE t) = rootE (σ t) := apply_rootParameter a ha 4 t
    rw [map_mul, map_mul, map_inv, hR, he]
  · change a (weylS * rootF t * weylS⁻¹) = weylS * rootF (σ t) * weylS⁻¹
    have he : a (rootF t) = rootF (σ t) :=
      (apply_rootParameter a ha 5 t).trans (congrArg rootF (h54 t))
    rw [map_mul, map_mul, map_inv, hS, he]

/-- Every automorphism preserving the eight labelled root groups is a product
of an actual torus conjugation and coefficientwise field transport. -/
theorem eq_torus_field_of_preservesRootGroups (a : MulAut (Model F))
    (ha : PreservesRootGroups a) :
    ∃ (u v : Fˣ) (σ : F ≃+* F),
      a = MulAut.conj (torus (u ^ 2 * v) (u * v)) * fieldAction σ := by
  let f := rootParameter a ha
  have hn (i : Fin 8) : f i 1 ≠ 0 := by
    intro h
    have hh : f i 1 = f i 0 := h.trans (map_zero (f i)).symm
    exact one_ne_zero ((f i).injective hh)
  let u : Fˣ := Units.mk0 (f 5 1) (hn 5)
  let v : Fˣ := Units.mk0 (f 4 1) (hn 4)
  let d := MulAut.conj (torus (u ^ 2 * v) (u * v))
  let b := d⁻¹ * a
  have hb : PreservesRootGroups b := (torus_preservesRootGroups u v).inv.mul ha
  have hE : d (rootE 1) = a (rootE 1) := by
    calc
      d (rootE 1) = rootE ((v : F) * 1) := torus_character u v 4 1
      _ = a (rootE 1) := by
        change rootE (f 4 1 * 1) = a (rootE 1)
        rw [mul_one]
        exact (apply_rootParameter a ha 4 1).symm
  have hF : d (rootF 1) = a (rootF 1) := by
    calc
      d (rootF 1) = rootF ((u : F) * 1) := torus_character u v 5 1
      _ = a (rootF 1) := by
        change rootF (f 5 1 * 1) = a (rootF 1)
        rw [mul_one]
        exact (apply_rootParameter a ha 5 1).symm
  have hbE : b (rootE 1) = rootE 1 := by
    change d.symm (a (rootE 1)) = rootE 1
    rw [← hE, MulEquiv.symm_apply_apply]
  have hbF : b (rootF 1) = rootF 1 := by
    change d.symm (a (rootF 1)) = rootF 1
    rw [← hF, MulEquiv.symm_apply_apply]
  obtain ⟨σ, hσ⟩ := normalized_eq_field b hb hbE hbF
  refine ⟨u, v, σ, ?_⟩
  have h := congrArg (fun c => d * c) hσ
  simpa only [b, mul_inv_cancel_left] using h

end Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
