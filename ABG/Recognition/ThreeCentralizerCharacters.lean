module
public import ABG.Basic
public import ABG.Recognition.ThreeCharacterTable
public import Theory.Character.Transport
public import Theory.Character.InvolutionRootInduction

/-!
# Wong's local characters on an actual involution centralizer

The field equivalence GF(3) ≃ ZMod 3 transports the actual matrix table to
any supplied GL₂(3) involution centralizer. The distinguished involution maps
to -I: it is central, and the table of conjugacy classes has only one central
involution. Consequently cyclic root support, the supported Gram matrix, and
its vanishing criterion all transport to the centralizer. Induction preserves
this Gram matrix and Frobenius reciprocity identifies the trivial coefficient.

Source: W. J. Wong, On finite groups whose 2-Sylow subgroups have cyclic
subgroups of index 2 (1964), Lemma 4 and equation (3), p.98; Appendix p.106.
-/

open Matrix Matrix.GeneralLinearGroup BenderGlauberman
open scoped BigOperators
namespace ABG
noncomputable section
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

/-- The coefficient equivalence connecting ABG's field model to the table. -/
public def glTwoThreeFieldEquiv : GL2 3 1 ≃* GL (Fin 2) (ZMod 3) :=
  Units.mapEquiv ((GaloisField.equivZmodP 3).toRingEquiv.mapMatrix (m := Fin 2)).toMulEquiv

private theorem central_involution_eq_threeCentral
    (z : GL (Fin 2) (ZMod 3)) (hz : orderOf z = 2)
    (hc : ∀ g, g * z = z * g) : z = threeCentral := by
  obtain ⟨i, hi, _⟩ := three_conjugacy_data.1 z
  obtain ⟨g, hg⟩ := isConj_iff.mp hi
  have he : z = threeClassRepr i := by
    simpa only [hc g, mul_assoc, mul_inv_cancel, mul_one] using hg
  rw [he, three_conjugacy_data.2.1] at hz
  have hn : threeUnipotent * threeReflection ≠ threeReflection * threeUnipotent := by
    decide +kernel
  fin_cases i <;> norm_num at hz
  · exact he
  · exact (hn (by simpa [he, threeClassRepr] using hc threeUnipotent)).elim

variable {G : Type*} [Group G] [Finite G] (t : G)
local notation "C" => Subgroup.centralizer (Set.singleton t)

/-- The supplied centralizer equivalence, expressed in the concrete table model. -/
public def threeCentralizerEquiv (e : C ≃* GL2 3 1) : C ≃* GL (Fin 2) (ZMod 3) :=
  e.trans glTwoThreeFieldEquiv

omit [Finite G] in
/-- Every centralizer equivalence identifies its distinguished involution with -I. -/
public theorem threeCentralizerEquiv_involution (ht : orderOf t = 2)
    (e : C ≃* GL2 3 1) :
    threeCentralizerEquiv t e ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ =
      threeCentral := by
  let z : C := ⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  apply central_involution_eq_threeCentral
  · exact (orderOf_injective (threeCentralizerEquiv t e).toMonoidHom
      (threeCentralizerEquiv t e).injective z).trans ((Subgroup.orderOf_coe z).symm.trans ht)
  · intro g
    obtain ⟨a, rfl⟩ := (threeCentralizerEquiv t e).surjective g
    rw [← map_mul, ← map_mul]
    apply congrArg (threeCentralizerEquiv t e)
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp a.property

omit [Finite G] in
/-- Cyclic root support agrees with the support used by the concrete table. -/
public theorem threeCentralizerEquiv_root_iff (ht : orderOf t = 2)
    (e : C ≃* GL2 3 1) (a : C) :
    threeCentralizerEquiv t e a ∈ glTwoThreeRootSupport ↔
      t ∈ Subgroup.zpowers (a : G) := by
  change threeCentral ∈ Subgroup.zpowers (threeCentralizerEquiv t e a) ↔ _
  rw [← threeCentralizerEquiv_involution t ht e]
  constructor
  · rintro ⟨n, hn⟩
    have h := (threeCentralizerEquiv t e).injective ((map_zpow (threeCentralizerEquiv t e) a n).trans hn)
    exact ⟨n, congrArg Subtype.val h⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    change (threeCentralizerEquiv t e a) ^ n = _
    rw [← map_zpow]
    exact congrArg (threeCentralizerEquiv t e) (Subtype.ext hn)

/-- The actual eight irreducible characters of the supplied centralizer. -/
@[expose] public def threeCentralizerCharacter (e : C ≃* GL2 3 1) (i : Fin 8) :
    ClassFunction C := fun a => glTwoThreeCharacter i (threeCentralizerEquiv t e a)

public theorem threeCentralizerCharacter_irreducible (e : C ≃* GL2 3 1) (i : Fin 8) :
    IsIrreducibleCharacter (threeCentralizerCharacter t e i) :=
  isIrreducibleCharacter_comp_mulEquiv (threeCentralizerEquiv t e) (glTwoThreeCharacter_irreducible i)

/-- The actual five supported generalized characters of the centralizer. -/
@[expose] public def threeCentralizerGenerator (e : C ≃* GL2 3 1) (k : Fin 5) :
    ClassFunction C := fun a => glTwoThreeSupportedGenerator k (threeCentralizerEquiv t e a)

omit [Finite G] in
public theorem threeCentralizerGenerator_generalized (e : C ≃* GL2 3 1) (k : Fin 5) :
    IsGeneralizedCharacter (threeCentralizerGenerator t e k) :=
  isGeneralizedCharacter_comp_hom (threeCentralizerEquiv t e).toMonoidHom
    (glTwoThreeSupportedGenerator_generalized k)

omit [Finite G] in
public theorem threeCentralizerGenerator_class (e : C ≃* GL2 3 1) (k : Fin 5) :
    IsClassFunction (threeCentralizerGenerator t e k) :=
  isClassFunction_of_isGeneralizedCharacter (threeCentralizerGenerator_generalized t e k)

omit [Finite G] in
public theorem threeCentralizerGenerator_supported (ht : orderOf t = 2)
    (e : C ≃* GL2 3 1) (k : Fin 5) (a : C)
    (ha : t ∉ Subgroup.zpowers (a : G)) : threeCentralizerGenerator t e k a = 0 :=
  glTwoThreeSupportedGenerator_supported k _
    (fun h => ha ((threeCentralizerEquiv_root_iff t ht e a).mp h))

public theorem threeCentralizerGenerator_gram (e : C ≃* GL2 3 1) (k l : Fin 5) :
    scalarProduct C (threeCentralizerGenerator t e k) (threeCentralizerGenerator t e l) =
      ![![3,1,0,-1,1], ![1,2,-1,0,1], ![0,-1,2,0,0],
        ![-1,0,0,3,1], ![1,1,0,1,3]] k l := by
  exact (scalarProduct_comp_mulEquiv (threeCentralizerEquiv t e)
    (glTwoThreeSupportedGenerator k) (glTwoThreeSupportedGenerator l)).trans
      (glTwoThreeSupportedGenerator_gram k l)

/-- The transported table contains every irreducible of the actual centralizer. -/
public theorem threeCentralizerCharacter_complete (e : C ≃* GL2 3 1)
    {χ : ClassFunction C} (hχ : IsIrreducibleCharacter χ) :
    ∃! i : Fin 8, threeCentralizerCharacter t e i = χ := by
  have hi := isIrreducibleCharacter_comp_mulEquiv (threeCentralizerEquiv t e).symm hχ
  obtain ⟨i, hi, hu⟩ := glTwoThreeCharacter_complete hi
  refine ⟨i, ?_, ?_⟩
  · funext a
    simpa [threeCentralizerCharacter] using congrFun hi (threeCentralizerEquiv t e a)
  · intro j hj
    apply hu j
    funext a
    simpa [threeCentralizerCharacter] using congrFun hj ((threeCentralizerEquiv t e).symm a)

omit [Finite G] in
/-- The rows remain distinct on the actual centralizer. -/
public theorem threeCentralizerCharacter_injective (e : C ≃* GL2 3 1) :
    Function.Injective (threeCentralizerCharacter t e) := by
  intro i j hij
  apply glTwoThreeCharacter_injective
  funext a
  simpa [threeCentralizerCharacter] using
    congrFun hij ((threeCentralizerEquiv t e).symm a)

omit [Finite G] in
/-- The exact concrete values, evaluated at the transported class representatives. -/
public theorem threeCentralizerCharacter_values (e : C ≃* GL2 3 1) (i j : Fin 8) :
    threeCentralizerCharacter t e i ((threeCentralizerEquiv t e).symm (threeClassRepr j)) =
      glTwoThreeCharacterTable i j := by
  simp only [threeCentralizerCharacter, MulEquiv.apply_symm_apply, glTwoThreeCharacter_values]

/-- Orthogonality to the five local generators detects vanishing on root support. -/
public theorem threeCentralizer_orthogonal_vanishes (ht : orderOf t = 2)
    (e : C ≃* GL2 3 1) {f : ClassFunction C} (hf : IsClassFunction f)
    (ho : ∀ k : Fin 5, scalarProduct C f (threeCentralizerGenerator t e k) = 0)
    (a : C) (ha : t ∈ Subgroup.zpowers (a : G)) : f a = 0 := by
  have hf' := isClassFunction_comp_hom (threeCentralizerEquiv t e).symm.toMonoidHom hf
  have ho' (k : Fin 5) : scalarProduct (GL (Fin 2) (ZMod 3))
      (fun g => f ((threeCentralizerEquiv t e).symm g))
      (glTwoThreeSupportedGenerator k) = 0 := by
    have h := scalarProduct_comp_mulEquiv (threeCentralizerEquiv t e).symm f
      (threeCentralizerGenerator t e k)
    simpa only [threeCentralizerGenerator, MulEquiv.apply_symm_apply, ho k] using h
  have h := glTwoThree_orthogonal_vanishes hf' ho' (threeCentralizerEquiv t e a)
    ((threeCentralizerEquiv_root_iff t ht e a).mpr ha)
  simpa using h

/-- Wong's five induced generalized characters, with the same local witnesses. -/
@[expose] public def threeInducedGenerator (e : C ≃* GL2 3 1) (k : Fin 5) :
    ClassFunction G := inducedClassFunction C (threeCentralizerGenerator t e k)

public theorem threeInducedGenerator_generalized (e : C ≃* GL2 3 1) (k : Fin 5) :
    IsGeneralizedCharacter (threeInducedGenerator t e k) :=
  isGeneralizedCharacter_induced C (threeCentralizerGenerator_generalized t e k)

public theorem threeInducedGenerator_gram (ht : orderOf t = 2)
    (e : C ≃* GL2 3 1) (k l : Fin 5) :
    scalarProduct G (threeInducedGenerator t e k) (threeInducedGenerator t e l) =
      ![![3,1,0,-1,1], ![1,2,-1,0,1], ![0,-1,2,0,0],
        ![-1,0,0,3,1], ![1,1,0,1,3]] k l := by
  exact (scalarProduct_inducedClassFunction_involutionRoots t ht
    _ _ (threeCentralizerGenerator_class t e l)
    (threeCentralizerGenerator_supported t ht e k)
    (threeCentralizerGenerator_supported t ht e l)).trans
      (threeCentralizerGenerator_gram t e k l)

public theorem threeInducedGenerator_apply_root (ht : orderOf t = 2)
    (e : C ≃* GL2 3 1) (k : Fin 5) (a : C)
    (ha : t ∈ Subgroup.zpowers (a : G)) :
    threeInducedGenerator t e k a = threeCentralizerGenerator t e k a :=
  inducedClassFunction_involutionRoots_apply t ht _ (threeCentralizerGenerator_class t e k)
    (threeCentralizerGenerator_supported t ht e k) a ha

public theorem threeInducedGenerator_one (ht : orderOf t = 2)
    (e : C ≃* GL2 3 1) (k : Fin 5) : threeInducedGenerator t e k 1 = 0 := by
  apply inducedClassFunction_involutionRoots_eq_zero t _
    (threeCentralizerGenerator_supported t ht e k)
  intro g
  simp only [mul_one, inv_mul_cancel, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot]
  intro h
  rw [h, orderOf_one] at ht
  norm_num at ht

public theorem threeInducedGenerator_trivial_coefficient
    (e : C ≃* GL2 3 1) (k : Fin 5) :
    scalarProduct G (threeInducedGenerator t e k) 1 = if k = 0 then 1 else 0 := by
  rw [threeInducedGenerator, scalarProduct_inducedClassFunction C _
    (irreducibleCharacter_isClassFunction isLinearCharacter_one.1)]
  change @scalarProduct C _ (fun a => glTwoThreeSupportedGenerator k (threeCentralizerEquiv t e a))
    (fun a => (1 : ClassFunction (GL (Fin 2) (ZMod 3))) (threeCentralizerEquiv t e a)) = _
  rw [scalarProduct_comp_mulEquiv]
  change scalarProduct _ (glTwoThreeSupportedGenerator k) (glTwoThreeCharacter 0) = _
  fin_cases k <;>
    simp [glTwoThreeSupportedGenerator, scalarProduct_add_left, _root_.scalarProduct_sub_left,
      glTwoThreeCharacter_orthonormal]

/-- Frobenius reciprocity turns absence from all induced generators into local vanishing. -/
public theorem threeInduced_orthogonal_vanishes_on_roots (ht : orderOf t = 2)
    (e : C ≃* GL2 3 1) {χ : ClassFunction G} (hχ : IsClassFunction χ)
    (ho : ∀ k : Fin 5, scalarProduct G χ (threeInducedGenerator t e k) = 0)
    (a : C) (ha : t ∈ Subgroup.zpowers (a : G)) : χ a = 0 := by
  apply threeCentralizer_orthogonal_vanishes t ht e
    (isClassFunction_comp_hom (Subgroup.centralizer ({t} : Set G)).subtype hχ) (fun k => ?_) a ha
  exact (scalarProduct_restrict_induced C hχ _).trans (ho k)

end
end ABG
