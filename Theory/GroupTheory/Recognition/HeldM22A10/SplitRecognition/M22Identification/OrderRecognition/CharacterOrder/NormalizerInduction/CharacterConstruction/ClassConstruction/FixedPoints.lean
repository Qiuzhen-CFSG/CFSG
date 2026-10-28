module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.Classes
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.Quotient
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Fixed vectors and lifting conjugacy in the actual normalizer

Conjugation on the actual elementary subgroup distinguishes classes meeting
an involution centralizer from classes acting without nonidentity fixed vectors.
For a fixed-point-free element, the commutator map on E is surjective. Therefore
its E-coset is one E-conjugacy class, and conjugacy in the actual A6 quotient
lifts to conjugacy inside N(E). All maps retain the original marking.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 5, pp.9–10.
-/

open Subgroup
noncomputable section
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer)

/-- Existence of a nonidentity fixed vector in the actual E. -/
@[expose] public def normalizerHasFixedVector (x : normalizer (CaseII.E D k : Set G)) : Prop :=
  ∃ v : CaseII.E D k, v ≠ 1 ∧ normalizerConjugation D k x v = v

public theorem normalizer_fixedPointFree_iff (x : normalizer (CaseII.E D k : Set G)) :
    MonoidHom.FixedPointFree (normalizerConjugation D k x) ↔
      ¬ normalizerHasFixedVector D k x := by
  simp only [MonoidHom.FixedPointFree, normalizerHasFixedVector, not_exists, not_and]
  constructor
  · intro h v hv hf
    exact hv (h v hf)
  · intro h v hf
    by_contra hv
    exact h v hv hf

public theorem normalizerHasFixedVector_isConj
    {x y : normalizer (CaseII.E D k : Set G)} (h : IsConj x y) :
    normalizerHasFixedVector D k x ↔ normalizerHasFixedVector D k y := by
  suffices hs : ∀ {x y : normalizer (CaseII.E D k : Set G)}, IsConj x y →
      normalizerHasFixedVector D k x → normalizerHasFixedVector D k y from
    ⟨hs h, hs h.symm⟩
  intro x y hxy ⟨v, hv, hf⟩
  obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
  refine ⟨normalizerConjugation D k g v, ?_, ?_⟩
  · exact fun he => hv ((normalizerConjugation D k g).injective
      (he.trans (map_one _).symm))
  · simp only [map_mul, map_inv, MulAut.mul_apply, MulAut.inv_apply,
      MulEquiv.symm_apply_apply, hf]

variable [Finite G]

public theorem normalizerCentralizer_hasFixedVector (x : TwistedModel) :
    normalizerHasFixedVector D k (normalizerCentralizer D k x) := by
  let v := normalizerVector D k (Multiplicative.ofAdd ![1, 1, 1, 1])
  have hv : (v : G) = D.z := CaseII.into_z_zero D k
  refine ⟨v, ?_, ?_⟩
  · intro h
    exact D.z_ne_one (hv.symm.trans (congrArg Subtype.val h))
  · apply Subtype.ext
    rw [normalizerConjugation_apply, hv]
    have hx : (normalizerCentralizer D k x : G) * D.z =
        D.z * (normalizerCentralizer D k x : G) :=
      mem_centralizer_singleton_iff.mp (k x).property
    rw [hx, mul_inv_cancel_right]

variable (K : Subgroup (normalizer (CaseII.E D k : Set G)))
    (hK : ((CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G))).IsComplement' K)
    (eK : K ≃* alternatingGroup (Fin 6))

omit [Finite G] in
/-- The quotient has exactly the same fibers as the actual action on E. -/
public theorem normalizerConjugation_eq_iff_quotient_eq (L : LocalAnalysisData D k)
    (x y : normalizer (CaseII.E D k : Set G)) :
    normalizerConjugation D k x = normalizerConjugation D k y ↔
      normalizerQuotient D k K hK eK x = normalizerQuotient D k K hK eK y := by
  rw [MonoidHom.eq_iff, MonoidHom.eq_iff, normalizerConjugation_ker D k L,
    normalizerQuotient_ker]

public theorem normalizer_isConj_of_quotient_eq
    (x y : normalizer (CaseII.E D k : Set G))
    (hx : ¬ normalizerHasFixedVector D k x)
    (hxy : normalizerQuotient D k K hK eK x = normalizerQuotient D k K hK eK y) :
    IsConj x y := by
  have hm : y / x ∈ (CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G)) := by
    rw [← normalizerQuotient_ker D k K hK eK]
    change normalizerQuotient D k K hK eK (y / x) = 1
    rw [map_div, hxy, div_self']
  let w : CaseII.E D k := ⟨(y / x : normalizer (CaseII.E D k : Set G)), hm⟩
  obtain ⟨v, hv⟩ := ((normalizer_fixedPointFree_iff D k x).mpr hx).commutatorMap_surjective w
  let n : normalizer (CaseII.E D k : Set G) := ⟨v, (CaseII.E D k).le_normalizer v.property⟩
  apply isConj_iff.mpr
  refine ⟨n, ?_⟩
  apply Subtype.ext
  have he := congrArg (fun t : CaseII.E D k => (t : G)) hv
  change (v : G) / ((x : G) * v * (x : G)⁻¹) = (y : G) / x at he
  change (v : G) * x * (v : G)⁻¹ = (y : G)
  calc
    _ = ((v : G) / ((x : G) * v * (x : G)⁻¹)) * x := by
      simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
      group
    _ = (y : G) := by rw [he, div_mul_cancel]

public theorem normalizer_isConj_iff_quotient_of_noFixedVector
    (x y : normalizer (CaseII.E D k : Set G))
    (hx : ¬ normalizerHasFixedVector D k x) :
    IsConj x y ↔ IsConj (normalizerQuotient D k K hK eK x)
      (normalizerQuotient D k K hK eK y) := by
  constructor
  · exact (normalizerQuotient D k K hK eK).map_isConj
  · intro h
    obtain ⟨q, hq⟩ := isConj_iff.mp h
    obtain ⟨g, rfl⟩ := normalizerQuotient_surjective D k K hK eK q
    have he : normalizerQuotient D k K hK eK x =
        normalizerQuotient D k K hK eK (g⁻¹ * y * g) := by
      rw [map_mul, map_mul, map_inv, ← hq]
      group
    have hc := normalizer_isConj_of_quotient_eq D k K hK eK x (g⁻¹ * y * g) hx he
    apply hc.trans
    exact isConj_iff.mpr ⟨g, by group⟩

include hK eK in
/-- Every fixed-point-free element is conjugate into the actual complement. -/
public theorem normalizer_conjugate_into_complement_of_noFixedVector
    (x : normalizer (CaseII.E D k : Set G))
    (hx : ¬ normalizerHasFixedVector D k x) :
    ∃ t : K, IsConj x (t : normalizer (CaseII.E D k : Set G)) := by
  obtain ⟨⟨v, t⟩, ht⟩ := hK.2 x
  refine ⟨t, normalizer_isConj_of_quotient_eq D k K hK eK x t hx ?_⟩
  have hv : normalizerQuotient D k K hK eK v = 1 := by
    change (v : normalizer (CaseII.E D k : Set G)) ∈
      (normalizerQuotient D k K hK eK).ker
    rw [normalizerQuotient_ker]
    exact v.property
  rw [← ht, map_mul, hv, one_mul]

omit [Finite G] in
/-- The order of a fixed-point-free element is unchanged in the A6 quotient. -/
public theorem normalizer_order_eq_quotient_of_noFixedVector
    (x : normalizer (CaseII.E D k : Set G))
    (hx : ¬ normalizerHasFixedVector D k x) :
    orderOf x = orderOf (normalizerQuotient D k K hK eK x) := by
  let n := orderOf (normalizerQuotient D k K hK eK x)
  have hm : x ^ n ∈ (CaseII.E D k).subgroupOf (normalizer (CaseII.E D k : Set G)) := by
    rw [← normalizerQuotient_ker D k K hK eK]
    change normalizerQuotient D k K hK eK (x ^ n) = 1
    rw [map_pow]
    exact pow_orderOf_eq_one _
  let v : CaseII.E D k := ⟨((x ^ n : normalizer (CaseII.E D k : Set G)) : G), hm⟩
  have hf : normalizerConjugation D k x v = v := by
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr ((Commute.refl (x : G)).pow_right n).eq
  have h1 : v = 1 := (normalizer_fixedPointFree_iff D k x).mpr hx v hf
  have hp : x ^ n = 1 := by
    apply Subtype.ext
    exact congrArg (fun t : CaseII.E D k => (t : G)) h1
  exact Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one hp)
    (orderOf_map_dvd (normalizerQuotient D k K hK eK) x)

/-- The nine marked representatives with a nonidentity fixed vector. -/
@[expose] public def normalizerFixedRepresentative :
    Fin 9 → normalizer (CaseII.E D k : Set G) := fun i =>
  normalizerCentralizer D k
    (![CaseII.z 0, CaseII.c * CaseII.z 0, CaseII.z 1 * CaseII.b * CaseII.d,
      CaseII.z 3 * CaseII.a, CaseII.z 1 * CaseII.d, 1, CaseII.a, CaseII.c,
      CaseII.b * CaseII.d] i)

/-- The three prospective classes acting without nonidentity fixed vectors. -/
@[expose] public def normalizerFreeRepresentative
    (c₁ μ : normalizer (CaseII.E D k : Set G)) :
    Fin 3 → normalizer (CaseII.E D k : Set G) := ![c₁, μ, μ ^ 2]

/-- Positions of the fixed-vector representatives in the published table. -/
@[expose] public def normalizerFixedIndex : Fin 9 → Fin 12 := ![0, 1, 2, 3, 4, 5, 6, 7, 9]

/-- Positions of the other three representatives in the published table. -/
@[expose] public def normalizerFreeIndex : Fin 3 → Fin 12 := ![8, 10, 11]

omit [Finite G] in
public theorem normalizerFullRepresentative_fixed
    (c₁ μ : normalizer (CaseII.E D k : Set G)) (i : Fin 9) :
    normalizerFullRepresentative D k c₁ μ (normalizerFixedIndex i) =
      normalizerFixedRepresentative D k i := by
  fin_cases i <;> try rfl
  exact (map_one (normalizerCentralizer D k)).symm

omit [Finite G] in
public theorem normalizerFullRepresentative_free
    (c₁ μ : normalizer (CaseII.E D k : Set G)) (i : Fin 3) :
    normalizerFullRepresentative D k c₁ μ (normalizerFreeIndex i) =
      normalizerFreeRepresentative D k c₁ μ i := by
  fin_cases i <;> rfl

public theorem normalizerIndex_cases (i : Fin 12) :
    (∃ j, i = normalizerFixedIndex j) ∨ ∃ j, i = normalizerFreeIndex j := by
  revert i
  decide +kernel

public theorem normalizerFixedRepresentative_hasFixedVector (i : Fin 9) :
    normalizerHasFixedVector D k (normalizerFixedRepresentative D k i) :=
  normalizerCentralizer_hasFixedVector D k _

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
