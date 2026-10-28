module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.HigherLinear.ExceptionalAction.Permutation
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.Transport


/-!
# Transporting the exceptional centralizer actions

The actual component equivalences restrict to ambient fixed subgroups.
In the j₂ marking an automorphism fixing the entire inner centralizer is
identity or the marked involution. In the exceptional outer marking, the
unique central involution of the fixed subgroup is fixed by every element
of the ambient normalizer commuting with the actor. The proof restricts
actual conjugation to that fixed subgroup and transports its center.

Changing a marking uses an actual S₈ conjugator and preserves the action.
Source: Aschbacher–Smith, 16.1.4(3),(9) and the comparison in 16.4.11(2),
combined manuscript (1 March 2004), printed pp.1171 and 1193.
-/

@[expose] public section

open Subgroup Equiv
open Theory.SpecificGroups.SymmetricEight.Involutions
open CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta
open CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.HigherLinear.ExceptionalAction.Transport
open CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.HigherLinear.ExceptionalAction.Permutation

variable {G : Type*} [Group G] {H : Subgroup G} {t : G}

/-- The actual fixed-point membership test under the marked model. -/
theorem fixed_iff (e : H ≃* A) (ht : t ∈ normalizer (H : Set G))
    {q : S} (hm : automorphismPermutationEquiv e (action ht) = q) (x : H) :
    (e x).val ∈ evenCentralizer q ↔ (x : G) ∈ centralizer ({t} : Set G) := by
  have he := automorphismPermutationEquiv_action e (action ht) x
  rw [hm] at he
  have hf : action ht x = x ↔ (x : G) ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have hh := congrArg Subtype.val hx
      change t * (x : G) * t⁻¹ = x at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hx
      apply Subtype.ext
      change t * (x : G) * t⁻¹ = x
      rw [← hx, mul_inv_cancel_right]
  constructor
  · intro hx
    apply hf.mp
    apply e.injective
    apply Subtype.ext
    rw [he, ← mem_centralizer_singleton_iff.mp hx.2, mul_inv_cancel_right]
  · intro hx
    refine ⟨(e x).property, mem_centralizer_singleton_iff.mpr ?_⟩
    rw [hf.mpr hx] at he
    exact eq_mul_inv_iff_mul_eq.mp he

/-- The chosen eight-point model restricts to the actual ambient centralizer. -/
noncomputable def centralizerEquiv (e : H ≃* A) (ht : t ∈ normalizer (H : Set G))
    {q : S} (hm : automorphismPermutationEquiv e (action ht) = q) :
    (H ⊓ centralizer ({t} : Set G) : Subgroup G) ≃* evenCentralizer q where
  toFun x := ⟨(e ⟨x.val, x.property.1⟩).val,
    (fixed_iff e ht hm _).mpr x.property.2⟩
  invFun y := ⟨(e.symm ⟨y.val, y.property.1⟩).val,
    (e.symm ⟨y.val, y.property.1⟩).property,
    (fixed_iff e ht hm _).mp (by simpa only [e.apply_symm_apply] using y.property)⟩
  left_inv x := by
    apply Subtype.ext
    change (e.symm (e ⟨x.val, x.property.1⟩)).val = x.val
    exact congrArg Subtype.val (e.symm_apply_apply _)
  right_inv y := by
    apply Subtype.ext
    change (e (e.symm ⟨y.val, y.property.1⟩)).val = y.val
    exact congrArg Subtype.val (e.apply_symm_apply _)
  map_mul' x y := by
    apply Subtype.ext
    change (e ((⟨x.val, x.property.1⟩ : H) * ⟨y.val, y.property.1⟩)).val = _
    exact congrArg Subtype.val (e.map_mul _ _)

/-- An automorphism fixing the inner centralizer is identity or the marked actor. -/
theorem fixing_inner (e : H ≃* A) (ht : t ∈ normalizer (H : Set G))
    (hm : automorphismPermutationEquiv e (action ht) = twoPairs)
    (b : MulAut H) (hb : ∀ x : H, (x : G) ∈ centralizer ({t} : Set G) → b x = x) :
    b = 1 ∨ b = action ht := by
  have hc : automorphismPermutationEquiv e b ∈
      centralizer (evenCentralizer twoPairs : Set S) := by
    intro y hy
    let x : H := e.symm ⟨y, hy.1⟩
    have hx : (x : G) ∈ centralizer ({t} : Set G) :=
      (fixed_iff e ht hm x).mp (by simpa [x] using hy)
    have he := automorphismPermutationEquiv_action e b x
    rw [hb x hx] at he
    have hex : (e x).val = y := congrArg Subtype.val (e.apply_symm_apply _)
    rw [hex] at he
    exact eq_mul_inv_iff_mul_eq.mp he
  rcases inner_centralizer hc with h | h
  · exact Or.inl ((automorphismPermutationEquiv e).injective (h.trans (map_one _).symm))
  · exact Or.inr ((automorphismPermutationEquiv e).injective (h.trans hm.symm))

/-- The exceptional centralizer contains a characteristic involution. Its
ambient value is retained, so normalizers act on this actual element. -/
theorem outer_characteristic_involution (e : H ≃* A)
    (ht : t ∈ normalizer (H : Set G))
    (hm : automorphismPermutationEquiv e (action ht) = threePairs) :
    ∃ v : G, v ∈ H ⊓ centralizer ({t} : Set G) ∧ v ≠ 1 ∧ v ^ 2 = 1 ∧
      ∀ x ∈ normalizer (H : Set G) ⊓ centralizer ({t} : Set G), x * v = v * x := by
  let J := H ⊓ centralizer ({t} : Set G)
  let f := centralizerEquiv e ht hm
  let w : evenCentralizer threePairs := ⟨outerCentral, outerCentral_mem⟩
  have hw : w ∈ center (evenCentralizer threePairs) := by
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact outerCentral_centralizes x.val x.property
  have hw1 : w ≠ 1 := fun h => outerCentral_ne_one (congrArg Subtype.val h)
  have hw2 : w ^ 2 = 1 := Subtype.ext outerCentral_square
  have huniq (a : evenCentralizer threePairs) (ha : a ∈ center _) : a = 1 ∨ a = w := by
    have hc : a.val ∈ centralizer (evenCentralizer threePairs : Set S) := by
      intro x hx
      exact congrArg Subtype.val (mem_center_iff.mp ha ⟨x, hx⟩)
    exact (outer_center a.property.1 hc).imp Subtype.ext Subtype.ext
  let v : J := f.symm w
  have hv1 : v ≠ 1 := by
    intro hv
    exact hw1 (by simpa [v] using congrArg f hv)
  refine ⟨v.val, v.property, (fun h => hv1 (Subtype.ext h)), ?_, ?_⟩
  · exact congrArg Subtype.val (show v ^ 2 = 1 by
      apply f.injective
      simpa [v] using hw2)
  · intro x hx
    have hxJ : x ∈ normalizer (J : Set G) := inf_normalizer_le_normalizer_inf
      ⟨hx.1, (centralizer ({t} : Set G)).le_normalizer hx.2⟩
    let a := J.normalizerMonoidHom ⟨x, hxJ⟩
    have hvC : v ∈ center J := ((centerCongr f).symm ⟨w, hw⟩).property
    have haC : a v ∈ center J := (centerCongr a ⟨v, hvC⟩).property
    rcases huniq (f (a v)) ((centerCongr f ⟨a v, haC⟩).property) with hzero | heq
    · have hh : a v = 1 := f.injective (hzero.trans f.map_one.symm)
      exact (hv1 (a.injective (hh.trans a.map_one.symm))).elim
    · have hh : a v = v := f.injective (heq.trans (f.apply_symm_apply w).symm)
      have he := congrArg Subtype.val hh
      change x * v.val * x⁻¹ = v.val at he
      exact mul_inv_eq_iff_eq_mul.mp he

/-- Re-mark the same component by a permutation conjugator. -/
theorem mark_of_cycleType {K : Type*} [Group K] (e : K ≃* A) (a : MulAut K) (q : S)
    (hc : (automorphismPermutationEquiv e a).cycleType = q.cycleType) :
    ∃ f : K ≃* A, automorphismPermutationEquiv f a = q := by
  obtain ⟨s, hs⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr hc)
  refine ⟨e.trans (permutationAutEquiv s), ?_⟩
  rw [← hs]
  apply permutationAutEquiv.injective
  have he (f : K ≃* A) : permutationAutEquiv (automorphismPermutationEquiv f a) =
      MulAut.congr f a := permutationAutEquiv.apply_symm_apply _
  rw [he, map_mul, map_mul, map_inv, he]
  ext x
  rfl

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.HigherLinear.ExceptionalAction.Transport
