module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.Setup
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Consequences of the local and model reductions

The commuting subgroup T_C is Sylow in C_G(L) because T normalizes L.
Once the p.1190 dichotomy has been proved, each surviving alternative forces
T_C = ⟨z⟩: an alternating component is centerless, and the graph-field
alternative supplies precisely the PSL₃(4) quotient map excluded by the
second branch of the dichotomy.

The empty-family result (!) rules out every residual fusion witness. Even
residual order and conjugacy of the involutions in rL construct such a witness.
For the central covers, an element of order four inverted by r conjugates r
to rz; centrality of z then removes a possible z factor from a lifted witness.
The actual model conjugators, quotient lifts and local dichotomy are separate
obligations, not hypotheses asserted to hold by this module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
16.4.9(2), printed pp.1190–1191. All conjugation is left conjugation.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}


/-- The Sylow clause in the first branch of the source dichotomy holds in the standard setup. -/
theorem commutingSylow_sylow (h : StandardSetup T z L) :
    SylowIn (commutingSylow T L) (centralizer (L : Set G)) := by
  let N := normalizer (L : Set G)
  let C := centralizer (L : Set G)
  have hCN : C ≤ N := centralizer_le_normalizer _
  obtain ⟨S, hS⟩ := (T.subtype h.sylow_normalizes).exists_subgroupOf_eq_of_normal
    (C.subgroupOf N)
  let e := subgroupOfEquivOfLe hCN
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS' : (S' : Subgroup C) = (T : Subgroup G).subgroupOf C := by
    change (S : Subgroup _).map e.toMonoidHom = _
    rw [hS]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨⟨x, hCN x.property⟩, x.property⟩, hx, rfl⟩
  refine ⟨S', ?_⟩
  rw [hS']
  exact subgroupOf_map_subtype _ _

omit [Finite G] in
private theorem not_mem_of_alternating (h : CentralComponentSetup T z L)
    {n : ℕ} (hn : 4 ≤ n) (e : L ≃* alternatingGroup (Fin n)) : z ∉ L := by
  intro hz
  have hzC : (⟨z, hz⟩ : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (h.component.1 x.property)
  have heC : e ⟨z, hz⟩ ∈ center (alternatingGroup (Fin n)) :=
    (centerCongr e ⟨⟨z, hz⟩, hzC⟩).property
  rw [alternatingGroup.center_eq_bot (by simpa only [Nat.card_fin] using hn), mem_bot] at heC
  have he : e ⟨z, hz⟩ = e 1 := by simpa only [map_one] using heC
  have hz1 : z = 1 := congrArg Subtype.val (e.injective he)
  have hz2 := h.involution
  simp [hz1] at hz2

/-- The surviving actual models force the first branch of the commuting-Sylow dichotomy. -/
theorem commutingSylow_eq_of_exceptional (h : IntersectionSetup T z L g R)
    (hd : CommutingSylowDichotomy T z L) (he : InnerFamilyExceptionalCase L r) :
    commutingSylow T L = zpowers z := by
  rcases hd with heq | ⟨hzL, hnL3, _⟩
  · exact heq
  · exfalso
    rcases he with ha | hg
    · rcases ha with ha | ha
      · obtain ⟨e⟩ := ha
        exact not_mem_of_alternating h.toCentralComponentSetup (by omega) e hzL
      · obtain ⟨e⟩ := ha
        exact not_mem_of_alternating h.toCentralComponentSetup (by omega) e hzL
    · obtain ⟨_, e, _⟩ := hg
      exact hnL3 ⟨e⟩

/-- The source separation (!) forbids a nonidentity residual fusion witness; residual placement is 16.4.8. -/
theorem no_residualFusionWitness (h : IntersectionSetup T z L g R)
    (hsmall : OrderTwoOutsideDeltaZero L) (hempty : ¬ (deltaZero L).Nonempty)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hres : OuterResidual.involutionResidual L r ≤ L.conjBy g) :
    ¬ ResidualFusionWitness L r := by
  rintro ⟨l, hl, v, hv, hv1, he⟩
  exact hv1 (h.conjugate_product_eq_one_of_le_component hsmall hempty hr hr2 hl hres
    ((OuterResidual.involutionResidual_le L r).trans inf_le_right) hv he)

/-- An involution in the even residual supplies a witness when the involutions of rL are conjugate under L. -/
theorem residualFusionWitness_of_even_of_coset_conjugacy
    (hr2 : orderOf r = 2) (hrL : r ∉ L)
    (heven : Even (Nat.card (OuterResidual.involutionResidual L r)))
    (hfuse : ∀ v ∈ L, orderOf (r * v) = 2 → ∃ l ∈ L, MulAut.conj l r = r * v) :
    ResidualFusionWitness L r := by
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  have hv2 : orderOf (v : G) = 2 := (orderOf_coe v).trans hv
  have hv1 : (v : G) ≠ 1 := by intro he; simp [he] at hv2
  have hvL := (OuterResidual.involutionResidual_le L r v.property).1
  have hrv : Commute r (v : G) :=
    (mem_centralizer_singleton_iff.mp (OuterResidual.involutionResidual_le L r v.property).2).symm
  have hrv2 : orderOf (r * v) = 2 := by
    apply orderOf_eq_prime
    · have hrpow : r ^ 2 = 1 := by simpa only [hr2] using pow_orderOf_eq_one r
      have hvpow : (v : G) ^ 2 = 1 := by simpa only [hv2] using pow_orderOf_eq_one (v : G)
      rw [hrv.mul_pow, hrpow, hvpow, one_mul]
    · intro he
      apply hrL
      have hrEq : r = (v : G)⁻¹ := (eq_inv_iff_mul_eq_one).mpr he
      exact hrEq ▸ L.inv_mem hvL
  obtain ⟨l, hl, hf⟩ := hfuse v hvL hrv2
  exact ⟨l, hl, v, v.property, hv1, hf⟩

omit [Finite G] in
private theorem conjugate_eq_mul_square_of_inverted_four_element {r y z : G}
    (hy4 : orderOf y = 4) (hyz : y ^ 2 = z)
    (hinv : MulAut.conj r y = y⁻¹) : MulAut.conj y r = r * z := by
  have hy4' : y ^ 4 = 1 := by simpa only [hy4] using pow_orderOf_eq_one y
  have hz2 : z * z = 1 := by rw [← hyz]; simpa only [← pow_add] using hy4'
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hinvi : MulAut.conj r y⁻¹ = y := by rw [map_inv, hinv, inv_inv]
  have hry : r * y⁻¹ = y * r := by
    have hh := congrArg (fun a : G => a * r) hinvi
    simpa only [MulAut.conj_apply, mul_assoc, inv_mul_cancel, mul_one] using hh
  calc
    MulAut.conj y r = y * r * y⁻¹ := rfl
    _ = r * (y⁻¹ * y⁻¹) := by rw [← hry, mul_assoc]
    _ = r * z⁻¹ := by rw [← hyz, pow_two, mul_inv_rev]
    _ = r * z := by rw [hzi]

omit [Finite G] in
/-- Fusion of r and rz removes the central error in a lifted residual witness. -/
theorem residualFusionWitness_of_central_twist {r z l y v : G} {L : Subgroup G}
    (hz : z ∈ centralizer (L : Set G)) (hz2 : z * z = 1)
    (hl : l ∈ L) (hy : y ∈ L) (hyconj : MulAut.conj y r = r * z)
    (hv : v ∈ OuterResidual.involutionResidual L r) (hv1 : v ≠ 1)
    (hconj : MulAut.conj l r = r * v ∨ MulAut.conj l r = r * v * z) :
    ResidualFusionWitness L r := by
  rcases hconj with hc | hc
  · exact ⟨l, hl, v, hv, hv1, hc⟩
  · refine ⟨l * y, L.mul_mem hl hy, v, hv, hv1, ?_⟩
    have hzl : MulAut.conj l z = z := by
      change l * z * l⁻¹ = z
      rw [mem_centralizer_iff.mp hz l hl, mul_inv_cancel_right]
    have hcomp : MulAut.conj (l * y) r = MulAut.conj l (MulAut.conj y r) := by
      simp only [MulAut.conj_apply, mul_inv_rev]
      group
    rw [hcomp, hyconj, map_mul, hc, hzl, mul_assoc (r * v), hz2, mul_one]


omit [Finite G] in
/-- The order-four inversion supplied by I.2.2(5b) removes the possible central factor in the lifted fusion. -/
theorem residualFusionWitness_of_inverted_four_element {r z l y v : G} {L : Subgroup G}
    (hz : z ∈ centralizer (L : Set G))
    (hl : l ∈ L) (hy : y ∈ L) (hy4 : orderOf y = 4) (hyz : y ^ 2 = z)
    (hinv : MulAut.conj r y = y⁻¹)
    (hv : v ∈ OuterResidual.involutionResidual L r) (hv1 : v ≠ 1)
    (hconj : MulAut.conj l r = r * v ∨ MulAut.conj l r = r * v * z) :
    ResidualFusionWitness L r := by
  have hy4' : y ^ 4 = 1 := by simpa only [hy4] using pow_orderOf_eq_one y
  have hz2 : z * z = 1 := by rw [← hyz]; simpa only [← pow_add] using hy4'
  exact residualFusionWitness_of_central_twist hz hz2 hl hy
    (conjugate_eq_mul_square_of_inverted_four_element hy4 hyz hinv) hv hv1 hconj

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction
