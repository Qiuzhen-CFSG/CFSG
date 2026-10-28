module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.Embedding
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Placing the fixed pair in an elementary sixteen

The inner two-rank bound supplies an outer involution t in A and identifies the
ambient group with Aut(M₁₂). Since the residual has index at most two, its
intersection with A has order at least eight. Transfer the actual inner
centralizer of t through the residual marking to the fixed subgroup of its
native automorphism. Under the genuine C₂ × A₅ table row, the projection onto
C₂ has a nontrivial kernel on this intersection. Thus A contains a nonidentity
involution in the actual A₅ factor. A small kernel-checked A₅ calculation finds
a conjugator whose commutator with it has order five.

Only the native outer fixed-subgroup row and the inner two-rank bound are
premises. No subgroup placement or representation-theoretic fact is assumed.
Source: Aschbacher–Smith H.11.1(4), printed pp.392–393, combined manuscript of
1 March 2004. The cycle calculation uses the ordinary five-letter A₅.
-/

public section
open Subgroup Representation.BinaryOffender Sporadic.Mathieu
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.FixedPairs

/-- The genuine fixed-subgroup row for outer involutions of the native M₁₂.
Its construction belongs to the parent involution-table task. -/
@[expose] def OuterFixedSubgroupTable : Prop := ∀ a : MulAut M12,
    a ∉ MulAut.innerSubgroup M12 → orderOf a = 2 →
      Nonempty (a.fixedSubgroup ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin 5))

private theorem conjugation_injective :
    Function.Injective (MulAut.conj : M12 →* MulAut M12) := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  have hc : g ∈ center M12 := by
    rw [mem_center_iff]
    intro x
    have hx := congrArg (fun a : MulAut M12 => a x) hg
    change g * x * g⁻¹ = x at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  simpa only [m12_center_eq_bot, mem_bot] using hc

private theorem conj_natural (a : MulAut M12) (x : M12) :
    MulAut.conj (a x) = a * MulAut.conj x * a⁻¹ := by
  ext y
  simp [MulAut.conj_apply]

private def cycleFive : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4, by
    change Equiv.Perm.sign _ = 1
    decide⟩

set_option maxRecDepth 4096 in
private theorem involution_certificate : ∀ z : alternatingGroup (Fin 5),
    z ≠ 1 → z ^ 2 = 1 →
    ((z * cycleFive * z⁻¹ * cycleFive⁻¹) ^ 5 = 1 ∧
      z * cycleFive * z⁻¹ * cycleFive⁻¹ ≠ 1) ∨
    ((z * cycleFive ^ 2 * z⁻¹ * (cycleFive ^ 2)⁻¹) ^ 5 = 1 ∧
      z * cycleFive ^ 2 * z⁻¹ * (cycleFive ^ 2)⁻¹ ≠ 1) := by
  decide +kernel

private theorem a5_involution_commutator (z : alternatingGroup (Fin 5))
    (hz : z ≠ 1) (hz2 : z ^ 2 = 1) :
    ∃ g : alternatingGroup (Fin 5), orderOf (z * g * z⁻¹ * g⁻¹) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rcases involution_certificate z hz hz2 with hh | hh
  · exact ⟨cycleFive, orderOf_eq_prime hh.1 hh.2⟩
  · exact ⟨cycleFive ^ 2, orderOf_eq_prime hh.1 hh.2⟩

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {h : M12ModuleInput ρ} (d : AmbientExtension ρ h)

private theorem residual_fixed_iff (t : G) (x : solvableResidual G) :
    h.residualEquiv x ∈ (d.embedding t).fixedSubgroup ↔ Commute t (x : G) := by
  have he : MulAut.conj (d.embedding t (h.residualEquiv x)) =
      d.embedding (t * x * t⁻¹) := by
    rw [conj_natural, ← d.embedding_residual, map_mul, map_mul, map_inv]
  rw [MulAut.mem_fixedSubgroup]
  constructor
  · intro hx
    have hi : d.embedding (t * x * t⁻¹) = d.embedding x := by
      rw [← he, hx, d.embedding_residual]
    exact mul_inv_eq_iff_eq_mul.mp (d.embedding_injective hi)
  · intro hc
    apply conjugation_injective
    rw [he, ← d.embedding_residual]
    exact congrArg d.embedding (mul_inv_eq_iff_eq_mul.mpr hc.eq)

private noncomputable def residualFixedEquiv (t : G) :
    (solvableResidual G ⊓ centralizer ({t} : Set G) : Subgroup G) ≃* (d.embedding t).fixedSubgroup where
  toFun x := ⟨h.residualEquiv ⟨x, x.property.1⟩,
    (residual_fixed_iff d t _).mpr (mem_centralizer_singleton_iff.mp x.property.2).symm⟩
  invFun x := ⟨h.residualEquiv.symm x, (h.residualEquiv.symm x).property,
    mem_centralizer_singleton_iff.mpr ((residual_fixed_iff d t _).mp (by
      simp only [h.residualEquiv.apply_symm_apply]
      exact x.property)).symm⟩
  left_inv x := by
    apply Subtype.ext
    change ((h.residualEquiv.symm (h.residualEquiv ⟨x.val, x.property.1⟩)) : G) = x.val
    exact congrArg Subtype.val (h.residualEquiv.symm_apply_apply _)
  right_inv x := by apply Subtype.ext; exact h.residualEquiv.apply_symm_apply _
  map_mul' x y := by
    apply Subtype.ext
    change h.residualEquiv ((⟨x.val, x.property.1⟩ : solvableResidual G) *
      ⟨y.val, y.property.1⟩) = _
    exact h.residualEquiv.map_mul _ _

variable [Finite G]
include d in
private theorem residual_index_le_two (hinner : primeRank 2 M12 ≤ 3)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16) :
    (solvableResidual G).index ≤ 2 := by
  have he := (solvableResidual G).index_map_equiv
    (d.automorphismEquivOfElementarySixteen hinner A hA hcard)
  change ((solvableResidual G).map d.embedding).index = (solvableResidual G).index at he
  rw [d.map_residual] at he
  rw [← he]
  exact M12A5Fixer.Automorphisms.outerIndexBound

include d in
private theorem residual_intersection_card (hinner : primeRank 2 M12 ≤ 3)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16) :
    8 ≤ Nat.card ((solvableResidual G).subgroupOf A) := by
  have hi := residual_index_le_two d hinner A hA hcard
  have hir : ((solvableResidual G).subgroupOf A).index ≤ 2 := by
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (solvableResidual G).index_ne_zero_of_finite)
      ((solvableResidual G).relIndex_dvd_index_of_normal A)).trans hi
  have hc := ((solvableResidual G).subgroupOf A).card_mul_index
  rw [hcard] at hc
  nlinarith

include d in
/-- The elementary sixteen meets the actual A₅ factor in an involution which
has an order-five commutator inside the outer involution centralizer. -/
theorem exists_centralizing_commutator_five (hinner : primeRank 2 M12 ≤ 3)
    (htable : OuterFixedSubgroupTable)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hcard : Nat.card A = 16) :
    ∃ t z g : G, t ∈ A ∧ t ∉ solvableResidual G ∧ orderOf t = 2 ∧
      z ∈ A ∧ z ∈ solvableResidual G ∧ orderOf z = 2 ∧
      g ∈ solvableResidual G ∧ Commute t z ∧ Commute t g ∧
      orderOf (z * g * z⁻¹ * g⁻¹) = 5 := by
  classical
  let := hA
  obtain ⟨t, htA, htL⟩ := Set.not_subset.mp
    (AmbientExtension.elementary_sixteen_not_le_residual (h := h) hinner A hA hcard)
  have ht : orderOf t = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian t htA) (fun he => htL (he ▸ (solvableResidual G).one_mem))
  obtain ⟨etable⟩ := htable (d.embedding t)
    (fun hi => htL ((d.embedding_mem_inner_iff t).mp hi))
    ((orderOf_injective d.embedding d.embedding_injective t).trans ht)
  let C := solvableResidual G ⊓ centralizer ({t} : Set G)
  let e : C ≃* Multiplicative (ZMod 2) × alternatingGroup (Fin 5) :=
    (residualFixedEquiv d t).trans etable
  let K := (solvableResidual G).subgroupOf A
  let f : K →* C := {
    toFun x := ⟨x.val.val, x.property, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm x.val (⟨t, htA⟩ : A)))⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    have hh : x.val.val = y.val.val := congrArg (fun c : C => (c : G)) hxy
    exact Subtype.ext (Subtype.ext hh)
  let q : K →* Multiplicative (ZMod 2) := (MonoidHom.fst _ _).comp (e.toMonoidHom.comp f)
  have hq : ¬ Function.Injective q := by
    intro hi
    have hc := Nat.card_le_card_of_injective q hi
    have hk := residual_intersection_card d hinner A hA hcard
    have hc2 : Nat.card (Multiplicative (ZMod 2)) = 2 := Nat.card_zmod 2
    rw [hc2] at hc
    change 8 ≤ Nat.card K at hk
    omega
  rw [injective_iff_map_eq_one] at hq
  push Not at hq
  obtain ⟨z, hzq, hz1⟩ := hq
  let y := (e (f z)).2
  have hze : e (f z) = (1, y) := Prod.ext hzq rfl
  have hy1 : y ≠ 1 := by
    intro hy
    apply hz1
    apply hf
    apply e.injective
    simpa only [map_one, hy, Prod.mk_one_one] using hze
  have hzpow : (f z) ^ 2 = 1 := by
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian _ z.val.property
  have hy2 : y ^ 2 = 1 := by
    have he := congrArg (fun c => (e c).2) hzpow
    simpa only [map_pow, map_one, Prod.pow_snd, Prod.snd_one] using he
  obtain ⟨g, hg⟩ := a5_involution_commutator y hy1 hy2
  let gc : C := e.symm (1, g)
  have hc : orderOf (f z * gc * (f z)⁻¹ * gc⁻¹) = 5 := by
    rw [← e.orderOf_eq (f z * gc * (f z)⁻¹ * gc⁻¹)]
    simp only [map_mul, map_inv, hze, gc, e.apply_symm_apply, Prod.mk_mul_mk,
      Prod.inv_mk, one_mul, inv_one, Prod.orderOf_mk, orderOf_one, Nat.lcm_one_left, hg]
  have hz : orderOf (f z : G) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian _ z.val.property) (by
      intro he
      exact hz1 (Subtype.ext (Subtype.ext he)))
  refine ⟨t, f z, gc, htA, htL, ht, z.val.property, (f z).property.1, hz,
    gc.property.1, (mem_centralizer_singleton_iff.mp (f z).property.2).symm,
    (mem_centralizer_singleton_iff.mp gc.property.2).symm, ?_⟩
  exact (orderOf_injective C.subtype C.subtype_injective _).trans hc

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.FixedPairs
