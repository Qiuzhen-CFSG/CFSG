module
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.A4
import Mathlib.GroupTheory.Sylow

/-!
# A₄ actor transport for the original local residual

The source marks the local residual by an even permutation of the six-letter
model and then uses `fourLetterEquiv` to obtain the literal A₄ quotient.  This
module records the transport needed after that marking: a cubic subgroup cannot
meet an elementary two-kernel nontrivially, its image therefore has order three,
and Sylow-3 conjugacy in the literal A₄ transports the binary fixed index to the
canonical four-letter Klein four.
Source: Aschbacher--Smith 13.7.10(8), printed p.942.
-/
public section
open Subgroup
open scoped Pointwise
namespace GLS3.Chapter5

private theorem map_centralizer_equiv (E : Subgroup (alternatingGroup (Fin 4)))
    (e : alternatingGroup (Fin 4) ≃* alternatingGroup (Fin 4)) :
    (centralizer (E : Set (alternatingGroup (Fin 4)))).map e.toMonoidHom =
      centralizer (E.map e.toMonoidHom : Set (alternatingGroup (Fin 4))) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

private theorem cubic_subgroup_index (D : Subgroup (alternatingGroup (Fin 4)))
    (hD : Nat.card D = 3) : ¬ 3 ∣ D.index := by
  intro hd
  obtain ⟨k, hk⟩ := hd
  have hh := D.index_mul_card
  have hG : Nat.card (alternatingGroup (Fin 4)) = 12 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [hD, hG] at hh
  omega


/-- A three-subgroup actor survives an elementary two-kernel map and hence has
cardinal three image. -/
theorem cubic_image_card_of_two_kernel {H K : Type*} [Group H] [Finite H] [Group K]
    (f : H →* K) (hp : IsPGroup 2 f.ker) (A : Subgroup H) (hA : Nat.card A = 3) :
    Nat.card (A.map f) = 3 := by
  have hd : Disjoint A f.ker := by
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hA, hn]
    exact Nat.Coprime.pow_right n (by decide)
  let fa : A →* K := f.comp A.subtype
  have hfa : Function.Injective fa := by
    intro a b hab
    apply Subtype.ext
    have hmem : (a : H) / b ∈ A ⊓ f.ker := by
      refine ⟨A.div_mem a.property b.property, ?_⟩
      change f ((a : H) / b) = 1
      have hab' : f (a : H) = f (b : H) := hab
      rw [map_div, hab']
      exact div_self' (f (b : H))
    rw [hd.eq_bot] at hmem
    exact div_eq_one.mp hmem
  have hrange : fa.range = A.map f := by
    rw [MonoidHom.range_eq_map]
    ext x
    constructor
    · rintro ⟨y, -, hy⟩
      exact ⟨y, y.property, hy⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨⟨y, hy⟩, trivial, hxy⟩
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hfa).toEquiv).symm.trans hA

/-- Every order-three subgroup of the literal A₄ has the same binary fixed index
as the marked cubic.  The proof uses Sylow conjugacy and transports the
centralizer relative index through the four-letter marking. -/
theorem cubic_length_one_of_card_three
    (D : Subgroup (alternatingGroup (Fin 4))) (hD : Nat.card D = 3) :
    conjugationCubicLength D alternatingFourKlein = 1 := by
  let c : alternatingGroup (Fin 4) := alternatingFourThreeCycle
  have hc : c ^ 3 = 1 := by
    rw [← alternatingFourThreeCycle_order]
    exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := by
    intro h
    have horder3 : orderOf c = 3 := by simpa [c] using alternatingFourThreeCycle_order
    have horder1 : orderOf c = 1 := orderOf_eq_one_iff.mpr h
    omega
  have hCc : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc hc1]
  have hcanonIndex := cubic_subgroup_index (Subgroup.zpowers c) hCc
  let P : Sylow 3 (alternatingGroup (Fin 4)) :=
    (IsPGroup.of_card (n := 1) hCc).toSylow hcanonIndex
  have hDindex := cubic_subgroup_index D hD
  let Q : Sylow 3 (alternatingGroup (Fin 4)) :=
    (IsPGroup.of_card (n := 1) hD).toSylow hDindex
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 4)) P Q
  have hmap : (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = D := by
    have hh := congrArg (fun R : Sylow 3 (alternatingGroup (Fin 4)) =>
        (R : Subgroup (alternatingGroup (Fin 4)))) hg
    change (Subgroup.zpowers c).map (MulAut.conj g).toMonoidHom = D at hh
    simpa only [P, Q, IsPGroup.toSylow_coe] using hh
  have hnorm : (Subgroup.zpowers c) ≤
      normalizer (alternatingFourKlein : Set (alternatingGroup (Fin 4))) :=
    le_normalizer_of_normal
  have hnormD : D ≤ normalizer (alternatingFourKlein : Set (alternatingGroup (Fin 4))) := by
    rw [alternatingFourKlein.normalizer_eq_top]
    exact le_top
  have hcent := map_centralizer_equiv (Subgroup.zpowers c) (MulAut.conj g)
  have hUmap : alternatingFourKlein.map (MulAut.conj g).toMonoidHom =
      alternatingFourKlein := by
    have hgU : g ∈ normalizer (alternatingFourKlein : Set (alternatingGroup (Fin 4))) := by
      rw [alternatingFourKlein.normalizer_eq_top]
      trivial
    exact mem_normalizer_iff_map_conj_eq.mp hgU
  unfold conjugationCubicLength
  rw [← hmap, ← hcent, ← hUmap,
    relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
  exact u_length_one

/-- The canonical four-letter marking computes the cubic fixed index for every
order-three subgroup, so arbitrary source actors need no conjugator choice. -/
theorem map_cubic_length_one_of_two_kernel {H : Type*} [Group H] [Finite H]
    (f : H →* alternatingGroup (Fin 4)) (hp : IsPGroup 2 f.ker)
    (A : Subgroup H) (hA : Nat.card A = 3) :
    conjugationCubicLength (A.map f) alternatingFourKlein = 1 := by
  apply cubic_length_one_of_card_three
  exact cubic_image_card_of_two_kernel f hp A hA

/-- The same transport for a marked ambient actor already presented as a
subgroup of the source residual. -/
theorem map_cubic_length_one_of_two_kernel_of_subgroup
    {G : Type*} [Group G] [Finite G]
    (J : Subgroup G) (f : J →* alternatingGroup (Fin 4)) (hp : IsPGroup 2 f.ker)
    (A : Subgroup G) (hAJ : A ≤ J) (hA : Nat.card A = 3) :
    conjugationCubicLength ((A.subgroupOf J).map f) alternatingFourKlein = 1 := by
  apply map_cubic_length_one_of_two_kernel f hp (A.subgroupOf J)
  exact (Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv).trans hA

end GLS3.Chapter5
