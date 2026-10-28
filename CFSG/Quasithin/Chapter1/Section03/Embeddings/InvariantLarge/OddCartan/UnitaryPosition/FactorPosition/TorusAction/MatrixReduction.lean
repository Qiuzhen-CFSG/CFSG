module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.Representation.RankThreeAbelianAutomizer
public import Theory.GroupTheory.CentralCoprimeAbelianLift
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# Reducing the projective unitary torus calculation to matrix centralizers

Lift the abelian prime subgroup through the actual scalar projective kernel,
whose elements have cube one. The chosen lift is invariant under the inverse
image of the projective normalizer. Its faithful matrix image is abelian,
noncyclic, cross-characteristic and determinant one. The existing weight action
embeds its automizer in S₃. Centralizers and their relative normalizer indices
then descend through the central projective map.

The abelianness of the matrix centralizer remains an explicit hypothesis here.
It must be proved from the determinant-one weight dimensions before the
unconditional torus-action theorem can be assembled.

Source: Aschbacher--Smith, A.3.21(c), printed pp.55--56, and the proof of
1.3.4, printed pp.510--511 of refs/quasithin.pdf.
-/

public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition

private theorem embedding_centralizer_bound
    {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (Q : Subgroup G)
    [IsMulCommutative (centralizer (Q.map f : Set H))]
    (hi : (centralizer (Q.map f : Set H)).relIndex (normalizer (Q.map f)) ∣ 6) :
    IsMulCommutative (centralizer (Q : Set G)) ∧
      (centralizer (Q : Set G)).relIndex (normalizer Q) ∣ 6 := by
  have hC : (centralizer (Q.map f : Set H)).comap f = centralizer (Q : Set G) := by
    ext x
    constructor
    · intro hx q hq
      apply hf
      simpa only [map_mul] using hx (f q) (mem_map_of_mem f hq)
    · intro hx y hy
      obtain ⟨q, hq, rfl⟩ := hy
      simpa only [map_mul] using congrArg f (hx q hq)
  refine ⟨hC ▸ (centralizer (Q.map f : Set H)).comap_injective_isMulCommutative hf, ?_⟩
  rw [← hC, relIndex_comap]
  let N := normalizer (Q.map f : Set H)
  let C := (centralizer (Q.map f : Set H)).subgroupOf N
  have hN : (normalizer Q).map f ≤ N := Q.le_normalizer_map f
  have hd : (centralizer (Q.map f : Set H)).relIndex ((normalizer Q).map f) ∣ C.index := by
    rw [← relIndex_subgroupOf hN]
    exact C.relIndex_dvd_index_of_normal _
  exact hd.trans hi

private theorem automizer_index_bound {G : Type*} [Group G] (B : Subgroup G)
    (j : B.normalizerMonoidHom.range →* Equiv.Perm (Fin 3)) (hj : Function.Injective j) :
    (centralizer (B : Set G)).relIndex (normalizer B) ∣ 6 := by
  rw [relIndex, ← B.normalizerMonoidHom_ker, index_ker]
  have hd := card_dvd_of_injective j hj
  simpa [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] using hd

/-- The actual projective unitary model has the required centralizer and
normalizer index once the determinant-one matrix centralizer theorem is supplied. -/
theorem isPSU_centralizer_bound_of_matrix_centralizers
    {H : Type*} [Group H] [Finite H] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hp3 : p ≠ 3) (hpq : p ≠ q) (hm : ClassicalGroup.IsPSU H 3 q)
    (B : Subgroup H) [IsMulCommutative B] (hB : IsPGroup p B) (hn : ¬ IsCyclic B)
    (hcent : ∀ (F : Type) [Field F] [Finite F] (R : Subgroup (GL (Fin 3) F)),
      IsMulCommutative R → (Nat.card R : F) ≠ 0 → ¬ IsCyclic R →
      (∀ x : R, Matrix.GeneralLinearGroup.det x.val = 1) →
      IsMulCommutative (centralizer (R : Set (GL (Fin 3) F)))) :
    IsMulCommutative (centralizer (B : Set H)) ∧
      (centralizer (B : Set H)).relIndex (normalizer B) ∣ 6 := by
  obtain ⟨F, hF, hfin, J, hcard, _hconj, ⟨e⟩⟩ := hm
  let _ := Fintype.ofFinite F
  let _ : CharP F q := charP_of_card_eq_prime_pow (by
    simpa only [Nat.card_eq_fintype_card] using hcard)
  let f : J.specialSubgroup →* H := e.symm.toMonoidHom.comp J.specialToProjective
  have hf : Function.Surjective f := e.symm.surjective.comp J.specialToProjective_surjective
  have hker : f.ker = J.specialToProjective.ker :=
    MonoidHom.ker_comp_of_injective _ _ e.symm.injective
  have hkc : f.ker ≤ center J.specialSubgroup := hker ▸ J.specialToProjective_ker_le_center
  have hk3 : IsPGroup 3 f.ker := by
    rw [hker]
    exact fun x => ⟨1, by simpa using J.specialToProjective_ker_cube x⟩
  obtain ⟨n, hncard⟩ := hk3.exists_card_eq
  have hcop : Nat.Coprime p (Nat.card f.ker) := by
    rw [hncard]
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      (fun h => hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp h))).pow_right n
  obtain ⟨Q, hQp, hQa, hQmap, hQnorm⟩ :=
    exists_abelian_prime_lift_of_central_coprime_kernel f hf hkc hcop B hB
  let _ : IsMulCommutative Q := hQa
  have hQi := injective_comp_subtype_of_coprime_ker f hcop Q hQp
  have hQn : ¬ IsCyclic Q := by
    intro hc
    let _ := hc
    have hm : IsCyclic (Q.map f) := isCyclic_of_surjective (f.subgroupMap Q)
      (f.subgroupMap_surjective Q)
    exact hn (hQmap ▸ hm)
  let R := Q.map J.specialSubgroup.subtype
  have hRp : IsPGroup p R := hQp.map J.specialSubgroup.subtype
  have hRn : ¬ IsCyclic R := by
    intro hc
    let _ := hc
    exact hQn ((Q.equivMapOfInjective J.specialSubgroup.subtype
      J.specialSubgroup.subtype_injective).isCyclic.mpr hc)
  have hRo : (Nat.card R : F) ≠ 0 := by
    obtain ⟨a, ha⟩ := hRp.exists_card_eq
    rw [ha, Nat.cast_pow]
    apply pow_ne_zero
    rw [Ne, CharP.cast_eq_zero_iff F q]
    exact fun hd => hpq ((Nat.prime_dvd_prime_iff_eq
      (Fact.out : q.Prime) (Fact.out : p.Prime)).mp hd).symm
  have hRd : ∀ x : R, Matrix.GeneralLinearGroup.det x.val = 1 := by
    intro x
    obtain ⟨y, _hy, he⟩ := x.property
    rw [← he]
    exact y.property.2
  let _ : IsMulCommutative (centralizer (R : Set (GL (Fin 3) F))) :=
    hcent F R inferInstance hRo hRn hRd
  obtain ⟨j, hj⟩ := Representation.generalLinear_abelian_automizer_embeds_perm 3 R hRo
  obtain ⟨hCQ, hIQ⟩ := embedding_centralizer_bound J.specialSubgroup.subtype
    J.specialSubgroup.subtype_injective Q (automizer_index_bound R j hj)
  let _ := hCQ
  obtain ⟨hcm, him⟩ := centralizer_map_and_relIndex_eq_of_normalizer_preimage f hf Q hQi
    (by simpa only [hQmap] using hQnorm)
  rw [hQmap] at hcm him
  refine ⟨?_, ?_⟩
  · rw [← hcm]
    infer_instance
  · rwa [← him]

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition
