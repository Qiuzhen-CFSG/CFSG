module

public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# A normalized cubic obstructs an exchanged normal-closure product

Suppose the normal closure of a lies in a product of two commuting disjoint
factors and contains both, with a in the first factor. The relation a c = c² a
puts c in that same factor. A Sylow 2-subgroup normalizing the cyclic group of
c cannot exchange the factors. Since the ambient group permutes two factors,
the first factor's normalizer has index at most two and odd index, hence is
normal. Normal-closure generation then contradicts the second factor.

This group-theoretic argument preserves the original element, factors, Sylow
and cubic. Source: Aschbacher–Smith, C.5.12, p.163, invoking G.6.4.
-/

public section

open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
omit [Finite G] in
theorem inverted_cubic_mem_first_of_normalClosure_product
    (A B : Subgroup G) (a c : G) (ha : a ∈ A)
    (hjoin : A ⊔ B = normalClosure ({a} : Set G))
    (hcomm : ⁅A,B⁆ = ⊥) (hi : a * c = c ^ 2 * a) : c ∈ A := by
  have he : a * (c * a⁻¹ * c⁻¹) = c := by
    calc
      a * (c * a⁻¹ * c⁻¹) = (a * c) * a⁻¹ * c⁻¹ := by group
      _ = (c ^ 2 * a) * a⁻¹ * c⁻¹ := by rw [hi]
      _ = c := by group
  let K := normalClosure ({a} : Set G)
  have haK : a ∈ K := subset_normalClosure (Set.mem_singleton a)
  have hcK : c ∈ K := he ▸ K.mul_mem haK
    ((inferInstance : K.Normal).conj_mem a⁻¹ (K.inv_mem haK) c)
  have hKF : K ≤ normalizer (A : Set G) := by
    change normalClosure ({a} : Set G) ≤ normalizer (A : Set G)
    rw [← hjoin]
    apply sup_le A.le_normalizer
    apply le_normalizer_iff_commutator_le_left.mpr
    rw [hcomm]
    exact bot_le
  have hca : c * a⁻¹ * c⁻¹ ∈ A :=
    (mem_normalizer_iff.mp (hKF hcK) a⁻¹).mp (A.inv_mem ha)
  exact he ▸ A.mul_mem ha hca

theorem not_sylow_normalizes_cubic_of_normalClosure_product
    (A B : Subgroup G) (a c : G) (ha : a ∈ A)
    (hjoin : A ⊔ B = normalClosure ({a} : Set G))
    (hcomm : ⁅A,B⁆ = ⊥) (hdis : Disjoint A B) (hB : B ≠ ⊥)
    (hperm : ∀ g : G, (A.map (MulAut.conj g).toMonoidHom = A ∧
      B.map (MulAut.conj g).toMonoidHom = B) ∨
      (A.map (MulAut.conj g).toMonoidHom = B ∧ B.map (MulAut.conj g).toMonoidHom = A))
    (S : Sylow 2 G) (hcne : c ≠ 1) (hi : a * c = c ^ 2 * a)
    (hn : (S : Subgroup G) ≤ normalizer (zpowers c : Set G)) : False := by
  have hd : A ⊓ B = ⊥ := disjoint_iff.mp hdis
  have hcF := inverted_cubic_mem_first_of_normalClosure_product A B a c ha hjoin hcomm hi
  have hSF : (S : Subgroup G) ≤ normalizer (A : Set G) := by
    intro s hs
    rcases hperm s with h | h
    · exact mem_normalizer_iff_map_conj_eq.mpr h.1
    · have hc' : s * c * s⁻¹ ∈ A :=
        (zpowers_le.mpr hcF) ((mem_normalizer_iff.mp (hn hs) c).mp (mem_zpowers c))
      have hc'' : s * c * s⁻¹ ∈ B := by
        rw [← h.1]
        exact mem_map_of_mem (MulAut.conj s).toMonoidHom hcF
      have hz : s * c * s⁻¹ = 1 := hd.le ⟨hc', hc''⟩
      have hcz := congrArg (fun x : G => s⁻¹ * x * s) hz
      exact (hcne (by simpa only [mul_assoc, inv_mul_cancel_left,
        inv_mul_cancel, mul_one, one_mul] using hcz)).elim
  have hpair : A ≠ B := by
    intro he
    apply hB
    simpa only [he, inf_idem] using hd
  have hsub : (Set.range fun g : G => A.map (MulAut.conj g).toMonoidHom) ⊆
      {A, B} := by
    rintro _ ⟨g, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      (hperm g).imp And.left And.left
  have hindex : (normalizer (A : Set G)).index ≤ 2 := by
    rw [← ncard_conjugates_eq_index_normalizer]
    exact (Set.ncard_le_ncard hsub).trans_eq (Set.ncard_pair hpair)
  have hindexne : (normalizer (A : Set G)).index ≠ 2 := by
    intro he
    have hd := index_dvd_of_le hSF
    rw [he] at hd
    exact S.not_dvd_index hd
  have hindexpos := (normalizer (A : Set G)).index_ne_zero_of_finite
  have hnormal : A.Normal := normalizer_eq_top_iff.mp
    (index_eq_one.mp (by omega))
  let := hnormal
  have hKF : normalClosure ({a} : Set G) ≤ A :=
    normalClosure_le_normal (by simpa only [Set.singleton_subset_iff, SetLike.mem_coe] using ha)
  have hsecond : B ≤ A := by
    have hj : A ⊔ B ≤ A := by rwa [hjoin]
    exact le_sup_right.trans hj
  apply hB
  apply bot_unique
  intro x hx
  exact hd.le ⟨hsecond hx, hx⟩
end Theory.GroupTheory
