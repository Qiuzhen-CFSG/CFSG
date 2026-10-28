module

public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# A two-central element cannot generate exchanged disjoint factors

If the ambient group permutes two disjoint factors and a nonidentity element
of the first is central in a full Sylow two-subgroup, that Sylow must fix the
first factor. Its normalizer has index at most two and odd index, hence equals
the ambient group. Normal-closure generation then makes the second factor
trivial. This is the group-theoretic step in Aschbacher–Smith G.6.4(4), p.346.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem not_twoCentral_of_normalClosure_pair
    (A B : Subgroup G) (a : G) (ha : a ∈ A) (hne : a ≠ 1)
    (hjoin : A ⊔ B = normalClosure ({a} : Set G))
    (hdis : Disjoint A B) (hB : B ≠ ⊥)
    (hperm : ∀ g : G, (A.map (MulAut.conj g).toMonoidHom = A ∧
      B.map (MulAut.conj g).toMonoidHom = B) ∨
      (A.map (MulAut.conj g).toMonoidHom = B ∧ B.map (MulAut.conj g).toMonoidHom = A))
    (S : Sylow 2 G) (hz : a ∈ (center S).map (S : Subgroup G).subtype) : False := by
  obtain ⟨z,hz,rfl⟩ := hz
  change (z : G) ∈ A at ha
  change (z : G) ≠ 1 at hne
  change A ⊔ B = normalClosure ({(z : G)} : Set G) at hjoin
  have hd : A ⊓ B = ⊥ := disjoint_iff.mp hdis
  have hSA : (S : Subgroup G) ≤ normalizer (A : Set G) := by
    intro s hs
    rcases hperm s with h | h
    · exact mem_normalizer_iff_map_conj_eq.mpr h.1
    · have hc : s * (z : G) * s⁻¹ = z := by
        have he := congrArg Subtype.val (mem_center_iff.mp hz (⟨s,hs⟩ : S))
        change s * (z : G) = (z : G) * s at he
        calc
          s * (z : G) * s⁻¹ = (z : G) * s * s⁻¹ := by rw [he]
          _ = z := mul_inv_cancel_right _ _
      have hb : (z : G) ∈ B := by
        rw [← hc, ← h.1]
        exact mem_map_of_mem (MulAut.conj s).toMonoidHom ha
      exact (hne (hd.le ⟨ha,hb⟩)).elim
  have hpair : A ≠ B := by
    intro he
    exact hB (by simpa only [he, inf_idem] using hd)
  have hsub : (Set.range fun g : G => A.map (MulAut.conj g).toMonoidHom) ⊆ {A,B} := by
    rintro _ ⟨g,rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      (hperm g).imp And.left And.left
  have hindex : (normalizer (A : Set G)).index ≤ 2 := by
    rw [← ncard_conjugates_eq_index_normalizer]
    exact (Set.ncard_le_ncard hsub).trans_eq (Set.ncard_pair hpair)
  have hindexne : (normalizer (A : Set G)).index ≠ 2 := by
    intro he
    have hd := index_dvd_of_le hSA
    rw [he] at hd
    exact S.not_dvd_index hd
  have hindexpos := (normalizer (A : Set G)).index_ne_zero_of_finite
  let : A.Normal := normalizer_eq_top_iff.mp (index_eq_one.mp (by omega))
  have hKA : normalClosure ({(z : G)} : Set G) ≤ A :=
    normalClosure_le_normal (by simpa only [Set.singleton_subset_iff, SetLike.mem_coe] using ha)
  have hBA : B ≤ A := le_sup_right.trans (hjoin.le.trans hKA)
  exact hB (bot_unique (fun x hx => hd.le ⟨hBA hx,hx⟩))
end Theory.GroupTheory
