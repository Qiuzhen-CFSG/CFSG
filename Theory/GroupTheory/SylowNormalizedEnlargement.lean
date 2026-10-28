module
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.SylowNormalizedSupIndex

/-!
# Enlarging a Sylow supplement inside a normalizing p-group

If S is Sylow in KS, and a p-group R contains S and normalizes K,
then R is Sylow in KR. Restrict the original Sylow to the relatively
normal K and use its coprime index for the larger supplement.

Source application: Aschbacher–Smith, Lemma 3.1.7, printed p.576,
the linear E.2.3 branch with S=Baum(T) and R=O₂(M₀).
-/

public section
open Subgroup

theorem IsPGroup.exists_sylow_sup_of_smaller_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (K S R : Subgroup G) (hR : IsPGroup p R) (hSR : S ≤ R)
    (hn : R ≤ normalizer (K : Set G))
    (P : Sylow p (K ⊔ S : Subgroup G))
    (hP : (P : Subgroup (K ⊔ S : Subgroup G)).map (K ⊔ S).subtype = S) :
    ∃ Q : Sylow p (K ⊔ R : Subgroup G),
      (Q : Subgroup (K ⊔ R : Subgroup G)).map (K ⊔ R).subtype = R := by
  let L := K ⊔ S
  let D := K.subgroupOf L
  let : D.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le K.le_normalizer (hSR.trans hn))
  obtain ⟨U, hU⟩ := P.exists_subgroupOf_eq_of_normal D
  let e : D ≃* K := subgroupOfEquivOfLe (show K ≤ L from le_sup_left)
  let U' := U.mapSurjective (f := e.toMonoidHom) e.surjective
  have hUS : (U' : Subgroup K).map K.subtype ≤ S := by
    rintro x ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    have hzP : z.val ∈ (P : Subgroup L) := by
      change z ∈ (P : Subgroup L).subgroupOf D
      rw [← hU]
      exact hz
    exact hP ▸ mem_map_of_mem L.subtype hzP
  exact hR.exists_sylow_sup_of_coprime_index K R hn (U' : Subgroup K)
    U'.not_dvd_index (hUS.trans hSR)

