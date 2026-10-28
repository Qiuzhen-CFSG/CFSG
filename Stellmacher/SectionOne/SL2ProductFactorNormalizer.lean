module
public import Stellmacher.SectionOne.SL2NormalizerInner

/-!
# Factorwise normalizers of an SL₂(2) product

An actor preserving every factor of an internal SL₂(2) product acts on the
product by inner automorphisms: it lies in the product times its centralizer.
For one factor, choose the correcting inner element from SL2NormalizerInner.
It commutes with the other factors, so finite induction corrects one factor
at a time without disturbing the earlier corrections. The final correction
lies in the generated group and leaves an element centralizing every factor,
hence centralizing their join.

This gives the group-side reduction used to split the odd core in
Stellmacher (1.7)(a), journal p.19 of `refs/latex/stellmacher-n-group.tex`.
Only generation and pairwise commutation from the internal product data
are needed; the correction argument does not assume ambient normality.
-/

namespace Stellmacher.SectionOne
universe u

private theorem family_correcting_element
    {G : Type u} [Group G] [Finite G]
    (F : Finset (Subgroup G))
    (hSL : ∀ D ∈ F, IsSL2Two D)
    (hcomm : ∀ D ∈ F, ∀ K ∈ F, D ≠ K →
      ∀ d ∈ D, ∀ k ∈ K, d*k=k*d)
    (g : G) (hg : ∀ D ∈ F, g ∈ Subgroup.normalizer (D : Set G)) :
    ∃ e : G, e ∈ (⨆ D : {D : Subgroup G // D ∈ F}, (D : Subgroup G)) ∧
      ∀ D ∈ F, e⁻¹*g ∈ Subgroup.centralizer (D : Set G) := by
  classical
  induction F using Finset.induction_on generalizing g with
  | empty => exact ⟨1, Subgroup.one_mem _, by simp⟩
  | @insert D F hDF ih =>
    obtain ⟨d,hd⟩ := sl2_normalizer_exists_inner D (hSL D (Finset.mem_insert_self ..))
      g (hg D (Finset.mem_insert_self ..))
    have hdnorm (K : Subgroup G) (hK : K ∈ F) :
        (d : G) ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (hcomm D (Finset.mem_insert_self ..) K (Finset.mem_insert_of_mem hK)
        (fun he => hDF (he ▸ hK)) d d.property k hk).symm
    have hc (K : Subgroup G) (hK : K ∈ F) :
        (d : G)⁻¹*g ∈ Subgroup.normalizer (K : Set G) :=
      (Subgroup.normalizer (K : Set G)).mul_mem
        ((Subgroup.normalizer (K : Set G)).inv_mem
          (Subgroup.centralizer_le_normalizer _ (hdnorm K hK)))
        (hg K (Finset.mem_insert_of_mem hK))
    obtain ⟨e,he,hec⟩ := ih
      (fun K hK => hSL K (Finset.mem_insert_of_mem hK))
      (fun K hK L hL => hcomm K (Finset.mem_insert_of_mem hK)
        L (Finset.mem_insert_of_mem hL)) ((d : G)⁻¹*g) hc
    have hecentral : e ∈ Subgroup.centralizer (D : Set G) := by
      have hle : (⨆ K : {K : Subgroup G // K ∈ F}, (K : Subgroup G)) ≤
          Subgroup.centralizer (D : Set G) := by
        apply iSup_le
        intro K k hk
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact hcomm D (Finset.mem_insert_self ..) K (Finset.mem_insert_of_mem K.property)
          (fun he => hDF (he ▸ K.property)) x hx k hk
      exact hle he
    refine ⟨(d : G)*e, ?_, ?_⟩
    · apply Subgroup.mul_mem
      · exact (le_iSup (fun K : {K : Subgroup G // K ∈ insert D F} => (K : Subgroup G))
          ⟨D,Finset.mem_insert_self ..⟩) d.property
      · apply (show (⨆ K : {K : Subgroup G // K ∈ F}, (K : Subgroup G)) ≤
            ⨆ K : {K : Subgroup G // K ∈ insert D F}, (K : Subgroup G) from ?_) he
        apply iSup_le
        intro K
        exact le_iSup (fun K : {K : Subgroup G // K ∈ insert D F} => (K : Subgroup G))
          ⟨K,Finset.mem_insert_of_mem K.property⟩
    · intro K hK
      rcases Finset.mem_insert.mp hK with rfl | hK
      · simpa only [mul_inv_rev,mul_assoc] using
          (Subgroup.centralizer (K : Set G)).mul_mem
            ((Subgroup.centralizer (K : Set G)).inv_mem hecentral) hd
      · simpa only [mul_inv_rev,mul_assoc] using hec K hK

public theorem sl2_product_normalizer_exists_inner
    {G : Type u} [Group G] [Finite G]
    (E : Subgroup G) (F : Finset (Subgroup G))
    (hprod : IsInternalDirectProduct E F)
    (hSL : ∀ D ∈ F, IsSL2Two D)
    (q : G) (hq : ∀ D ∈ F, q ∈ Subgroup.normalizer (D : Set G)) :
    ∃ e : E, (e : G)⁻¹*q ∈ Subgroup.centralizer (E : Set G) := by
  obtain ⟨e,he,hec⟩ := family_correcting_element F hSL hprod.2.2.2 q
    hq
  have heE : e ∈ E := by rwa [hprod.1]
  refine ⟨⟨e,heE⟩, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  have hle : E ≤ Subgroup.centralizer ({e⁻¹*q} : Set G) := by
    rw [hprod.1]
    apply iSup_le
    intro D d hd
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (hec D D.property) d hd
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

public theorem sl2_product_factor_normalizer_le_sup_centralizer
    {G : Type u} [Group G] [Finite G]
    (E Q : Subgroup G) (F : Finset (Subgroup G))
    (hprod : IsInternalDirectProduct E F)
    (hSL : ∀ D ∈ F, IsSL2Two D)
    (hQ : ∀ D ∈ F, Q ≤ Subgroup.normalizer (D : Set G)) :
    Q ≤ E ⊔ Subgroup.centralizer (E : Set G) := by
  intro q hq
  obtain ⟨e,hcent⟩ := sl2_product_normalizer_exists_inner E F hprod hSL q
    (fun D hD => hQ D hD hq)
  have heq : (e : G)*((e : G)⁻¹*q) ∈ E ⊔ Subgroup.centralizer (E : Set G) :=
    (E ⊔ Subgroup.centralizer (E : Set G)).mul_mem
      ((show E ≤ E ⊔ Subgroup.centralizer (E : Set G) from le_sup_left) e.property)
      ((show Subgroup.centralizer (E : Set G) ≤ E ⊔ Subgroup.centralizer (E : Set G)
        from le_sup_right) hcent)
  simpa using heq

end Stellmacher.SectionOne
