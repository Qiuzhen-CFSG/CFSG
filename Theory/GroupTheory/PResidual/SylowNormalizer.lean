module
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Normalization from a residual and a Sylow supplement

An acting subgroup which normalizes both the embedded prime residual and a
Sylow subgroup normalizes the whole finite group.  The proof is the literal
residual--Sylow supplement followed by the subgroup normalizer product
lemma.  This is used by the Case-I `M_Z` normalizer argument.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem le_normalizer_of_residual_and_sylow
    {p : ℕ} [Fact p.Prime] (A H S : Subgroup G)
    (hTres : A ≤ normalizer ((pResidual p H).map H.subtype : Set G))
    (hTS : A ≤ normalizer (S : Set G))
    (hSyl : ∃ P : Sylow p H,
      (P : Subgroup H).map H.subtype = S) :
    A ≤ normalizer (H : Set G) := by
  obtain ⟨P, hP⟩ := hSyl
  have hs := congrArg (Subgroup.map H.subtype) (pResidual_sup_sylow_eq_top P)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype, hP] at hs
  rw [← hs]
  exact (le_inf hTres hTS).trans
    (normalizer_inf_normalizer_le_normalizer_sup
      ((pResidual p H).map H.subtype) S)

theorem le_normalizer_of_residual_sup_sylow
    {p : ℕ} [Fact p.Prime] (A H S R C : Subgroup G)
    (hproduct : (pResidual p H).map H.subtype = R ⊔ C)
    (hR : A ≤ normalizer (R : Set G))
    (hC : A ≤ normalizer (C : Set G))
    (hST : S ≤ A)
    (hSnA : (S.subgroupOf A).Normal)
    (hSyl : ∃ P : Sylow p H,
      (P : Subgroup H).map H.subtype = S) :
    A ≤ normalizer (H : Set G) := by
  let : (S.subgroupOf A).Normal := hSnA
  have hSA : S ≤ A := hST
  have hAS : A ≤ normalizer (S : Set G) :=
    le_normalizer_of_normal_subgroupOf hSA
  have hAC : A ≤ normalizer (R ⊔ C : Subgroup G) := by
    exact (le_inf hR hC).trans
      (normalizer_inf_normalizer_le_normalizer_sup R C)
  have hres : A ≤ normalizer ((pResidual p H).map H.subtype : Set G) := by
    rw [hproduct]
    exact hAC
  obtain ⟨P, hP⟩ := hSyl
  have hs := congrArg (Subgroup.map H.subtype) (pResidual_sup_sylow_eq_top P)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype, hP] at hs
  rw [← hs]
  exact (le_inf hres hAS).trans
    (normalizer_inf_normalizer_le_normalizer_sup
      ((pResidual p H).map H.subtype) S)

end Subgroup
