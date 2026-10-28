module
public import Theory.GroupTheory.IrreducibleSectionCore

/-!
# The core on an ambient irreducible section

An actor A normalizing a p-section V/N acts irreducibly on it. Restricting
N and V to A allows the intrinsic core-centralization theorem to apply;
mapping back shows that the ambient image of O_p(A) acts trivially on V/N.
The original 13.7.4 application uses V₃/V₁ and A=L₁T.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
theorem ambient_irreducible_section_core
    (N V A : Subgroup G) (hNV : N ≤ V) (hVA : V ≤ A)
    (hAN : A ≤ normalizer (N : Set G)) (hAV : A ≤ normalizer (V : Set G))
    (hp : IsPGroup p V)
    (hirr : ∀ E : Subgroup G, N ≤ E → E ≤ V →
      A ≤ normalizer (E : Set G) → E=N ∨ E=V) : ⁅V,A.pCoreIn p⁆ ≤ N := by
  let N' := N.subgroupOf A
  let V' := V.subgroupOf A
  let : N'.Normal := normal_subgroupOf_of_le_normalizer hAN
  let : V'.Normal := normal_subgroupOf_of_le_normalizer hAV
  have hmin (E : Subgroup A) (hNE : N' ≤ E) (hEV : E ≤ V') (hn : E.Normal) :
      E=N' ∨ E=V' := by
    have hnorm : A ≤ normalizer (E.map A.subtype : Set G) := by
      apply le_normalizer_iff.mpr
      rintro g hg x ⟨x,hx,rfl⟩
      exact ⟨⟨g,hg⟩*x*⟨g,hg⟩⁻¹,hn.conj_mem x hx ⟨g,hg⟩,rfl⟩
    have hlo : N ≤ E.map A.subtype := by
      simpa only [N',map_subgroupOf_eq_of_le (hNV.trans hVA)] using map_mono (f:=A.subtype) hNE
    have hhi : E.map A.subtype ≤ V := by
      simpa only [V',map_subgroupOf_eq_of_le hVA] using map_mono (f:=A.subtype) hEV
    rcases hirr _ hlo hhi hnorm with he|he
    · left
      apply map_injective A.subtype_injective
      simpa only [N',map_subgroupOf_eq_of_le (hNV.trans hVA)] using he
    · right
      apply map_injective A.subtype_injective
      simpa only [V',map_subgroupOf_eq_of_le hVA] using he
  have hc := commutator_pCore_le_of_irreducible_section N' V'
    (comap_mono hNV) hp.comap_subtype hmin
  have hm := map_mono (f:=A.subtype) hc
  rwa [map_commutator,map_subgroupOf_eq_of_le hVA,
    map_subgroupOf_eq_of_le (hNV.trans hVA)] at hm
end Subgroup
