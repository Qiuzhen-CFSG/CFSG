module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent.QuotientIdentification.Cores
public import Theory.GroupTheory.SylowIndexThreeQuotient

/-!
# Recognition of the original centralizer factor

The product `G_E = M_E I`, with `I ≤ C_G(E)`, transfers index three to
`M_E ∩ C_G(E)` inside `C_G(E)`. The actual 15.3.66 action-kernel identity
makes that intersection a two-group, hence a Sylow subgroup. It properly
contains the intrinsic centralizer core: equality would put the surviving
Sylow Thompson subgroup in the original `Q_E`.

The action on these three cosets now identifies `C_G(E)/O₂(C_G(E))` with
`S₃`. This derives the second factor from the original groups and index;
it assumes neither the second identification nor a temporary-core equality.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
Lemma 15.3.67, printed pp.1153–1154, PDF pp.1170–1171.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped Pointwise

private theorem index_in_normal_supplement
    {H : Type*} [Group H] [Finite H] (M C : Subgroup H) [C.Normal]
    (hsup : M ⊔ C = ⊤) : M.relIndex C = M.index := by
  have hC : C.relIndex M = C.index := by
    rw [← relIndex_sup_right M C, hsup, relIndex_top_right]
  have h1 := relIndex_inf_mul_relIndex M C (⊤ : Subgroup H)
  have h2 := relIndex_inf_mul_relIndex C M (⊤ : Subgroup H)
  simp only [inf_top_eq, relIndex_top_right] at h1 h2
  rw [inf_comm C M, hC] at h2
  apply Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (index_ne_zero_of_finite : C.index ≠ 0))
  exact h1.trans (h2.symm.trans (Nat.mul_comm _ _))

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification
variable {G : Type*} [Group G] [Finite G]

/-- The centralizer meets `M_E` with the same index as the full line normalizer. -/
theorem centralizer_intersection_index (M E : Subgroup G)
    (hprod : (lineNormalizer E : Set G) = (lineM M E : Set G) * (lineI E : Set G)) :
    (lineM M E).relIndex (centralizer (E : Set G)) =
      (lineM M E).relIndex (lineNormalizer E) := by
  let H := lineNormalizer E
  let A := (lineM M E).subgroupOf H
  let C := (centralizer (E : Set G)).subgroupOf H
  let : C.Normal := inferInstance
  have hs : A ⊔ C = ⊤ := by
    apply top_unique
    intro g _
    have hg : (g : G) ∈ (lineM M E : Set G) * (lineI E : Set G) := by
      rw [← hprod]
      exact g.property
    obtain ⟨m, hm, i, hi, hmi⟩ := hg
    have he : (⟨m, hm.2⟩ : H) * ⟨i, lineI_le_lineNormalizer E hi⟩ = g :=
      Subtype.ext hmi
    rw [← he]
    exact mul_mem_sup hm (lineI_le_centralizer E hi)
  have h := index_in_normal_supplement A C hs
  rw [show A.relIndex C = (lineM M E).relIndex (centralizer (E : Set G)) from
    relIndex_subgroupOf (centralizer_le_normalizer (E : Set G))] at h
  exact h

/-- The original line-centralizer quotient is `S₃`. The two-group intersection
is supplied by 15.3.66(5) after `M_E = Y_E T_E`; the strict core containment
comes from the actual Thompson family and the recognized index of `I₀`. -/
theorem centralizer_core_quotient (M T V E : Subgroup G) [IsMulCommutative V]
    (hEV : E ≤ V) (U : Sylow 2 (lineNormalizer E))
    (hU : (U : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E)
    (hTM : T ≤ M)
    (hJ : elementaryAbelianMaxJ (lineT T E) =
      elementaryAbelianMaxJ (T ⊓ centralizer (V : Set G)))
    (hQC : lineQ E ≤ centralizer (E : Set G))
    (hNM : normalizer (V : Set G) ≤ M)
    (hprod : (lineNormalizer E : Set G) = (lineM M E : Set G) * (lineI E : Set G))
    (hindex : (lineI0 T V E ⊓ lineM M E).relIndex (lineI0 T V E) = 3)
    (hS : IsPGroup 2 (lineM M E ⊓ centralizer (E : Set G) : Subgroup G)) :
    Nonempty ((centralizer (E : Set G) ⧸ pCore 2 (centralizer (E : Set G))) ≃*
      Equiv.Perm (Fin 3)) := by
  let C := centralizer (E : Set G)
  let S := (lineM M E).subgroupOf C
  have hi : S.index = 3 := (centralizer_intersection_index M E hprod).trans
    (original_index_three M T V E hEV U hU hNM hprod hindex)
  have hSp : IsPGroup 2 S := by
    have he : (lineM M E ⊓ C).comap C.subtype = S := by
      ext x
      exact and_iff_left x.property
    exact he ▸ hS.comap_subtype (K := C)
  let P : Sylow 2 C := hSp.toSylow (by rw [hi]; decide)
  have hJC : elementaryAbelianMaxJ (lineT T E) ≤ C := by
    rw [hJ]
    exact (sSup_le fun _ hA => hA.1).trans (inf_le_right.trans (centralizer_le hEV))
  have hp : pCore 2 C < (P : Subgroup C) := by
    apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal P)
    intro he
    apply sylowThompson_not_le_lineQ M T V E U hU hTM hJC hindex
    intro x hx
    have hxM : x ∈ lineM M E :=
      (inf_le_inf hTM le_rfl) ((show elementaryAbelianMaxJ (lineT T E) ≤ lineT T E from
        sSup_le fun _ hA => hA.1) hx)
    have hxCore : (⟨x, hJC hx⟩ : C) ∈ pCore 2 C := he.symm ▸ hxM
    have hxMap : x ∈ C.pCoreIn 2 := mem_map_of_mem C.subtype hxCore
    rwa [centralizer_twoCore E hQC] at hxMap
  exact sylow_index_three_core_quotient P hi hp

omit [Finite G] in
/-- The two-group intersection follows from the actual 15.3.66 action kernel. -/
theorem centralizer_intersection_isTwo_of_core (M Y T E : Subgroup G)
    (hME : lineM M E = lineY Y E ⊔ lineT T E)
    (hSE : (lineY Y E ⊔ lineT T E : Subgroup G).pCoreIn 2 =
      (lineY Y E ⊔ lineT T E) ⊓ centralizer (E : Set G)) :
    IsPGroup 2 (lineM M E ⊓ centralizer (E : Set G) : Subgroup G) := by
  rw [hME, ← hSE]
  exact isPGroup_pCoreIn 2 _

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Descent.QuotientIdentification
