module
public import Stellmacher.SectionThree.LemmaThreeTwo

/-!
# Extracting a generating member of the local family

Let P have a unique maximal subgroup containing S. Suppose L supplements S
inside P and belongs to the local L-family for a supplied Sylow subgroup T.
If N_L(T) together with S is proper in P, some member of PSet L T already
generates P together with S. No normality assumption on L is needed. The auxiliary
`le_unique_maximal_over` also exposes the proper-overgroup containment used
when recovering a generating residual from the selected family member.

By Stellmacher (3.2), the local family generates the Sylow-generated
residual of L. Frattini supplements that residual by a subgroup of N_L(T).
If every family member had a proper join with S, uniqueness of the maximal
subgroup containing S would put the whole residual and N_L(T) into it,
contradicting the generation of P by L and S.

This is the local-family extraction used for the centralizer in Stellmacher
(6.4), journal p32, based on (3.1)--(3.2), journal pp21--22 of
refs/latex/stellmacher-n-group.tex. The supplied Sylow condition on T is
explicit and must be established by that centralizer application.
-/

namespace Stellmacher.SectionThree

/-- Every proper overgroup of S is contained in its unique maximal overgroup. -/
public theorem le_unique_maximal_over
    {G : Type*} [Group G] [Finite G]
    {S P L : Subgroup G} {B : Subgroup P}
    (huniq : ∀ B' : Subgroup P, IsCoatom B' → S ≤ B'.map P.subtype → B' = B)
    (hSL : S ≤ L) (hLP : L ≤ P) (hne : L ≠ P) : L ≤ B.map P.subtype := by
  have hproper : L.subgroupOf P ≠ ⊤ := by
    intro ht
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hLP, ht,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨B',hB',hLB'⟩ :=
    (eq_top_or_exists_le_coatom (L.subgroupOf P)).resolve_left hproper
  have hSB' : S ≤ B'.map P.subtype := by
    apply hSL.trans
    rw [← Subgroup.map_subgroupOf_eq_of_le hLP]
    exact Subgroup.map_mono hLB'
  rw [← huniq B' hB' hSB', ← Subgroup.map_subgroupOf_eq_of_le hLP]
  exact Subgroup.map_mono hLB'

public theorem exists_pSet_generating_of_normalizer_join_ne
    {G : Type*} [Group G] [Finite G]
    (S T P L : Subgroup G) (h : Hypotheses G T)
    (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hL : L ∈ LSet (⊤ : Subgroup G) T)
    (hLP : L ≤ P) (hgen : L ⊔ S = P)
    (hnorm : (L ⊓ Subgroup.normalizer (T : Set G)) ⊔ S ≠ P) :
    ∃ F : Subgroup G, F ∈ PSet L T ∧ F ⊔ S = P := by
  classical
  have hSP : S ≤ P := le_sup_right.trans_eq hgen
  obtain ⟨B,hB,hSB,huniq⟩ := hP.2
  obtain ⟨N,hTN,hNL,hNT,hcover⟩ := exists_normalizer_factor L T hL.2.1
  by_contra! hnone
  have hRB : twoPrimeResidualAmbient L ≤ B.map P.subtype := by
    rw [lemma_three_two T h L hL]
    apply iSup_le
    intro F
    exact le_sup_left.trans (le_unique_maximal_over huniq le_sup_right
      (sup_le (F.property.1.1.trans hLP) hSP) (hnone F F.property))
  have hNB : N ≤ B.map P.subtype := by
    apply (le_inf hNL hNT).trans
    exact le_sup_left.trans (le_unique_maximal_over huniq le_sup_right
      (sup_le (inf_le_left.trans hLP) hSP) hnorm)
  have hPB : P ≤ B.map P.subtype := by
    exact hgen.ge.trans (sup_le (hcover.trans (sup_le hRB hNB)) hSB)
  apply hB.1
  apply Subgroup.map_injective P.subtype_injective
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact le_antisymm (Subgroup.map_subtype_le _) hPB

end Stellmacher.SectionThree

