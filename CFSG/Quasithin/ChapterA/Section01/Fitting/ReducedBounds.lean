module

public import Theory.GroupTheory.ReducedNormal.Defs

/-!
# Centralizer bounds for the reduced-two subgroup

The two-core of a normal subgroup K centralizes R₂(G). Conversely, a genuinely
2-reduced normal elementary subgroup U with C_K(U) = O₂(K) gives equality,
because U lies in R₂(G). These are the final containments in A.1.19.
`Fitting.Reduced` supplies the full theorem: it constructs such a reduced
witness from the source's arbitrary normal elementary witness using the
minimal-witness argument and Thompson's A × B lemma.

Source: Aschbacher–Smith, A.1.19, printed p.24; B.2.11–12, pp.77–78.
-/

public section
namespace CFSG.Quasithin.ChapterA
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- The immediate containment in A.1.19, with both sides embedded in G. -/
theorem lemma_A_1_19_core_le (K : Subgroup G) [K.Normal] :
    (pCore 2 K).map K.subtype ≤ K ⊓ centralizer (reducedTwoSubgroup G : Set G) :=
  le_inf (map_subtype_le _) (normal_pCore_le_centralizer_reducedPSubgroup 2 K)

/-- The concluding centralizer argument of A.1.19, once its reduced witness
has been constructed. Reducedness is an explicit extra premise here. -/
theorem centralizer_reducedTwo_eq_core_of_reduced_witness
    (K U : Subgroup G) [K.Normal] (hU : IsPReduced 2 U)
    (hcentral : K ⊓ centralizer (U : Set G) = (pCore 2 K).map K.subtype) :
    K ⊓ centralizer (reducedTwoSubgroup G : Set G) = (pCore 2 K).map K.subtype :=
  le_antisymm
    ((inf_le_inf_left K (centralizer_le hU.le_reducedPSubgroup)).trans_eq hcentral)
    (lemma_A_1_19_core_le K)

end CFSG.Quasithin.ChapterA
