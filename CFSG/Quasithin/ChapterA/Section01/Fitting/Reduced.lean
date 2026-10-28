module

public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic
public import CFSG.Quasithin.ChapterA.Section01.Fitting.ReducedBounds
public import Theory.GroupTheory.ReducedNormal.Inheritance
public import Theory.GroupTheory.ReducedNormal.Detection

/-!
# A.1.11 and A.1.19: the reduced-two subgroup

A.1.11 places R₂(H) in R₂(G) for a Sylow overgroup H in a group with
F*(G) = O₂(G). The characteristic-two bridge and Sylow core containment
place its normal closure in Z(O₂(G)); the literal centralizer quotient
then proves that closure is reduced.

For A.1.19, an arbitrary elementary abelian detecting witness contains a
minimal witness. Thompson's fixed-point kernel theorem shows that this
minimal witness is reduced. The previously established centralizer bounds
then give C_K(R₂(G)) = O₂(K). No reducedness premise is imposed on U.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript of 1 March 2004, A.1.11 and A.1.19, printed pp.22 and 24;
B.2.11–12, printed pp.77–78, define the reduced subgroups.
-/

public section
namespace CFSG.Quasithin.ChapterA
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A.1.11: reduced-two subgroups are inherited from Sylow overgroups in
characteristic two. The left side is embedded in the ambient group. -/
theorem lemma_A_1_11 (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hG : generalizedFitting G = pCore 2 G) :
    (reducedTwoSubgroup H).map H.subtype ≤ reducedTwoSubgroup G :=
  reducedPSubgroup_map_le_of_sylow_le T H hTH
    ((generalizedFitting_eq_pCore_iff 2).mp hG)

/-- A.1.19: any normal elementary abelian detecting witness gives the
same centralizer as the maximal reduced-two subgroup. -/
theorem lemma_A_1_19 (K U : Subgroup G) [K.Normal] [U.Normal]
    [IsElementaryAbelian 2 U]
    (hcentral : K ⊓ centralizer (U : Set G) = (pCore 2 K).map K.subtype) :
    K ⊓ centralizer (reducedTwoSubgroup G : Set G) = (pCore 2 K).map K.subtype := by
  obtain ⟨V, _, hV, hVc⟩ := exists_isPReduced_le_centralizer_eq_core K U hcentral
  exact centralizer_reducedTwo_eq_core_of_reduced_witness K V hV hVc

end CFSG.Quasithin.ChapterA
