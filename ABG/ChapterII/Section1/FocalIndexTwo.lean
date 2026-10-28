module
public import ABG.ChapterII.Section1.FusionPatterns
public import GorensteinWalter.GWLemma21
public import Theory.GroupTheory.NormalIndexTwo
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Realizing an index-two focal subgroup

If the focal subgroup F of a Sylow two-subgroup P has index two in P,
there is a normal subgroup K of index two in G whose actual intersection
with P is F. Moreover, K has no further normal subgroup of index two.
The second theorem supplies an actual Sylow two-subgroup of K, with its
ambient image equal to F's image and a multiplicative equivalence to F.

These are the common normal-subgroup conclusions in the Q and D alternatives
of Alperin–Brauer–Gorenstein, Chapter II, Section 1, Proposition 1
(article pp.10–11 of `refs/latex/alperin-brauer-gorenstein.tex`). The later
applications identify F with the explicit quaternion or dihedral maximal
subgroup of the quasi-dihedral presentation. No such identification is
assumed or substituted for the focal equality here.

The focal and first Grün theorems identify the transfer target subgroup.
The Grün transfer kernel then has the prescribed index and intersection.
A normal subgroup of index four in G would force four to divide F's index,
which is two. The general index-two lemma therefore rules out a further
normal subgroup of index two in K. Restricting P to normal K provides its
actual Sylow subgroup, and the injective subtype maps identify its model.
The existing Feit–Thompson focal API is used throughout.
-/

namespace ABG
open BenderSuzuki.External
variable {G : Type*} [Group G] [Finite G]

/-- An index-two focal subgroup is the Sylow intersection of a normal
index-two subgroup which has no further normal subgroup of index two. -/
public theorem exists_normal_index_two_of_focalSubgroupOf
    (P : Sylow 2 G) (F : Subgroup P) (hFi : F.index = 2)
    (hF : (P : Subgroup G).focalSubgroupOf = F) :
    ∃ K : Subgroup G, K.Normal ∧ K.index = 2 ∧ HasNoNormalIndexTwoSubgroup K ∧
      K ⊓ (P : Subgroup G) = F.map (P : Subgroup G).subtype := by
  have hgrun : huppertIV34GrunKernelSubgroup (P : Subgroup G) =
      (P : Subgroup G).focalSubgroup := by
    rw [← huppert_IV_3_4_first_grun P, inf_comm, Subgroup.commutator_inf_eq_focalSubgroup P]
  have hrel : (huppertIV34GrunKernelSubgroup (P : Subgroup G)).relIndex
      (P : Subgroup G) = 2 := by
    change ((huppertIV34GrunKernelSubgroup (P : Subgroup G)).subgroupOf
      (P : Subgroup G)).index = 2
    rw [hgrun]
    change ((P : Subgroup G).focalSubgroupOf).index = 2
    rw [hF]
    exact hFi
  let K := (huppertIV34GrunTransfer P).ker
  have hKi : K.index = 2 := (huppertIV34GrunTransfer_ker_index P).trans hrel
  have hno4 : ∀ M : Subgroup G, M.Normal → M.index ≠ 4 := by
    intro M hM hi
    exact GorensteinWalter.no_normal_index_four_of_grun_relIndex_eq_two P hrel ⟨M, hM, hi⟩
  refine ⟨K, inferInstance, hKi,
    Subgroup.no_normal_index_two_of_index_two_of_no_normal_index_four K hKi hno4, ?_⟩
  change (huppertIV34GrunTransfer P).ker ⊓ (P : Subgroup G) = _
  rw [huppertIV34GrunTransfer_ker_inf_sylow, hgrun,
    ← Subgroup.map_focalSubgroupOf, hF]

/-- The same normal subgroup, with an actual Sylow subgroup and the
multiplicative equivalence needed to transport the focal subgroup's model. -/
public theorem exists_normal_index_two_sylow_of_focalSubgroupOf
    (P : Sylow 2 G) (F : Subgroup P) (hFi : F.index = 2)
    (hF : (P : Subgroup G).focalSubgroupOf = F) :
    ∃ K : Subgroup G, K.Normal ∧ K.index = 2 ∧ HasNoNormalIndexTwoSubgroup K ∧
      ∃ R : Sylow 2 K, (R : Subgroup K).map K.subtype = F.map (P : Subgroup G).subtype ∧
        Nonempty (R ≃* F) := by
  obtain ⟨K, hK, hKi, hKno, hKP⟩ := exists_normal_index_two_of_focalSubgroupOf P F hFi hF
  let : K.Normal := hK
  obtain ⟨R, hR⟩ := P.exists_subgroupOf_eq_of_normal K
  have hmap : (R : Subgroup K).map K.subtype = F.map (P : Subgroup G).subtype := by
    rw [hR, Subgroup.subgroupOf_map_subtype, inf_comm]
    exact hKP
  refine ⟨K, hK, hKi, hKno, R, hmap, ?_⟩
  exact ⟨((R : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans
    ((MulEquiv.subgroupCongr hmap).trans
      (F.equivMapOfInjective (P : Subgroup G).subtype (P : Subgroup G).subtype_injective).symm)⟩
end ABG
