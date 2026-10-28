module
public import Theory.GroupTheory.PResidual.CoreCentralizer
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PCoreImage

/-!
# Sylow placement in the centralizer of a residual section

Let A be a normal two-perfect subgroup and T a Sylow two-subgroup.
The intersection of T with C_G(A/O₂(A)) is O₂(AT): a two-subgroup
centralizing the two-residual of AT modulo its core lies in O₂(AT),
and normality gives the reverse inclusion. Restricting T to the normal
section centralizer supplies a Sylow subgroup with this exact image.

The application takes A=O²(K) for the kernel K of a reduced module.
It constructs the Sylow placement used in Aschbacher–Smith 13.4.4(2ii)
and 13.4.8, printed pp.897 and904–905, on the original common Sylow.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The original Sylow meets the section centralizer in the core of its residual supplement. -/
theorem sylow_inf_sectionCentralizer_eq_join_core (A : Subgroup G) [A.Normal]
    (hA : IsPPerfect 2 A) (T : Sylow 2 G) :
    (T : Subgroup G) ⊓ commutatorPreimage ⊤ A (A.pCoreIn 2) =
      (A ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let P := A ⊔ (T : Subgroup G)
  let C := commutatorPreimage (⊤ : Subgroup G) A (A.pCoreIn 2)
  let R := (T : Subgroup G) ⊓ C
  let : (A.pCoreIn 2).Normal := inferInstanceAs ((pCore 2 A).map A.subtype).Normal
  have hres : (pResidual 2 P).map P.subtype = A :=
    embedded_pResidual_join_pGroup A (T : Subgroup G) hA T.isPGroup' le_normalizer_of_normal
  have hRP : R ≤ P := inf_le_left.trans le_sup_right
  have hAP : A ≤ P := le_sup_left
  have hcore : A.pCoreIn 2 ≤ P.pCoreIn 2 :=
    pCoreIn_mono_of_normalizes hAP le_normalizer_of_normal
  have hQP : P ≤ normalizer (P.pCoreIn 2 : Set G) :=
    P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image P (pCore 2 P))
  have hQT : P.pCoreIn 2 ≤ T := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ P from le_sup_right)]
      using pCoreIn_le_sylow P (T.subtype le_sup_right)
  apply le_antisymm
  · have hc : ⁅R.subgroupOf P,pResidual 2 P⁆ ≤ pCore 2 P := by
      apply (map_le_map_iff_of_injective P.subtype_injective).mp
      rw [map_commutator,map_subgroupOf_eq_of_le hRP,hres]
      exact ((commutator_mono inf_le_right le_rfl).trans
        (commutator_commutatorPreimage_le ⊤ A (A.pCoreIn 2) le_normalizer_of_normal)).trans hcore
    have hh := map_mono (f := P.subtype)
      (pSubgroup_le_pCore_of_commutator_pResidual_le (R.subgroupOf P)
        (T.isPGroup'.to_le inf_le_left).comap_subtype hc)
    rwa [map_subgroupOf_eq_of_le hRP] at hh
  · refine le_inf hQT (le_commutatorPreimage le_top ?_)
    apply le_trans (le_inf (commutator_le_right _ _) ?_) (inf_pCoreIn_le_of_le 2 hAP)
    exact le_normalizer_iff_commutator_le_left.mp (hAP.trans hQP)

/-- The core of the residual/Sylow supplement is Sylow in the residual-section centralizer. -/
theorem exists_sylow_residualSection_map_eq_join_core (K : Subgroup G) [K.Normal] (T : Sylow 2 G) :
    ∃ S : Sylow 2 (residualSectionCentralizer 2 K),
      (S : Subgroup _).map (residualSectionCentralizer 2 K).subtype =
        ((pResidual 2 K).map K.subtype ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let D := (pResidual 2 K).map K.subtype
  let : D.Normal := inferInstance
  let : (residualSectionCentralizer 2 K).Normal := residualSectionCentralizer_normal K
  obtain ⟨S,hS⟩ := T.exists_sylow_map_eq_inf_of_normal (residualSectionCentralizer 2 K)
  refine ⟨S,hS.trans ?_⟩
  exact sylow_inf_sectionCentralizer_eq_join_core D (isPPerfect_embedded_pResidual 2 K) T
end Subgroup
