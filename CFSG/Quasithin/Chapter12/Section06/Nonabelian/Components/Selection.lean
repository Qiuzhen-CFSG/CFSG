module

public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Consequences
public import Theory.GroupTheory.GeneralizedFitting.MovedComponent

/-!
# Component selection in the contrary-nonabelian argument

The selected subgroup is a C-component of the original H, whose image in
the literal H/O₂(H) is an ordinary component. Centralization of F(H*) is
the preceding odd-core stage, not an assumption that a component exists.
Centrality in the marked Sylow image gives normalization and the full
commutator. The latter also forces the component outside M: otherwise
its image would be a perfect nontrivial two-group.

The subsequent L₁-action, condition (*), exceptional-cover exclusions and
rank-one recognition are separate, still unproved steps. This module does
not claim the rank-one reduction or Lemma 12.6.26 is complete.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
12.6.26, printed pp.832–833, PDF pp.849–850.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup
variable {G : Type*} [Group G] (D : Setup G)

/-- The marked Sylow image uses the original T and the actual star map. -/
noncomputable def Tstar [Finite G] (H : Subgroup G) (hT : (D.T : Subgroup G) ≤ H) :
    Sylow 2 (Hstar H) :=
  (D.T.subtype hT).mapSurjective (f := QuotientGroup.mk' (pCore 2 H))
    (QuotientGroup.mk'_surjective _)

/-- Results of selection, not hypotheses of the source theorem. -/
structure SelectedComponent (H : Subgroup G) where
  K : Subgroup G
  le_H : K ≤ H
  ccomponent : (K.subgroupOf H).IsCComponent
  component : IsComponent (Hstar H) (star H K)
  moved : ⁅star H K, star H D.V⁆ ≠ ⊥
  normalized : star H D.V ≤ normalizer (star H K : Set (Hstar H))
  full_commutator : ⁅star H K, star H D.V⁆ = star H K
  outside : ¬ K ≤ D.M

variable [Finite G]

/-- A full nontrivial component commutator cannot occur inside M when
the actor lies in O₂(M). This uses the actual ambient subgroup maps. -/
theorem component_not_le_M {H K : Subgroup G}
    (hK : IsComponent (Hstar H) (star H K))
    (hV : D.V ≤ D.M.pCoreIn 2)
    (hfull : ⁅star H K, star H D.V⁆ = star H K) : ¬ K ≤ D.M := by
  intro hKM
  let q := QuotientGroup.mk' (pCore 2 H)
  let B := (D.M.pCoreIn 2).subgroupOf H
  have hnorm : D.M ≤ normalizer (D.M.pCoreIn 2 : Set G) :=
    D.M.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image D.M (pCore 2 D.M))
  have hc : ⁅K.subgroupOf H, D.V.subgroupOf H⁆ ≤ B := by
    apply (map_le_map_iff_of_injective H.subtype_injective).mp
    rw [map_commutator, subgroupOf_map_subtype, subgroupOf_map_subtype,
      subgroupOf_map_subtype]
    apply le_inf
    · exact (commutator_mono (inf_le_left.trans hKM) (inf_le_left.trans hV)).trans
        (le_normalizer_iff_commutator_le_right.mp hnorm)
    · exact (Subgroup.commutator_le_sup _ _).trans (sup_le inf_le_right inf_le_right)
  have himage : star H K ≤ B.map q := by
    rw [← hfull]
    exact (map_commutator _ _ q).symm.le.trans (map_mono hc)
  have hp : IsPGroup 2 (star H K) :=
    (((isPGroup_pCoreIn 2 D.M).comap_of_injective H.subtype
      H.subtype_injective).map q).to_le himage
  let := hK.2
  let : IsSimpleGroup ((star H K) ⧸ center (star H K)) := IsQuasisimple.simple
  let : Nontrivial (star H K) :=
    (QuotientGroup.mk'_surjective (center (star H K))).nontrivial
  let : Group.IsNilpotent (star H K) := hp.isNilpotent
  exact Group.IsPerfect.not_isSolvable (star H K) inferInstance

/-- Component selection from the preceding odd-core conclusion and the
earlier Sylow-centrality. Evenness is retained as the universal earlier
simple-section input, not assumed for a newly chosen family tag. -/
theorem exists_selectedComponent {H : Subgroup G}
    (hT : (D.T : Subgroup G) ≤ H)
    (hVcore : D.V ≤ D.M.pCoreIn 2)
    (hne : star H D.V ≠ ⊥)
    (hF : star H D.V ≤ centralizer (fittingSubgroup (Hstar H) : Set (Hstar H)))
    (hcentral : star H D.V ≤ centralizer (D.Tstar H hT : Set (Hstar H)))
    (heven : ∀ J : Subgroup (Hstar H), IsComponent (Hstar H) J →
      2 ∣ Nat.card (J ⧸ center J)) :
    Nonempty (D.SelectedComponent H) := by
  let : IsElementaryAbelian 2 D.V := D.elementary
  have hV : IsPGroup 2 (D.V.subgroupOf H) :=
    (IsElementaryAbelian.isPGroup 2 D.V).comap_of_injective
      H.subtype H.subtype_injective
  obtain ⟨J, hJ, hj, hm⟩ := exists_cComponent_moved_in_twoCore_quotient
    (D.V.subgroupOf H) hV hne hF
  let K := J.map H.subtype
  have hKH : K ≤ H := map_subtype_le J
  have hsub : K.subgroupOf H = J := by
    exact comap_map_eq_self_of_injective H.subtype_injective J
  have hstar : star H K = J.map (QuotientGroup.mk' (pCore 2 H)) := by
    rw [star, hsub]
  have hk : IsComponent (Hstar H) (star H K) := hstar.symm ▸ hj
  have hmove : ⁅star H K, star H D.V⁆ ≠ ⊥ := hstar.symm ▸ hm
  have hn := hk.centralizes_sylow_normalizes (D.Tstar H hT) (heven _ hk) hcentral
  have hfull := hk.commutator_eq_self_of_normalizes hn hmove
  exact ⟨⟨K, hKH, hsub.symm ▸ hJ, hk, hmove, hn, hfull,
    D.component_not_le_M hk hVcore hfull⟩⟩

/-- Actual application to the contrary-nonabelian branch: nontriviality
of V* is derived by 12.6.25 rather than inserted into the source input. -/
theorem selectedComponent_of_nonabelian {H : Subgroup G}
    (h : (D.f9 H).Hypothesis)
    (hC : centralizer (D.V₅ : Set G) = centralizer (D.V : Set G))
    (hnonab : ¬ IsMulCommutative (D.VH H))
    (hT : (D.T : Subgroup G) ≤ H)
    (hVcore : D.V ≤ D.M.pCoreIn 2)
    (hF : star H D.V ≤ centralizer (fittingSubgroup (Hstar H) : Set (Hstar H)))
    (hcentral : star H D.V ≤ centralizer (D.Tstar H hT : Set (Hstar H)))
    (heven : ∀ J : Subgroup (Hstar H), IsComponent (Hstar H) J →
      2 ∣ Nat.card (J ⧸ center J)) : Nonempty (D.SelectedComponent H) :=
  D.exists_selectedComponent hT hVcore (D.nonabelian_inputs h hC hnonab).2.2
    hF hcentral heven

end CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup
