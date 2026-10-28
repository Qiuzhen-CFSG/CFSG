module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsGlobalOrdinaryComponent
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Components.Selection

/-!
# Actual component selection in the original contrary HS branch

The returned common residual directly supplies a moved ordinary normal
component in the singular star group. Thus selection needs neither an
assumed component nor the later nonsingular-centralizer control. Normality
gives the full module commutator, and the original V ≤ O₂(M) excludes
containment in the original maximal local subgroup.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original escaping HS configuration supplies a genuine selected
ordinary component, with all selection fields derived on the original
singular centralizer. -/
theorem SourceHypothesis.exists_original_hs_selected_component
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L) :
    ∃ hZ : ZV L V = ⊥, ∃ z : V, z ≠ 1 ∧ ¬ D.Nonsingular z ∧
      (T : Subgroup G) ≤ Gv (z : G) ∧ ¬ Gv (z : G) ≤ M L ∧
      Gv (z : G) ∈ (D.fullSetup hZ T z).Hz ∧
      Nonempty ((D.fullSetup hZ T z).SelectedComponent (Gv (z : G))) := by
  obtain ⟨hZ,u,w,_,_,_,P,t,_,_,_,hz,hsz,hTz,_,hout,hHz,
    _,_,_,_,_,K,hKG,hK,hordinary,_,hKN,_,_,hmove⟩ :=
    H.exists_original_hs_ordinary_normal_overcomponent D hTV hTI v hv he
  let z := u*w
  let X := Gv (z : G)
  let E := D.fullSetup hZ T z
  let π := QuotientGroup.mk' (pCore 2 X)
  let K₀ := K.subgroupOf X
  let K₁ := K₀.map π
  have hHz' : X ∈ E.Hz := by rwa [E.Gz_eq] at hHz
  let eK : K ≃* K₀ := (subgroupOfEquivOfLe hKG).symm
  let d : (K ⧸ pCore 2 K) ≃* K₁ :=
    (QuotientGroup.congr _ _ eK (pCore_map_iso 2 eK)).trans
      (cComponentTwoCoreQuotientEquiv hK)
  let : IsQuasisimple K₁ := hordinary.of_mulEquiv d
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer hKN
  let : K₁.Normal := Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  have hc : IsComponent (X ⧸ pCore 2 X) K₁ :=
    ⟨(inferInstance : K₁.Normal).isSubnormal,inferInstance⟩
  have hn : Nonabelian.Setup.star X V ≤ normalizer (K₁ : Set (X ⧸ pCore 2 X)) :=
    le_normalizer_of_normal
  have hm : ⁅K₁,Nonabelian.Setup.star X V⁆ ≠ ⊥ := by
    intro hh
    have hi : ⁅K₀,V.subgroupOf X⁆ ≤ pCore 2 X := by
      have hmap : (⁅K₀,V.subgroupOf X⁆).map π = ⊥ := by
        rw [map_commutator]
        exact hh
      simpa only [π,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hmap
    have ha := map_mono (f := X.subtype) hi
    rw [map_commutator,map_subgroupOf_eq_of_le hKG,
      map_subgroupOf_eq_of_le (V_le_Gv z),commutator_comm] at ha
    exact hmove ha
  have hfull := hc.commutator_eq_self_of_normalizes hn hm
  have hVM : V ≤ (M L).pCoreIn 2 := H.chosen.le_componentCore.trans
    (pCoreIn_mono_of_normalizes L.le_normalizer (le_refl (M L)))
  have houtside : ¬ K ≤ M L := E.component_not_le_M hc hVM hfull
  refine ⟨hZ,z,hz,hsz,hTz,hout,hHz',?_⟩
  exact ⟨⟨K,hKG,hK,hc,hm,hn,hfull,houtside⟩⟩

end CFSG.Quasithin.Chapter12.Section06
