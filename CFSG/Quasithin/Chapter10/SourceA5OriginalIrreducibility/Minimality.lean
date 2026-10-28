module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalModuleMarking
public import CFSG.Quasithin.Chapter3.Section02.MinimalModuleSelection
public import Theory.GroupTheory.ReducedNormal.MovedConstituent

/-!
# Minimal full modules contain no proper moved invariant subgroup

For an M-invariant subgroup U of the original full module, A.4.11 constructs
an actual reduced constituent whenever L moves U. The original3.2.3 choice
then gives another Fundamental Setup with full module contained in U.
Minimal full-module order forces U to be the whole original module.
Thus the source reselection argument needs a proper invariant moved subgroup,
without a preselected reduced seed or a replacement setup as an input.

Source: Aschbacher–Smith,D.3.21 and3.2.6, printed pp.204–207 and581.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem minimalMoved_chief {Q : Type*} [Group Q] [Finite Q]
    [IsQuasisimple Q] : HasCentralPChiefFactors 2 Q := by
  let e : (Q ⧸ (⊥ : Subgroup Q)) ≃* Q := QuotientGroup.quotientBot
  let : IsQuasisimple (Q ⧸ (⊥ : Subgroup Q)) := IsQuasisimple.of_mulEquiv e.symm
  exact hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient
    (⊥ : Subgroup Q) (by simp) inferInstance

theorem source_minimal_fullModule_eq_of_normal_moved
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) (hD : D.IsMinimalFullModule)
    (U : Subgroup G) (hU : D.maximalLocal ≤ normalizer (U : Set G))
    (hUD : U ≤ D.fullModule) (hmoved : ⁅U,L⁆ ≠ ⊥) : U = D.fullModule := by
  let H := localJoin T L
  let X := L.subgroupOf H
  let Y := (localOrbit T L).subgroupOf H
  let B := U.subgroupOf H
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  have hUH : U ≤ H := hUD.trans (D.fullModule_le_orbit.trans le_sup_left)
  have hHM : H ≤ D.maximalLocal :=
    sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
  let : B.Normal := normal_subgroupOf_of_le_normalizer (hHM.trans hU)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun A _ _ => ChapterA.Section02.theoremA_knownSimple (G := A))
    (fun A _ _ => ChapterA.Section02.theoremC_knownSimple (G := A))
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.of_le hUD
  let : IsElementaryAbelian 2 B :=
    IsElementaryAbelian.comap_of_injective H.subtype H.subtype_injective U
  let e : X ≃* L := subgroupOfEquivOfLe hLH
  have hp : IsPPerfect 2 X := D.faithful.1.2.1.of_surjective
    e.symm.toMonoidHom e.symm.surjective
  have hs : X.IsSubnormal := by
    change (L.subgroupOf (componentOrbit L T ⊔ (T : Subgroup G))).IsSubnormal
    rw [componentOrbit_sup]
    exact D.maximal.1.1.subnormal
  let eq := QuotientGroup.congr (pCore 2 X) (pCore 2 L) e (pCore_map_iso 2 e)
  let := D.quasisimple
  let : IsQuasisimple (X ⧸ pCore 2 X) := IsQuasisimple.of_mulEquiv eq.symm
  have hc : HasCentralPChiefFactorsAbove 2 (pCore 2 X) :=
    (hasCentralPChiefFactorsAbove_iff_quotient _).mpr minimalMoved_chief
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect (localOrbit T L) := isPerfect_iSup_conjugates L T
  let eY : Y ≃* localOrbit T L := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect Y :=
    Group.IsPerfect.ofSurjective (f := eY.symm.toMonoidHom) eY.symm.surjective
  have hkill : (pCore 2 X).map X.subtype ≤ centralizer (B : Set H) := by
    have hcore : (X.pCoreIn 2).map H.subtype ≤ centralizer (U : Set G) := by
      rw [map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
        map_subgroupOf_eq_of_le hLH]
      exact (source_component_core_centralizes_fullModule D).trans (centralizer_le hUD)
    intro x hx b hb
    apply Subtype.ext
    exact hcore (mem_map_of_mem H.subtype hx) b hb
  have hm : ⁅B,X⁆ ≠ ⊥ := by
    intro h
    apply hmoved
    have h' := congrArg (Subgroup.map H.subtype) h
    simpa only [B,X,map_commutator,map_subgroupOf_eq_of_le hUH,
      map_subgroupOf_eq_of_le hLH,Subgroup.map_bot] using h'
  obtain ⟨I,hI,hIU⟩ := ReducedNormal.exists_irrPlus_subspace_le_of_moved
    H X Y B (comap_mono (le_componentOrbit L T)) hs hp hc hkill hm
  have hIU' : ReducedNormal.subspaceImage H I ≤ U := by
    simpa only [B,map_subgroupOf_eq_of_le hUH] using hIU
  exact hD.eq_of_contains_irrPlus I hI U hIU' hU hUD
end CFSG.Quasithin.Chapter10
