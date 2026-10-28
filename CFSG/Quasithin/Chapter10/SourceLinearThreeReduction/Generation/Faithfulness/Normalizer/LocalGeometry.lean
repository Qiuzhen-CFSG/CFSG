module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.Placement
public import Theory.GroupTheory.PCoreCoverEquiv
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.SubgroupTransport
public import Theory.ElementaryAbelian.Injective

/-!
# The original local geometry inside a containing normalizer component

The fixed perfect residual covers L₀ modulo O₂(L₀), so its intrinsic
two-core quotient is identified with the original orbit quotient by the
literal inclusion. Once the residual is placed in K, the original full
module and M-intersection give a nontrivial moved elementary two-subgroup,
its exact normalizer, and a perfect subgroup carrying that quotient.
This supplies the local data required by the remaining model inspection.

Source: Aschbacher--Smith, 4.4.5 and 4.4.10--12, printed pp.620--622
(combined manuscript of 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D in
/-- The residual quotient map is induced by its original inclusion in L₀. -/
theorem source_oddActorResidual_orbit_quotient_equiv
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) :
    let X := localOrbit T L
    let F := (solvableResidual (X ⊓ centralizer (B : Set G) : Subgroup G)).map
      (X ⊓ centralizer (B : Set G)).subtype
    let hFX : F ≤ X := (map_subtype_le _).trans inf_le_left
    ∃ q : (F ⧸ pCore 2 F) ≃* (X ⧸ pCore 2 X),
      ∀ x : F, q (QuotientGroup.mk' (pCore 2 F) x) =
        QuotientGroup.mk' (pCore 2 X) (inclusion hFX x) := by
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect (localOrbit T L) := isPerfect_iSup_conjugates L (T : Subgroup G)
  exact exists_pCoreQuotientEquiv_of_cover ((map_subtype_le _).trans inf_le_left)
    (perfect_centralizer_cover (localOrbit T L) B hBC hodd).subset

/-- The literal residual and full module inside a containing component form
an actual two-local marking with the original orbit quotient. -/
theorem source_oddNormalizer_component_local_geometry_of_residual_le
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K) :
    let N := normalizer (B : Set G)
    let F := ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
    let P := F.subgroupOf K
    let W := (D.fullModule.subgroupOf N).subgroupOf K
    let MK := (D.maximalLocal.subgroupOf N).subgroupOf K
    Group.IsPerfect P ∧ P ≤ MK ∧ MK ≤ normalizer (P : Set K) ∧
      W ≠ ⊥ ∧ IsElementaryAbelian 2 W ∧ W ≤ P.pCoreIn 2 ∧
      W = ⁅W,P⁆ ∧ normalizer (W : Set K) = MK ∧
      Nonempty ((P ⧸ pCore 2 P) ≃*
        (localOrbit T L ⧸ pCore 2 (localOrbit T L))) := by
  let N := normalizer (B : Set G)
  let C := localOrbit T L ⊓ centralizer (B : Set G)
  let F := (solvableResidual C).map C.subtype
  let F0 := F.subgroupOf N
  let P := F0.subgroupOf K
  let U := D.fullModule.subgroupOf N
  let W := U.subgroupOf K
  let Y := D.maximalLocal.subgroupOf N
  let MK := Y.subgroupOf K
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hVN : D.fullModule ≤ N := (le_centralizer_iff.mp hBV).trans
    (Subgroup.centralizer_le_normalizer _)
  obtain ⟨_,hm,hVF⟩ := source_fullModule_oddActor_cover D B hBC hodd hBV
  have hUF : U ≤ F0 := subgroupOf_mono N (hVF.trans (pCoreIn_le 2 F))
  have hUK : U ≤ K := hUF.trans hFK
  let a : P ≃* F := (subgroupOfEquivOfLe hFK).trans (subgroupOfEquivOfLe hFN)
  let := source_oddNormalizer_residual_perfect (T := T) (L := L) B
  let : Group.IsPerfect P := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hFK).symm.toMonoidHom)
    (subgroupOfEquivOfLe hFK).symm.surjective
  have hFY : F ≤ D.maximalLocal :=
    ((map_subtype_le _).trans inf_le_left).trans (localOrbit T L).le_normalizer
  have hYF : Y ≤ normalizer (F0 : Set N) := by
    have hnorm : D.maximalLocal ⊓ N ≤ normalizer (F : Set G) :=
      ((le_inf inf_le_left (inf_le_right.trans (normalizer_le_normalizer_centralizer B))).trans
        inf_normalizer_le_normalizer_inf).trans
          (normalizer_le_normalizer_characteristic_image C (solvableResidual C))
    intro y hy f
    exact hnorm ⟨hy,y.property⟩ (f : G)
  have hMP : MK ≤ normalizer (P : Set K) := by
    rw [←subgroupOf_normalizer_eq hFK]
    exact subgroupOf_mono K hYF
  have hW : W ≠ ⊥ := by
    intro hb
    have hbV : D.fullModule = ⊥ := by
      apply le_bot_iff.mp
      intro v hv
      have hw : (⟨⟨v,hVN hv⟩,hUK hv⟩ : K) ∈ W := hv
      have he := mem_bot.mp (hb ▸ hw)
      exact mem_bot.mpr (congrArg (fun x : K => x.val.val) he)
    exact D.module_ne_bot
      (bot_unique ((le_componentOrbit D.moduleSubgroup D.maximalLocal).trans hbV.le))
  have heW : IsElementaryAbelian 2 W := by
    let := D.fullModule_elementary (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      D.simpleQTKE T D.maximal)
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.comap_of_injective (p := 2)
      N.subtype N.subtype_injective D.fullModule
    exact IsElementaryAbelian.comap_of_injective (p := 2) K.subtype K.subtype_injective U
  have hWP : W ≤ P.pCoreIn 2 := by
    rw [pCoreIn_subgroupOf 2 F0 K hFK,pCoreIn_subgroupOf 2 F N hFN]
    exact subgroupOf_mono K (subgroupOf_mono N hVF)
  have hmove : W = ⁅W,P⁆ := by
    change U.subgroupOf K = ⁅U.subgroupOf K,F0.subgroupOf K⁆
    rw [←SubgroupTransport.subgroupOf_commutator U F0 hUK hFK,
      ←SubgroupTransport.subgroupOf_commutator D.fullModule F hVN hFN,←hm]
  have hnormal : normalizer (W : Set K) = MK := by
    rw [←subgroupOf_normalizer_eq hUK,←subgroupOf_normalizer_eq hVN,
      source_fullModule_normalizer D]
  obtain ⟨q,_⟩ := source_oddActorResidual_orbit_quotient_equiv (D := D) (B := B) hBC hodd
  exact ⟨inferInstance,subgroupOf_mono K (subgroupOf_mono N hFY),hMP,hW,heW,hWP,
    hmove,hnormal,⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans q⟩⟩

/-- Apply placement and local geometry to a selected elementary subgroup of
an actual Hall kernel. The literal section kernel and full-module fixation
are retained; covering uniqueness and soluble outer action are the two
remaining premises of this placement step. -/
theorem source_hall_kernel_component_local_geometry
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (B : Subgroup H)
    (hfix : B.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
      centralizer (D.fullModule : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (A : Subgroup G) (hA : IsElementaryAbelian p A)
    (hAB : A ≤ B.map H.subtype) (hAC : A ≤ sectionCentralizer (localOrbit T L))
    (hu : UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (A : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (A : Set G))) D.maximalLocal)
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K) [K.Normal]
    [Group.IsSolvable (MulAut.Outer K)]
    (hout : ¬ K.map (normalizer (A : Set G)).subtype ≤ D.maximalLocal) :
    let N := normalizer (A : Set G)
    let F := ((solvableResidual
      (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (A : Set G)).subtype).subgroupOf N
    let P := F.subgroupOf K
    let W := (D.fullModule.subgroupOf N).subgroupOf K
    let MK := (D.maximalLocal.subgroupOf N).subgroupOf K
    D.fullModule.subgroupOf N ≤ K ∧ centralizer (K : Set N) = pPrimeCore 2 N ∧
      F ≤ K ∧ Group.IsPerfect P ∧ P ≤ MK ∧ MK ≤ normalizer (P : Set K) ∧
      W ≠ ⊥ ∧ IsElementaryAbelian 2 W ∧ W ≤ P.pCoreIn 2 ∧
      W = ⁅W,P⁆ ∧ normalizer (W : Set K) = MK ∧
      Nonempty ((P ⧸ pCore 2 P) ≃*
        (localOrbit T L ⧸ pCore 2 (localOrbit T L))) := by
  have hAV : A ≤ centralizer (D.fullModule : Set G) := (le_inf hAB hAC).trans hfix
  let := hA
  have hodd : Odd (Nat.card A) := by
    obtain ⟨k,hk⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [hk]
    exact hp.pow
  have hYK : D.maximalLocal.subgroupOf (normalizer (A : Set G)) ≤
      normalizer (K : Set (normalizer (A : Set G))) := by
    intro x _
    exact le_normalizer_of_normal (mem_top x)
  have hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (A : Set G)).subtype).subgroupOf
          (normalizer (A : Set G)) ≤ normalizer (K : Set (normalizer (A : Set G))) := by
    intro x _
    exact le_normalizer_of_normal (mem_top x)
  obtain ⟨_,hV,hC,hF⟩ := source_nonnormal_oddNormalizer_component_closure_of_overlap_normalizes
    D hn A hAC hodd hAV hu K hK hout hYK
      (source_oddNormalizer_component_inner A K hK hFK)
  exact ⟨hV,hC,hF,source_oddNormalizer_component_local_geometry_of_residual_le
    D A hAC hodd hAV K hF⟩

end CFSG.Quasithin.Chapter10
