module
public import CFSG.Quasithin.Chapter10.SourceA5PointCentralizerConstrained
public import Theory.GroupTheory.CentralSylowNormalClosure
public import Theory.GroupTheory.ConjugateSpanSupplement
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
/-!
# The literal reduced module in the constrained source point centralizer

Let S=C_T(v), J=IS and Z=C_[V,L](S). The previously proved
characteristic-two entry makes the J-normal closure of Z elementary.
Sylow inheritance makes it reduced. Since S centralizes Z and normalizes
I, its J-orbit is exactly its I-orbit; hence the reduced subgroup is
literally <C_[V,L](C_T(v))^I>, with the source actor J unchanged.
Source: Aschbacher–Smith10.2.9, printed p.751, using B.2.14.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
/-- The precise B2.14 reduced module used in the constrained source branch,
retaining the original fixed space and the containing component orbit. -/
theorem source_a5_point_component_reduced_module
    {v : G} (hv : v ∈ D.fullModule) (hvne : v ≠ 1)
    (hvL : v ∈ centralizer (L : Set G))
    (hCW : centralizer (↑(⁅D.fullModule,L⁆ : Subgroup G) : Set G) ≤ D.maximalLocal)
    (I : Subgroup G) (hLI : L ≤ I) (hIX : I ≤ centralizer ({v} : Set G))
    (hI : (I.subgroupOf (centralizer ({v} : Set G))).IsCComponent)
    (hNI : centralizer ({v} : Set G) ≤ normalizer (I : Set G))
    (hnot : ¬ IsQuasisimple I)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({v} : Set G))
      (centralizer ({v} : Set G))) :
    let S := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
    let J := I ⊔ S
    let Z := ⁅D.fullModule,L⁆ ⊓ centralizer (S : Set G)
    IsPReduced 2 ((conjugateSpanBy Z I).subgroupOf J) := by
  dsimp only
  let S := (T : Subgroup G) ⊓ centralizer ({v} : Set G)
  let J := I ⊔ S
  let W := ⁅D.fullModule,L⁆
  let Z := W ⊓ centralizer (S : Set G)
  have hZJ : Z ≤ J := inf_le_left.trans ((source_full_moved_le_component D).trans (hLI.trans le_sup_left))
  have hZT : Z ≤ (T : Subgroup G) := by
    have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
      D.simpleQTKE T D.maximal
    have hWV : W ≤ D.fullModule := le_normalizer_iff_commutator_le_left.mp
      (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
        D.maximalLocal_normalizes_fullModule)
    exact inf_le_left.trans (hWV.trans (D.fullModule_le_sylow hu))
  have hZS : Z ≤ S := le_inf hZT
    (inf_le_left.trans ((source_full_moved_le_component D).trans (hLI.trans hIX)))
  have hSJ : Chapter1.IsSylowIn 2 S J := hs.restrict le_sup_right (sup_le hIX inf_le_right)
  obtain ⟨P,hP⟩ := hSJ
  have hP' : (P : Subgroup J) = S.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le le_sup_right]
  have hchar : centralizer (pCore 2 J : Set J) ≤ pCore 2 J := by
    rw [←source_a5_point_component_characteristicTwo D hv hvne hvL hCW I hIX hI hnot]
    exact centralizer_generalizedFitting_le J
  let : IsElementaryAbelian 2 W := source_original_full_moved_elementary D
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_le inf_le_left
  let : IsElementaryAbelian 2 (Z.subgroupOf J) := IsElementaryAbelian.subgroupOf hZJ
  have hZP : Z.subgroupOf J ≤ (P : Subgroup J) := by
    rw [hP']
    exact comap_mono hZS
  have hc : Z.subgroupOf J ≤ centralizer (P : Set J) := by
    intro z hz p hp
    apply Subtype.ext
    have hpS : p ∈ S.subgroupOf J := hP' ▸ hp
    exact hz.2 p hpS
  have hE := (central_sylow_normalClosure_elementary P (Z.subgroupOf J) hc hchar).1
  let : IsElementaryAbelian 2 (normalClosure (Z.subgroupOf J : Set J)) := hE
  have hr := isPReduced_normalClosure_of_sylow_central P (Z.subgroupOf J) hZP hc
  have hZI : conjugateSpanBy Z J = conjugateSpanBy Z I :=
    conjugateSpanBy_sup_of_normalizes_seed Z I S
      ((le_centralizer_iff.mp inf_le_right).trans (Subgroup.centralizer_le_normalizer _))
      (inf_le_right.trans hNI)
  rw [normalClosure_subgroupOf_eq_conjugateSpanBy Z J hZJ,hZI] at hr
  exact hr
end CFSG.Quasithin.Chapter10
