module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.MixedGeometry.Prebranch
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.ComponentElimination.Actions

/-!
# Original source inputs for mixed component recognition

The constructed mixed centralizer supplies one actual Sylow and the original
local 1.1.5 hypotheses. Applying the complete ABC classifier on these same
subgroups gives characteristic-two involution centralizers and the faithful
central-omega action on every ordinary component. The quotient and subgroup
maps are retained literally when passing to the intrinsic mixed group.

Source: Aschbacher--Smith, proof of 15.4.18, pp.1162--1163.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource
open FamilySource FamilySource.ModuleStructure LocalSetup
open LocalSetup.TwoFactors LocalSetup.TwoFactors.MixedLocal
open Chapter15.Section03.Candidates.ComponentStructure
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original marked local hypotheses supply all component-action inputs. -/
theorem source_mixed_component_inputs {κ : GroupClass.{u}}
    (hABC : ∀ (A : Type u) [Group A] [Finite A], ChapterA.Section02.TheoremsABC κ A)
    {T : Sylow 2 G} {M₁ M₂ Y X : Subgroup G} {F : Bool → Subgroup G}
    (hY : Input κ T M₁ Y 1) (c : Configuration κ T Y X M₂ F) :
    let I := generated T Y F
    let Z := (omegaOneCenterAmbient (T : Subgroup G)).subgroupOf I
    pPrimeCore 2 I = ⊥ ∧
      (∀ z : Z, z ≠ 1 → HasCharacteristicTwo (centralizer ({(z : I)} : Set I))) ∧
      (∀ L : Subgroup I, IsComponent I L →
        (Z ≤ normalizer (L : Set I) ∧ Z ⊓ centralizer (L : Set I) = ⊥) ∧
        ∀ z : Z, z ≠ 1 → HasModelAction115 L (z : G)) := by
  let I := generated T Y F
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  obtain ⟨P,hP,hlocal,hodd,_⟩ := source_mixed_prebranch hY c
  have hZI : Z ≤ I := by
    intro z hz
    obtain ⟨hzT,_,hzc⟩ := (mem_omegaOneCenterAmbient_iff _ _).mp hz
    have hzC : z ∈ centralizer (commonFixed T Y F : Set G) := by
      intro e he
      exact hzc e ((c.common_le_stabilizer he).1)
    have hzU : z ∈ stabilizer T F := c.sylow_intersection ▸ ⟨hzT,hzC⟩
    exact (show stabilizer T F ≤ I from le_sup_right.trans le_sup_left) hzU
  refine ⟨hodd,?_,?_⟩
  · intro z hz1
    have hzg : (z : G) ≠ 1 := by
      intro he
      exact hz1 (Subtype.ext (Subtype.ext he))
    obtain ⟨M,hm⟩ := hlocal z z.property hzg
    exact hm.intrinsic_centralizer_characteristicTwo
  · intro L hL
    let A := L.map I.subtype
    have hAI : A ≤ I := map_subtype_le _
    have hback : A.subgroupOf I = L :=
      comap_map_eq_self_of_injective I.subtype_injective L
    have hact := ComponentElimination.component_actions_of_earlier115 hY.ambient
      (SourceRecognition.Source.earlier115Three hABC)
      (H := I) (Z := Z) (L := A) (fun z hz hz1 => by
        obtain ⟨M,hm⟩ := hlocal z hz hz1
        exact ⟨P,M,hm⟩) hAI (hback.symm ▸ hL)
    have hn : Z.subgroupOf I ≤ normalizer (L : Set I) := by
      rw [← hback,← subgroupOf_normalizer_eq hAI]
      intro z hz
      exact hact.1 hz
    have hf : Z.subgroupOf I ⊓ centralizer (L : Set I) = ⊥ := by
      apply map_injective I.subtype_injective
      rw [map_inf _ _ _ I.subtype_injective,map_subgroupOf_eq_of_le hZI,
        map_centralizer_subtype,Subgroup.map_bot,← inf_assoc,inf_of_le_left hZI]
      exact hact.2.2.1
    refine ⟨⟨hn,hf⟩,?_⟩
    intro z hz1
    have hzg : (z : G) ≠ 1 := by
      intro he
      exact hz1 (Subtype.ext (Subtype.ext he))
    have hm := hact.2.2.2 z z.property hzg
    rwa [hback] at hm

end CFSG.Quasithin.Chapter15.Section04.InitialSource
