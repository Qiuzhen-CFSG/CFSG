module

public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalSeedPlacement
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.StarModels
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoImages
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The original seed two-core in the literal star image

The star map has solvable kernel. Its restriction to the original perfect
A₅ seed therefore has kernel inside the seed's two-core. The restricted
surjection carries the original two-core onto the complete two-core of the
seed image. The identity retains the original ambient subgroup and any
chosen marking of the selected component's actual star image.

Source: the core-fixed module transport in Aschbacher--Smith C.4.8 and
12.7.5, printed pp.154 and 840.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

/-- The actual star map carries the original seed two-core onto the full
embedded two-core of its literal image, under any chosen star marking. -/
theorem constrained_normal_seed_core_image
    {G S : Type*} [Group G] [Finite G] [Group S]
    {H M L R V : Subgroup G}
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal)
    (eA5 : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (J : Subgroup H) (hJ : J.IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) (hout : ¬ J ≤ M.subgroupOf H)
    (hf : generalizedFitting J = pCore 2 J)
    (e : starImage (J.map H.subtype) R (J.map H.subtype) ≃* S) :
    let q := e.toMonoidHom.comp (toStarImage (J.map H.subtype) R)
    ((L.pCoreIn 2).subgroupOf (J.map H.subtype)).map q =
      ((L.subgroupOf (J.map H.subtype)).map q).pCoreIn 2 := by
  let K := J.map H.subtype
  let q := e.toMonoidHom.comp (toStarImage K R)
  let A := L.subgroupOf K
  let B := A.map q
  let : Finite S := Finite.of_injective e.symm e.symm.injective
  have hLK : L ≤ K := by
    intro l hl
    exact ⟨⟨l,h.local_le (h.component_le hl)⟩,
      h.constrained_normal_seed_le hn J hJ hq hout hf hl,rfl⟩
  have hi := h.constrained_source_input J hJ hq hout hf
  let : Group.IsPerfect (L.subgroupOf M) := h.component.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h.component_le).toMonoidHom)
    (subgroupOfEquivOfLe h.component_le).surjective
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (L ⧸ pCore 2 L) := eA5.isSimpleGroup
  have hker : q.ker = (toStarImage K R).ker := by
    ext x
    change e (toStarImage K R x) = 1 ↔ toStarImage K R x = 1
    exact e.map_eq_one_iff
  let : Group.IsSolvable q.ker := by
    rw [hker]
    exact C27Source.toStarImage_ker_solvable_from_source hi
  let qL : L →* B := (q.subgroupMap A).comp (subgroupOfEquivOfLe hLK).symm.toMonoidHom
  have hqL : Function.Surjective qL :=
    (q.subgroupMap_surjective A).comp (subgroupOfEquivOfLe hLK).symm.surjective
  let j : qL.ker →* q.ker :=
    ((inclusion hLK).comp qL.ker.subtype).codRestrict _ (by
      intro x
      exact congrArg Subtype.val x.property)
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : q.ker => ((z : K) : G)) he))
  let : Group.IsSolvable qL.ker := Group.isSolvable_of_isSolvable_injective hj
  have hk : IsPGroup 2 qL.ker :=
    pCore_isPGroup.to_le (PerfectCoreTwoExtension.solvable_ker_le_core qL)
  have hc : (pCore 2 L).map qL = pCore 2 B := by
    rw [←qL.comap_pCore_of_ker_isPGroup hqL hk,map_comap_eq_self_of_surjective hqL]
  have hleft : ((L.pCoreIn 2).subgroupOf K).map q =
      ((pCore 2 L).map qL).map B.subtype := by
    ext x
    constructor
    · rintro ⟨k,⟨l,hl,he⟩,rfl⟩
      refine ⟨qL l,mem_map_of_mem _ hl,?_⟩
      exact congrArg q (Subtype.ext he)
    · rintro ⟨b,⟨l,hl,rfl⟩,rfl⟩
      exact ⟨inclusion hLK l,⟨l,hl,rfl⟩,rfl⟩
  exact hleft.trans (congrArg (map B.subtype) hc)

end CFSG.Quasithin.ChapterC.HypothesisC28
