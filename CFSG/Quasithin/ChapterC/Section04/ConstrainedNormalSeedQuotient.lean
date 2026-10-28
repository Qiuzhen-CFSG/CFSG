module
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedNormalSeedCoreImage

/-!
# The original normal A₅ seed quotient under an arbitrary star marking

The same restriction of the star map has a two-group kernel. Consequently
it identifies the original seed quotient by its two-core with the marked
image quotient, and the identification retains the image of every original
element. This is the quotient transport for the original cubic actor.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface

/-- The literal restriction of the marked star map identifies the two
seed quotients, compatibly with every original seed element. -/
theorem constrained_normal_seed_quotient
    {G D : Type*} [Group G] [Finite G] [Group D]
    {H M L R V : Subgroup G}
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (eA5 : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (J : Subgroup H) (hJ : J.IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J)) (hout : ¬ J ≤ M.subgroupOf H)
    (hf : generalizedFitting J = pCore 2 J)
    (hLK : L ≤ J.map H.subtype)
    (E : starImage (J.map H.subtype) R (J.map H.subtype) ≃* D) :
    let K := J.map H.subtype
    let q := E.toMonoidHom.comp (toStarImage K R)
    let B := (L.subgroupOf K).map q
    let qL : L →* B := (q.subgroupMap (L.subgroupOf K)).comp
      (subgroupOfEquivOfLe hLK).symm.toMonoidHom
    Function.Surjective qL ∧ IsPGroup 2 qL.ker ∧
      ∃ a : (L ⧸ pCore 2 L) ≃* (B ⧸ pCore 2 B),
        ∀ l : L, a (QuotientGroup.mk' (pCore 2 L) l) =
          QuotientGroup.mk' (pCore 2 B) (qL l) := by
  let K := J.map H.subtype
  let q := E.toMonoidHom.comp (toStarImage K R)
  let B := (L.subgroupOf K).map q
  let qL : L →* B := (q.subgroupMap (L.subgroupOf K)).comp
    (subgroupOfEquivOfLe hLK).symm.toMonoidHom
  have hqL : Function.Surjective qL := (q.subgroupMap_surjective _).comp
    (subgroupOfEquivOfLe hLK).symm.surjective
  have hker : q.ker = (toStarImage K R).ker := by
    ext x
    exact E.map_eq_one_iff
  let : Group.IsSolvable q.ker := by
    rw [hker]
    exact C27Source.toStarImage_ker_solvable_from_source
      (h.constrained_source_input J hJ hq hout hf)
  let j : qL.ker →* q.ker :=
    ((inclusion hLK).comp qL.ker.subtype).codRestrict _ (by
      intro x
      exact congrArg Subtype.val x.property)
  have hj : Function.Injective j := by
    intro x y he
    exact Subtype.ext (Subtype.ext (congrArg (fun z : q.ker => ((z : K) : G)) he))
  let : Group.IsSolvable qL.ker := Group.isSolvable_of_isSolvable_injective hj
  let : Group.IsPerfect (L.subgroupOf M) := h.component.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h.component_le).toMonoidHom)
    (subgroupOfEquivOfLe h.component_le).surjective
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (L ⧸ pCore 2 L) := eA5.isSimpleGroup
  have hk : IsPGroup 2 qL.ker :=
    pCore_isPGroup.to_le (PerfectCoreTwoExtension.solvable_ker_le_core qL)
  let : Finite D := Finite.of_injective E.symm E.symm.injective
  exact ⟨hqL,hk,qL.pCoreQuotientEquiv hqL hk,fun _ => rfl⟩

end CFSG.Quasithin.ChapterC.HypothesisC28
