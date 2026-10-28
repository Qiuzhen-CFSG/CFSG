module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.Sections
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.OddBenderOdd
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.TwoRank
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining
/-!
# A containing component of the local A₈ section is quasisimple

A solvable-kernel map preserves the smaller A₈ two-core quotient. Thus the
noncentral-Fitting alternative, whose Fitting quotient is SL₂(p), is
impossible: projecting again to PSL₂(p) contradicts the cyclic derived
subgroups of its Sylow two-groups. The remaining Fitting subgroup is
central, so the containing C-component is quasisimple.

Source: Aschbacher–Smith A.3.6 and15.3.32(3), printed pp.43–45 and1133.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- No perfect subgroup with the A₈ two-core quotient lies in odd prime-field SL₂. -/
theorem not_section_specialLinear_two (B : Subgroup G) [Group.IsPerfect B]
    (hB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hm : IsSL G 2 p) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let f : G →* PSL(2,F) := (QuotientGroup.mk' (center SL(2,F))).comp e.toMonoidHom
  have hk : f.ker ≤ center G := by
    intro x hx
    have hz : e x ∈ center SL(2,F) := (QuotientGroup.eq_one_iff _).mp hx
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    simpa only [map_mul] using mem_center_iff.mp hz (e y)
  let : Group.IsSolvable (center G) := Group.isSolvable_of_comm (fun a b => Subtype.ext
    (mem_center_iff.mp a.property b).symm)
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hk) (inclusion_injective hk)
  have hm' : ChapterA.Section02.IsTheoremCOddModel PSL(2,F) :=
    .linear_two p 1 hp ho (by decide) ⟨F, inferInstance, inferInstance,
      by simpa only [pow_one] using hF, ⟨MulEquiv.refl _⟩⟩
  exact not_linearFourTwo_section_of_odd_model hm' (B.map f) (section_map B hB f)

/-- Quasisimplicity of the actual containing C-component, without a rank-lifting premise. -/
theorem containing_quasisimple (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hO : pCore 2 G = ⊥) (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hsection : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) : IsQuasisimple K := by
  have hfit : fittingSubgroup K ≤ center K := by
    by_contra hn
    obtain ⟨p,hp,hp3,⟨e⟩⟩ := NoncentralFitting.primeSL2FittingQuotient_of_noncentral
      RankActions.primeSL2CoverRigidity hG hO hK hn
    let : Fact p.Prime := ⟨hp⟩
    let q := QuotientGroup.mk' (fittingSubgroup K)
    let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
    have hlocal := local_restrict hB hBK
    let : Group.IsPerfect (B.subgroupOf K) := by
      let := hlocal.perfect
      let a := subgroupOfEquivOfLe (show B.subgroupOf K ≤ B.subgroupOf K ⊔ (T : Subgroup G).subgroupOf K from le_sup_left)
      exact Group.IsPerfect.ofSurjective (f := a.toMonoidHom) a.surjective
    have hsmall : ClassicalGroup.IsPSL ((B.subgroupOf K) ⧸ pCore 2 (B.subgroupOf K)) 4 2 :=
      hsection.of_mulEquiv (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBK)
        (pCore_map_iso 2 (subgroupOfEquivOfLe hBK)))
    let : Group.IsPerfect ((B.subgroupOf K).map q) :=
      Group.IsPerfect.ofSurjective (f := q.subgroupMap (B.subgroupOf K))
        (q.subgroupMap_surjective _)
    exact not_section_specialLinear_two ((B.subgroupOf K).map q)
      (section_map _ hsmall q) hp (hp.odd_of_ne_two (by omega))
      ⟨ZMod p, inferInstance, inferInstance, Nat.card_zmod p, ⟨e⟩⟩
  have hs : solvableRadical K = center K := by
    apply le_antisymm (solvableRadical_le_center_of_fitting_le_center hfit)
    exact le_solvableRadical (center K) inferInstance
      (Group.isSolvable_of_comm (fun a b => Subtype.ext
        (mem_center_iff.mp a.property b).symm))
  let := hK.perfect
  let := hK.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hs).symm.isSimpleGroup⟩
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
