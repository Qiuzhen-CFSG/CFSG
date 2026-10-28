module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.Sections
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional.OddModels
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.TwoRank
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining
/-!
# Quasisimplicity of a component containing an exceptional local section

A solvable-kernel map preserves the actual exceptional simple two-core
quotient. The noncentral-Fitting case would put this quotient in a
prime-field SL₂ section. Its projective image is impossible because odd
Theorem C Sylow groups have cyclic commutator subgroups, whereas each
exceptional model has a noncyclic Sylow commutator. The containing
component consequently has central Fitting subgroup and is quasisimple.

Source: Aschbacher–Smith A.3.6 and A.3.12, printed pp.43–48.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- No perfect subgroup with an exceptional two-core quotient lies in odd prime-field SL₂. -/
theorem not_section_specialLinear_two (B : Subgroup G) [Group.IsPerfect B]
    (hB : IsModel (B ⧸ pCore 2 B))
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
  exact not_section_of_odd_model hm' (B.map f) (section_map B hB f)

/-- Quasisimplicity of the actual containing C-component, without a rank-lifting premise. -/
theorem containing_quasisimple (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (hO : pCore 2 G = ⊥) (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B ≤ K)
    (hsection : IsModel (B ⧸ pCore 2 B)) : IsQuasisimple K := by
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
    have hsmall : IsModel ((B.subgroupOf K) ⧸ pCore 2 (B.subgroupOf K)) :=
      hsection.of_equiv (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hBK)
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
end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Exceptional
