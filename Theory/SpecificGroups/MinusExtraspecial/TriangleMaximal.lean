module
public import Theory.SpecificGroups.MinusExtraspecial.AlternatingCentralModule
public import Theory.GroupTheory.SplitExtensionGivenComplement
public import Theory.Representation.BinaryAlternatingFiveExtension.ComplementOvergroups
public import Theory.GroupTheory.QuotientIntersection

/-!
# Maximality of the actual central A₅ supplement

The full central quotient has its natural binary A₅ module. A subgroup
meeting the full extraspecial core precisely in the center and supplementing
that core maps to an actual affine complement. Irreducibility makes every
overgroup of this subgroup either itself or the whole original group.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace MinusExtraspecial

/-- Maximality retains the actual core, central line, and chosen supplement. -/
theorem triangle_overgroup_eq_or_top {H : Type*} [Group H]
    (Q R K : Subgroup H) [Q.Normal]
    (eQ : Q ≃* Model) (hself : centralizer (Q : Set H) ≤ Q)
    (eA : (H ⧸ Q) ≃* alternatingGroup (Fin 5))
    (hinf : Q ⊓ R = center H) (hsup : Q ⊔ R = ⊤) (hRK : R ≤ K) :
    K = R ∨ K = ⊤ := by
  let q := QuotientGroup.mk' (center H)
  have hZR : center H ≤ R := hinf ▸ inf_le_right
  have hZK : center H ≤ K := hZR.trans hRK
  obtain ⟨d,p,hp,_hrep,hker,e,_hcoords,he⟩ :=
    AlternatingCentralModule.exists_marked_module Q eQ hself eA
  have hdis : Disjoint p.ker (R.map q) := by
    rw [hker,disjoint_iff,←map_inf_of_ker_le q Q R
      (by simpa only [q,QuotientGroup.ker_mk'] using hZR),hinf]
    exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
  have hgen : p.ker ⊔ R.map q = ⊤ := by
    rw [hker,←Subgroup.map_sup,hsup,map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hcomp : p.ker.IsComplement' (R.map q) := by
    apply isComplement'_of_disjoint_and_mul_eq_univ hdis
    rw [←normal_mul,hgen,coe_top]
  have he' (g : H ⧸ center H) (v : p.ker) :
      e (MulAut.conjNormal g v) =
        BinaryPermutation.AlternatingFiveExtension.TriangleTranslation.action (p g) (e v) := by
    apply Multiplicative.toAdd.injective
    exact he g v
  obtain ⟨E,_hq,_hv,_hr,hR⟩ := exists_marked_semidirect_equiv_of_given_complement
    p hp e BinaryPermutation.AlternatingFiveExtension.TriangleTranslation.action he' (R.map q) hcomp
  have hle : (SemidirectProduct.inr : alternatingGroup (Fin 5) →*
      BinaryPermutation.AlternatingFiveExtension.TriangleTranslation.Model).range ≤
        (K.map q).map E.toMonoidHom := by
    rw [←hR]
    exact map_mono (map_mono hRK)
  rcases BinaryPermutation.AlternatingFiveExtension.TriangleTranslation.overgroup_complement_eq_or_top
      ((K.map q).map E.toMonoidHom) hle with hh | hh
  · left
    apply map_injective_of_ker_le q
      (by simpa only [q,QuotientGroup.ker_mk'] using hZK)
      (by simpa only [q,QuotientGroup.ker_mk'] using hZR)
    apply map_injective (f := E.toMonoidHom) E.injective
    exact hh.trans hR.symm
  · right
    apply map_injective_of_ker_le q
      (by simpa only [q,QuotientGroup.ker_mk'] using hZK) le_top
    apply map_injective (f := E.toMonoidHom) E.injective
    rw [map_top_of_surjective q (QuotientGroup.mk'_surjective _),
      map_top_of_surjective E.toMonoidHom E.surjective]
    exact hh

end MinusExtraspecial
