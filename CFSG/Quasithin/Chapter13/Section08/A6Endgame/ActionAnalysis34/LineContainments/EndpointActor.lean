module

public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.ActionAnalysis34.LineContainments.Sections

/-!
# A common nonidentity actor on the endpoint sections

Choose an element of the actual `U_H` whose action on `Vγ/Uγ` is nonidentity,
using the order-two common center. The common axis makes its conjugation on
`Uγ` a transvection; the canonical quotient map descends this formula to
`Uγ/A₁`. Compatibility on representatives identifies both actions with those
of the same image in `J/O₂(J)`. Elementary abelianness of `U_H` gives its
square-one equation, and the nonidentity action proves that image is nonidentity.

The center and axis are explicit geometric inputs, supplied by the oriented
geometry in the line-containment owner. This helper needs no model identification
or faithfulness premise and does not assert the line containments themselves.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 13.8.34(1), printed p.968 (PDF p.985), using 13.8.9–10, pp.949–950.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.A6Endgame.LineContainments
open CriticalGeometry CriticalGeometry.SectionActions
variable {G : Type*} [Group G] [Finite G] {L T H V : Subgroup G}

/-- The center and axis actions yield one nonidentity involution in the
actual endpoint star group with displacement at most one on both literal
sections. Its nonidentity action on `Vγ/Uγ` is retained explicitly. -/
theorem exists_common_endpoint_actor
    (c : CriticalPair L T H V) (V₃ Z : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (c.Ugamma V₃)] [IsElementaryAbelian 2 c.Vgamma]
    (hz : H ≤ normalizer (Z : Set G))
    (hUJ : Source.UH H V₃ ≤ vertexGroup L T H c.gamma)
    (E : EndpointActions c V₃ Z hz)
    (hcenter : HasTransvectionCenter (Source.UH H V₃) c.Vgamma (c.Ugamma V₃) Z
      (hUJ.trans (c.normalizes_Ugamma V)) (hUJ.trans (c.normalizes_Ugamma V₃)))
    (haxis : HasTransvectionAxis (Source.UH H V₃) (c.Ugamma V₃)
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) Z)
      (hUJ.trans (c.normalizes_Ugamma V₃))) :
    ∃ t : Source.Hstar (vertexGroup L T H c.gamma), t ≠ 1 ∧ t ^ 2 = 1 ∧
      Module.finrank (ZMod 2) (LinearMap.range (E.onU t - LinearMap.id)) ≤ 1 ∧
      Module.finrank (ZMod 2) (LinearMap.range (E.onV t - LinearMap.id)) ≤ 1 ∧
      E.onV t ≠ LinearMap.id := by
  let P := Source.UH H V₃
  let U := c.Ugamma V₃
  let A := c.Aone Z
  let J := vertexGroup L T H c.gamma
  let hn := hUJ.trans (c.normalizes_Ugamma V₃)
  let hv := hUJ.trans (c.normalizes_Ugamma V)
  let ha := hUJ.trans (SectionActions.CriticalPair.normalizes_Aone c Z hz)
  obtain ⟨p, hp, hpV⟩ := exists_nonidentity_of_center P c.Vgamma U Z hv hn hcenter
  let a := quotientAction P U A hn ha p
  let b := quotientAction P c.Vgamma U hv hn p
  let q := QuotientGroup.mk' (A.subgroupOf U)
  have hi (w : Additive U) :
      binaryMap q (binaryLinear (conjugationAction P U hn p) w) =
        binaryLinear a (binaryMap q w) := by
    change q (conjugationAction P U hn p w.toMul) = a (q w.toMul)
    rw [quotientAction_apply]
    rfl
  have hpU := transvection_of_surjective_intertwiner (binaryMap q)
    (QuotientGroup.mk'_surjective (A.subgroupOf U))
    (binaryLinear (conjugationAction P U hn p)) (binaryLinear a) hi (haxis.2.2 p)
  let j : J := inclusion hUJ p
  let t : Source.Hstar J := QuotientGroup.mk' (pCore 2 J) j
  have heU : E.onU t = (binaryLinear a).toLinearMap := by
    rw [E.onU_mk]
    have he : quotientAction J U A (c.normalizes_Ugamma V₃)
        (SectionActions.CriticalPair.normalizes_Aone c Z hz) j = a := by
      ext w
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf U) w
      rw [quotientAction_apply, quotientAction_apply]
      rfl
    rw [he]
  have heV : E.onV t = (binaryLinear b).toLinearMap := by
    rw [E.onV_mk]
    have he : quotientAction J c.Vgamma U (c.normalizes_Ugamma V)
        (c.normalizes_Ugamma V₃) j = b := by
      ext w
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf c.Vgamma) w
      exact (quotientAction_apply J c.Vgamma U (c.normalizes_Ugamma V)
        (c.normalizes_Ugamma V₃) j u).trans
        (quotientAction_apply P c.Vgamma U hv hn p u).symm
    rw [he]
  have hmoved : E.onV t ≠ LinearMap.id := by
    intro he
    apply hp
    apply MulEquiv.ext
    intro w
    exact LinearMap.congr_fun (heV.symm.trans he) (Additive.ofMul w)
  have htwo : t ^ 2 = 1 := by
    have hp2 : p ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 P) p
    change ((QuotientGroup.mk' (pCore 2 J)).comp (inclusion hUJ) p) ^ 2 = 1
    rw [← map_pow, hp2, map_one]
  refine ⟨t, ?_, htwo, ?_, ?_, hmoved⟩
  · intro ht
    apply hmoved
    rw [ht, map_one]
    rfl
  · rw [heU]
    exact LinearEquiv.mem_dilatransvections_iff_finrank.mp
      (LinearEquiv.transvections_subset_dilatransvections hpU)
  · rw [heV]
    exact LinearEquiv.mem_dilatransvections_iff_finrank.mp
      (LinearEquiv.transvections_subset_dilatransvections hpV)

end CFSG.Quasithin.Chapter13.Section08.A6Endgame.LineContainments
