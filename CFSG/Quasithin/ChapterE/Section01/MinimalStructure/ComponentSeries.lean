module

public import CFSG.Quasithin.ChapterE.Section01.MinimalSupplement
public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.Frattini
public import CFSG.Quasithin.ChapterE.Section01.MinimalStructure.Kernel
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.CComponent.LayerTransport
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The radical--layer--two series of a minimal supplement

In E.1.10(4), the normal image of `K ∩ X` is an `O_{∞,E}`-group. Its image
modulo the radical of `Kbar` therefore lies in the ordinary component layer.
The identity `K = (K ∩ X)T` makes the remaining quotient a two-group.
The solvable kernel of `K → Kbar` identifies the radical quotients and their
layers, giving `K = O_{∞,E,2}(K)`.

The source hypothesis `KbarX = O_{∞,E}(KbarX)` is expressed as the ordinary
layer being the whole radical quotient. Its equivalence is proved in
`Subgroup.oInfELayer_eq_top_iff`, using the C-component correspondence from
`CComponent.Structure`. The radical two-closedness and residual hypotheses
of E.1.10(4) are needed for its other conclusions, not for this conclusion.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma E.1.10(4), printed p.211.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

private theorem component_series_of_solvable_kernel
    (f : G →* H) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (N P : Subgroup H) (hN : N.IsSubnormal) (hE : oInfELayer N = ⊤)
    (hP : IsPGroup 2 P) (hsup : N ⊔ P = ⊤) :
    HasTwoGroupQuotient (componentLayer (G ⧸ solvableRadical G)) := by
  let q := QuotientGroup.mk' (solvableRadical H)
  let E := componentLayer (H ⧸ solvableRadical H)
  let : E.Normal := componentLayer_normal_of_solvableRadical_eq_bot
    solvableRadical_quotient_solvableRadical
  have hNE : N.map q ≤ E := map_le_componentLayer_of_oInfELayer_eq_top hN hE
  have hEP : E ⊔ P.map q = ⊤ := by
    apply top_unique
    have hs := congrArg (Subgroup.map q) hsup
    rw [Subgroup.map_sup, map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at hs
    rw [← hs]
    exact sup_le_sup_right hNE _
  have hp := isPGroup_quotient_of_sup_eq_top E (P.map q) (hP.map q) hEP
  let e := solvableRadicalQuotientEquiv f hf
  let : (componentLayer (G ⧸ solvableRadical G)).Normal :=
    componentLayer_normal_of_solvableRadical_eq_bot solvableRadical_quotient_solvableRadical
  have he : (componentLayer (G ⧸ solvableRadical G)).map e.toMonoidHom = E :=
    map_componentLayer_equiv_of_solvableRadical_eq_bot
      solvableRadical_quotient_solvableRadical solvableRadical_quotient_solvableRadical e
  exact ⟨inferInstance, hp.of_equiv (QuotientGroup.congr _ E e he).symm⟩

/-- The first conclusion of E.1.10(4), using only the layer hypothesis.
Normality is intrinsic to the supplement and its image; `K` need not be
normal in `G`. The result is the source equality `K = O_{∞,E,2}(K)`. -/
theorem IsMinimalSupplement.hasTwoGroupQuotient_componentLayer (T : Sylow 2 G)
    {X Y K : Subgroup G} [X.Normal] [Y.Normal]
    (h : IsMinimalSupplement (T : Subgroup G) X Y K)
    (hE : componentLayer
      (((K ⊓ X).map (QuotientGroup.mk' Y)) ⧸
        solvableRadical ((K ⊓ X).map (QuotientGroup.mk' Y))) = ⊤) :
    HasTwoGroupQuotient (componentLayer (K ⧸ solvableRadical K)) := by
  let f := (QuotientGroup.mk' Y).subgroupMap K
  have hf := (QuotientGroup.mk' Y).subgroupMap_surjective K
  let N := (X.subgroupOf K).map f
  let S : Sylow 2 K := T.subtype h.1.1
  let P := (S : Subgroup K).map f
  have hk : f.ker = Y.subgroupOf K := by
    ext k
    change (f k = 1) ↔ (k : G) ∈ Y
    rw [Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff (k : G)
  let : Group.IsSolvable f.ker := hk.symm ▸ h.isSolvable_kernel T
  have hn : N.Normal := Normal.map inferInstance f hf
  have hNmap : N.map (K.map (QuotientGroup.mk' Y)).subtype =
      (K ⊓ X).map (QuotientGroup.mk' Y) := by
    rw [show N = (X.subgroupOf K).map f from rfl, map_map]
    change (X.subgroupOf K).map ((QuotientGroup.mk' Y).comp K.subtype) = _
    rw [← map_map, subgroupOf_map_subtype, inf_comm]
  let e := (N.equivMapOfInjective (K.map (QuotientGroup.mk' Y)).subtype
      (K.map (QuotientGroup.mk' Y)).subtype_injective).trans (MulEquiv.subgroupCongr hNmap)
  have hNE : oInfELayer N = ⊤ := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_oInfELayer_equiv, oInfELayer_eq_top_iff.mpr hE,
      map_top_of_surjective _ e.surjective]
  have hs : X.subgroupOf K ⊔ (S : Subgroup K) = ⊤ := by
    apply map_injective K.subtype_injective
    rw [Subgroup.map_sup, subgroupOf_map_subtype]
    change X ⊓ K ⊔ ((T : Subgroup G).subgroupOf K).map K.subtype = (⊤ : Subgroup K).map K.subtype
    rw [map_subgroupOf_eq_of_le h.1.1, ← MonoidHom.range_eq_map, range_subtype, inf_comm]
    exact h.eq_inf_sup.symm
  have hNP : N ⊔ P = ⊤ := by
    have hm := congrArg (Subgroup.map f) hs
    simpa only [Subgroup.map_sup, map_top_of_surjective f hf] using hm
  exact component_series_of_solvable_kernel f hf N P hn.isSubnormal hNE
    (S.isPGroup'.map f) hNP

end CFSG.Quasithin.ChapterE
