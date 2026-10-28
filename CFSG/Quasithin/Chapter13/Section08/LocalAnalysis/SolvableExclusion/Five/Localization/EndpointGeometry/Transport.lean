module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.Data
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.NoTransvections
public import Theory.ElementaryAbelian.Quotient

/-!
# Conjugation of the actual endpoint quotient

The stored critical-pair conjugator identifies U_H/V₁ with Uγ/A₁ and H
with the endpoint vertex stabilizer. The transported action has the literal
conjugation formula. Transvections are preserved under this identification,
and also descend through surjective linear intertwiners. Consequently the
solvable 13.8.5(1) exclusion applies to this endpoint quotient.

These are algebraic transport results. They do not construct the reversed
critical path required by Remark F.9.17, nor claim the rank conclusion of
13.8.11. The source component implication remains an earlier input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.5(1),
13.8.10–11 and 13.8.13, printed pp.947, 950–951.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08
open CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five
open CriticalGeometry
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.EndpointGeometry
variable {G : Type*} [Group G]

theorem map_section_denominator (e : G ≃* G) (U Z : Subgroup G) :
    (Z.subgroupOf U).map (e.subgroupMap U).toMonoidHom =
      (Z.map (e : G →* G)).subgroupOf (U.map (e : G →* G)) := by
  ext x
  rw [mem_map_equiv]
  change e.symm (x : G) ∈ Z ↔ (x : G) ∈ Z.map (e : G →* G)
  exact mem_map_equiv.symm

theorem map_section_normal (e : G ≃* G) (U Z : Subgroup G)
    [(Z.subgroupOf U).Normal] :
    ((Z.map (e : G →* G)).subgroupOf (U.map (e : G →* G))).Normal := by
  rw [← map_section_denominator e U Z]
  exact Subgroup.Normal.map inferInstance (e.subgroupMap U).toMonoidHom
    (e.subgroupMap U).surjective

def sectionEquiv (e : G ≃* G) (U Z : Subgroup G)
    [(Z.subgroupOf U).Normal]
    [((Z.map (e : G →* G)).subgroupOf (U.map (e : G →* G))).Normal] :
    (U ⧸ Z.subgroupOf U) ≃*
      ((U.map (e : G →* G)) ⧸ (Z.map (e : G →* G)).subgroupOf (U.map (e : G →* G))) :=
  QuotientGroup.congr _ _ (e.subgroupMap U) (map_section_denominator e U Z)

theorem sectionEquiv_mk (e : G ≃* G) (U Z : Subgroup G)
    [(Z.subgroupOf U).Normal]
    [((Z.map (e : G →* G)).subgroupOf (U.map (e : G →* G))).Normal] (u : U) :
    sectionEquiv e U Z (QuotientGroup.mk' (Z.subgroupOf U) u) =
      QuotientGroup.mk' ((Z.map (e : G →* G)).subgroupOf (U.map (e : G →* G)))
        (e.subgroupMap U u) := rfl

def binaryEquiv {W W' : Type*} [Group W] [Group W']
    [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 W'] (e : W ≃* W') :
    Additive W ≃ₗ[ZMod 2] Additive W' :=
  { e.toAdditive with map_smul' := ZMod.map_smul e.toAdditive }

theorem transvection_transport {W W' : Type*} [Group W] [Group W']
    [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 W']
    (e : W ≃* W') (t : MulAut W)
    (ht : binaryLinear t ∈ LinearEquiv.transvections (ZMod 2) (Additive W)) :
    binaryLinear (MulAut.congr e t) ∈
      LinearEquiv.transvections (ZMod 2) (Additive W') := by
  obtain ⟨f, v, hfv, ht⟩ := ht
  let E := binaryEquiv e
  refine ⟨f.comp E.symm.toLinearMap, E v, by simpa using hfv, ?_⟩
  ext x
  change E (binaryLinear t (E.symm x)) = _
  rw [ht, LinearEquiv.transvection.apply, map_add, map_smul]
  simp only [LinearEquiv.apply_symm_apply, LinearEquiv.transvection.apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe]
  rfl

theorem transvection_transport_iff {W W' : Type*} [Group W] [Group W']
    [IsElementaryAbelian 2 W] [IsElementaryAbelian 2 W']
    (e : W ≃* W') (t : MulAut W) :
    binaryLinear (MulAut.congr e t) ∈
        LinearEquiv.transvections (ZMod 2) (Additive W') ↔
      binaryLinear t ∈ LinearEquiv.transvections (ZMod 2) (Additive W) := by
  refine ⟨fun ht => ?_, transvection_transport e t⟩
  have hh := transvection_transport e.symm (MulAut.congr e t) ht
  have he : MulAut.congr e.symm (MulAut.congr e t) = t := by
    ext x
    exact e.symm_apply_apply (t (e.symm (e x))) |>.trans (congrArg t (e.symm_apply_apply x))
  rwa [he] at hh

theorem transvection_of_surjective_intertwiner
    {K W W' : Type*} [Field K] [AddCommGroup W] [AddCommGroup W']
    [Module K W] [Module K W'] (q : W →ₗ[K] W') (hq : Function.Surjective q)
    (t : W ≃ₗ[K] W) (t' : W' ≃ₗ[K] W')
    (heq : ∀ w, q (t w) = t' (q w))
    (ht : t ∈ LinearEquiv.transvections K W) :
    t' ∈ LinearEquiv.transvections K W' := by
  obtain ⟨f, v, hfv, ht⟩ := ht
  obtain ⟨r, hr⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  have hqr (w : W') : q (r w) = w := LinearMap.congr_fun hr w
  have hformula (w : W') : t' w = w + f (r w) • q v := by
    rw [← hqr w, ← heq, ht, LinearEquiv.transvection.apply, map_add, map_smul, hqr]
  by_cases hv : q v = 0
  · have he : t' = 1 := by
      ext w
      change t' w = w
      rw [hformula, hv, smul_zero, add_zero]
    rw [he]
    exact LinearEquiv.one_mem_transvections
  · have hfixed : t' (q v) = q v := by
      rw [← heq, ht, LinearEquiv.transvection.apply, hfv, zero_smul, add_zero]
    have hpair : f (r (q v)) = 0 := by
      have hh := hformula (q v)
      rw [hfixed] at hh
      have hz : f (r (q v)) • q v = 0 := (add_eq_left.mp hh.symm)
      exact (smul_eq_zero.mp hz).resolve_right hv
    refine ⟨f.comp r, q v, hpair, ?_⟩
    ext w
    exact hformula w

section TransportedAction
variable {H U Z : Subgroup G} [(Z.subgroupOf U).Normal]
variable (a : StarAction H U Z) (e : G ≃* G)
variable [((Z.map (e : G →* G)).subgroupOf (U.map (e : G →* G))).Normal]

def transportedAction : H.map (e : G →* G) →*
    MulAut ((U.map (e : G →* G)) ⧸
      (Z.map (e : G →* G)).subgroupOf (U.map (e : G →* G))) :=
  (MulAut.congr (sectionEquiv e U Z)).toMonoidHom.comp
    (a.action.comp ((QuotientGroup.mk' (pCore 2 H)).comp
      (e.subgroupMap H).symm.toMonoidHom))

theorem transportedAction_on_section (h : H) (u : U ⧸ Z.subgroupOf U) :
    transportedAction a e (e.subgroupMap H h) (sectionEquiv e U Z u) =
      sectionEquiv e U Z (a.action (QuotientGroup.mk' (pCore 2 H) h) u) := by
  change sectionEquiv e U Z
    (a.action (QuotientGroup.mk' (pCore 2 H) ((e.subgroupMap H).symm
      (e.subgroupMap H h))) ((sectionEquiv e U Z).symm (sectionEquiv e U Z u))) = _
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

theorem transportedAction_conjugation (h : H) (u : U) :
    transportedAction a e (e.subgroupMap H h)
        (QuotientGroup.mk' ((Z.map (e : G →* G)).subgroupOf (U.map (e : G →* G)))
          (e.subgroupMap U u)) =
      QuotientGroup.mk' ((Z.map (e : G →* G)).subgroupOf (U.map (e : G →* G)))
        ⟨e (h : G) * e (u : G) * (e (h : G))⁻¹, by
          apply mem_map_equiv.mpr
          simp only [map_mul, map_inv, e.symm_apply_apply]
          exact (mem_normalizer_iff.mp (a.normalizes h.property) u).mp u.property⟩ := by
  rw [← sectionEquiv_mk, transportedAction_on_section, a.conjugation, sectionEquiv_mk]
  congr 1
  apply Subtype.ext
  exact (map_mul e _ _).trans (by rw [map_mul, map_inv])

theorem transportedAction_eq_one_of_transvection
    [IsElementaryAbelian 2 (U ⧸ Z.subgroupOf U)]
    [IsElementaryAbelian 2 ((U.map (e : G →* G)) ⧸
      (Z.map (e : G →* G)).subgroupOf (U.map (e : G →* G)))]
    (T : Subgroup G) (hs : Group.IsSolvable H)
    (h135 : TransvectionComponentConclusion a T) (h : H.map (e : G →* G))
    (ht : binaryLinear (transportedAction a e h) ∈
      LinearEquiv.transvections (ZMod 2) (Additive ((U.map (e : G →* G)) ⧸
        (Z.map (e : G →* G)).subgroupOf (U.map (e : G →* G))))) :
    transportedAction a e h = 1 := by
  have hh := (transvection_transport_iff (sectionEquiv e U Z) _).mp ht
  have hone := a.eq_one_of_transvection_of_solvable T hs h135
    (QuotientGroup.mk' (pCore 2 H) ((e.subgroupMap H).symm h)) hh
  change MulAut.congr (sectionEquiv e U Z)
    (a.action (QuotientGroup.mk' (pCore 2 H) ((e.subgroupMap H).symm h))) = 1
  rw [hone, map_one]
end TransportedAction

section CriticalEndpoint
variable {L T H V : Subgroup G} (c : CriticalPair L T H V)

/-- The actual conjugator identifies H with the endpoint vertex stabilizer. -/
def endpointGroupEquiv : H ≃* vertexGroup L T H c.gamma :=
  ((MulAut.conj (c.gb : G)).subgroupMap H).trans
    (MulEquiv.subgroupCongr c.vertexGroup_gamma.symm)

theorem endpoint_section_normal (V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal] :
    ((c.Aone V₁).subgroupOf (c.Ugamma V₃)).Normal :=
  map_section_normal (MulAut.conj (c.gb : G)) (Source.UH H V₃) V₁

variable (V₃ V₁ : Subgroup G)
variable [(V₁.subgroupOf (Source.UH H V₃)).Normal]
variable [((c.Aone V₁).subgroupOf (c.Ugamma V₃)).Normal]

/-- The literal U_H/V₁ is sent to Uγ/A₁ by the stored endpoint conjugator. -/
def endpointSectionEquiv : Source.Utilde H V₃ V₁ ≃*
    (c.Ugamma V₃ ⧸ (c.Aone V₁).subgroupOf (c.Ugamma V₃)) :=
  by
    let := map_section_normal (MulAut.conj (c.gb : G)) (Source.UH H V₃) V₁
    exact sectionEquiv (MulAut.conj (c.gb : G)) (Source.UH H V₃) V₁

theorem endpointSectionEquiv_mk (u : Source.UH H V₃) :
    endpointSectionEquiv c V₃ V₁ (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) =
      QuotientGroup.mk' ((c.Aone V₁).subgroupOf (c.Ugamma V₃))
        ((MulAut.conj (c.gb : G)).subgroupMap (Source.UH H V₃) u) := rfl

theorem endpoint_section_elementary [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)] :
    IsElementaryAbelian 2 (c.Ugamma V₃ ⧸ (c.Aone V₁).subgroupOf (c.Ugamma V₃)) :=
  IsElementaryAbelian.of_surjective (endpointSectionEquiv c V₃ V₁).toMonoidHom
    (endpointSectionEquiv c V₃ V₁).surjective

/-- The endpoint vertex group acts on its actual section by transported conjugation. -/
def endpointAction (a : StarAction H (Source.UH H V₃) V₁) :
    vertexGroup L T H c.gamma →*
      MulAut (c.Ugamma V₃ ⧸ (c.Aone V₁).subgroupOf (c.Ugamma V₃)) :=
  by
    let := map_section_normal (MulAut.conj (c.gb : G)) (Source.UH H V₃) V₁
    exact (transportedAction a (MulAut.conj (c.gb : G))).comp
      (MulEquiv.subgroupCongr c.vertexGroup_gamma).toMonoidHom

theorem endpointAction_on_section (a : StarAction H (Source.UH H V₃) V₁)
    (h : H) (u : Source.Utilde H V₃ V₁) :
    endpointAction c V₃ V₁ a (endpointGroupEquiv c h) (endpointSectionEquiv c V₃ V₁ u) =
      endpointSectionEquiv c V₃ V₁ (a.action (QuotientGroup.mk' (pCore 2 H) h) u) :=
  by
    let := map_section_normal (MulAut.conj (c.gb : G)) (Source.UH H V₃) V₁
    exact transportedAction_on_section a (MulAut.conj (c.gb : G)) h u

theorem endpointAction_eq_one_of_transvection
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    [IsElementaryAbelian 2 (c.Ugamma V₃ ⧸ (c.Aone V₁).subgroupOf (c.Ugamma V₃))]
    (a : StarAction H (Source.UH H V₃) V₁)
    (hs : Group.IsSolvable H) (h135 : TransvectionComponentConclusion a T)
    (h : vertexGroup L T H c.gamma)
    (ht : binaryLinear (endpointAction c V₃ V₁ a h) ∈
      LinearEquiv.transvections (ZMod 2)
        (Additive (c.Ugamma V₃ ⧸ (c.Aone V₁).subgroupOf (c.Ugamma V₃)))) :
    endpointAction c V₃ V₁ a h = 1 :=
  by
    let := map_section_normal (MulAut.conj (c.gb : G)) (Source.UH H V₃) V₁
    let : IsElementaryAbelian 2
        ((Source.UH H V₃).map (MulAut.conj (c.gb : G) : G →* G) ⧸
          (V₁.map (MulAut.conj (c.gb : G) : G →* G)).subgroupOf
            ((Source.UH H V₃).map (MulAut.conj (c.gb : G) : G →* G))) :=
      IsElementaryAbelian.of_surjective
      (sectionEquiv (MulAut.conj (c.gb : G)) (Source.UH H V₃) V₁).toMonoidHom
      (sectionEquiv (MulAut.conj (c.gb : G)) (Source.UH H V₃) V₁).surjective
    exact transportedAction_eq_one_of_transvection a (MulAut.conj (c.gb : G)) T hs h135
      ((MulEquiv.subgroupCongr c.vertexGroup_gamma) h) ht
end CriticalEndpoint

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.EndpointGeometry

end
