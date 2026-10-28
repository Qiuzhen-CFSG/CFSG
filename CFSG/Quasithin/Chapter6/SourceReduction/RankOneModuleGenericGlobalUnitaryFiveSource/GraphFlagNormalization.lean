module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.Descent.FlagNormalization
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.GraphFlag

/-!
# A graph conjugator preserving the original unitary-five flag

Descend the flag of a represented middle involution, normalize it over the
actual fixed field, and correct the unitary descent basis by that fixed
isometry. The result preserves the original line and plane while retaining
the literal conjugated-graph equation. Its fixed-group equivalence identifies
both original native endpoint intersections and the whole middle through
the same extension's base map.

Source: F.4.29(2), F.4.37(2), printed pp.289,293 of refs/quasithin.pdf.
Representability of the selected abstract outer actor and the geometry of
the full fixed Sylow remain source obligations. No such premises are
claimed to have been discharged by this conditional calculation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
open Theory.SpecificGroups.UnitaryFive
open Descent GraphFixed

/-- A represented middle involution has a graph conjugator preserving the
original vector-space line and plane, with no supplied flag-conjugacy premise. -/
theorem unitary_twist_flag_conjugator (U : Model 4) (E : FiveExtension U)
    (f : E.middle) (hf2 : f^2=1) (u : U.form.unitarySubgroup)
    (hf : f.val=unitaryConj U.form u*projectiveAut U.form U.matrix) :
    ∃ v : U.form.unitarySubgroup,
      f.val=unitaryConj U.form v*projectiveAut U.form U.matrix*(unitaryConj U.form v)⁻¹ ∧
      Preserves U.form v (line U.F) ∧ Preserves U.form v (plane U.F) := by
  have hσ : U.form.conj≠1 := by
    intro he
    obtain ⟨c,hc⟩ := U.exists_lineTraceOne
    have hfix : U.form.conj c=c := by rw [he]; rfl
    rw [hfix,CharTwo.add_self_eq_zero] at hc
    exact zero_ne_one hc
  obtain ⟨v,hgraph,hW₀,hW₁,_⟩ := unitary_twist_descended_flag U E f hf2 u hf
  let W₀ := (line U.F).comap (unitaryLinear U.form v).toLinearMap
  let W₁ := (plane U.F).comap (unitaryLinear U.form v).toLinearMap
  have hdim₀ : Module.finrank U.F W₀=1 := by rw [unitary_comap_finrank,finrank_line]
  have hdim₁ : Module.finrank U.F W₁=2 := by rw [unitary_comap_finrank,finrank_plane]
  have hiso : ∀ x∈W₁, ∀ y∈W₁, IsotropicGeometry.pairing U.form x y=0 := by
    apply unitary_comap_isotropic U.form U.matrix v (plane U.F)
    intro x hx y hy
    exact plane_isotropic U.F U.form.conj ⟨x,hx⟩ ⟨y,hy⟩
  obtain ⟨w,hwf,hw₀,hw₁⟩ := FlagNormalization.normalize_stable_flag U.form U.matrix hσ
    W₀ W₁ (Submodule.comap_mono (line_le_plane U.F)) hdim₀ hdim₁ hW₀ hW₁ hiso
  refine ⟨v*w⁻¹,?_,FlagNormalization.correction_preserves U.form v w (line U.F) hw₀,
    FlagNormalization.correction_preserves U.form v w (plane U.F) hw₁⟩
  exact hgraph.trans (FlagNormalization.conjugate_graph_fixed_correction U.form U.matrix v w hwf).symm

private theorem flag_conjugate_graph_endpoints (U : Model 4) (E : FiveExtension U)
    (f : E.middle) (b : Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U)
    (hf : f.val=b.val*projectiveAut U.form U.matrix*b.val⁻¹) :
      let j := inclusion (inf_le_left.trans E.left_le : E.middle ≤ E.carrier)
      ∃ e : (projectiveAut U.form U.matrix).fixedSubgroup ≃*
          (E.baseHom.range ⊓ centralizer ({j f} : Set E.carrier) : Subgroup E.carrier),
        (∀ x, (e x).val=E.baseHom (b.val x.val)) ∧
        (∀ x, (e x).val∈E.family false ↔ x.val∈U.leftParabolic) ∧
        (∀ x, (e x).val∈E.family true ↔ x.val∈U.rightParabolic) ∧
        (∀ x, (e x).val∈E.middle.subgroupOf E.carrier ↔ x.val∈U.overlap) := by
  let j := inclusion (inf_le_left.trans E.left_le : E.middle ≤ E.carrier)
  have hfj : (j f).val=b.val*projectiveAut U.form U.matrix*b.val⁻¹ :=
    (show (j f).val=f.val from rfl).trans hf
  let e := conjugateGraphInnerEquiv U E (j f) b.val hfj
  have hmap₀ : U.leftParabolic.map b.val.toMonoidHom=U.leftParabolic := b.property.1
  have hmap₁ : U.rightParabolic.map b.val.toMonoidHom=U.rightParabolic := b.property.2
  have hb₀ (x : U.Carrier) : b.val x∈U.leftParabolic ↔ x∈U.leftParabolic := by
    have he : b.val x∈U.leftParabolic.map b.val.toMonoidHom ↔ x∈U.leftParabolic :=
      mem_map_iff_mem b.val.injective
    simpa only [hmap₀] using he
  have hb₁ (x : U.Carrier) : b.val x∈U.rightParabolic ↔ x∈U.rightParabolic := by
    have he : b.val x∈U.rightParabolic.map b.val.toMonoidHom ↔ x∈U.rightParabolic :=
      mem_map_iff_mem b.val.injective
    simpa only [hmap₁] using he
  have hl (x : (projectiveAut U.form U.matrix).fixedSubgroup) :
      (e x).val∈E.family false ↔ x.val∈U.leftParabolic := by
    dsimp only [e]
    rw [conjugateGraphInnerEquiv_apply,E.baseHom_mem_family_iff (five_conj_injective U)]
    exact hb₀ x.val
  have hr (x : (projectiveAut U.form U.matrix).fixedSubgroup) :
      (e x).val∈E.family true ↔ x.val∈U.rightParabolic := by
    dsimp only [e]
    rw [conjugateGraphInnerEquiv_apply,E.baseHom_mem_family_iff (five_conj_injective U)]
    exact hb₁ x.val
  exact ⟨e,conjugateGraphInnerEquiv_apply U E (j f) b.val hfj,
    hl,hr,fun x => and_congr (hl x) (hr x)⟩

-- The endpoint transport is checked separately above; this dependent assembly
-- still crosses the default elaboration budget when unpacking its unitary witness.
set_option maxHeartbeats 400000 in
/-- The constructed graph conjugator identifies both original native endpoint
intersections and the whole middle inside the same extension and base map. -/
theorem unitary_twist_fixed_native_flag (U : Model 4) (E : FiveExtension U)
    (f : E.middle) (hf2 : f^2=1) (u : U.form.unitarySubgroup)
    (hf : f.val=unitaryConj U.form u*projectiveAut U.form U.matrix) :
    ∃ b : Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U,
      let j := inclusion (inf_le_left.trans E.left_le : E.middle ≤ E.carrier)
      f.val=b.val*projectiveAut U.form U.matrix*b.val⁻¹ ∧
      ∃ e : (projectiveAut U.form U.matrix).fixedSubgroup ≃*
          (E.baseHom.range ⊓ centralizer ({j f} : Set E.carrier) : Subgroup E.carrier),
        (∀ x, (e x).val=E.baseHom (b.val x.val)) ∧
        (∀ x, (e x).val∈E.family false ↔ x.val∈U.leftParabolic) ∧
        (∀ x, (e x).val∈E.family true ↔ x.val∈U.rightParabolic) ∧
        (∀ x, (e x).val∈E.middle.subgroupOf E.carrier ↔ x.val∈U.overlap) := by
  obtain ⟨v,hv,hv₀,hv₁⟩ := unitary_twist_flag_conjugator U E f hf2 u hf
  let b : Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U :=
    ⟨unitaryConj U.form v,unitaryConj_parabolic_of_preserves U.form v (line U.F) hv₀,
      unitaryConj_parabolic_of_preserves U.form v (plane U.F) hv₁⟩
  have hb : f.val=b.val*projectiveAut U.form U.matrix*b.val⁻¹ := hv
  exact ⟨b,hb,flag_conjugate_graph_endpoints U E f b hb⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
