module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.Descent.Flags
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.Descent.FixedFlag
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryFiveSource.GraphDescent
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.CartanTransport

/-!
# The descended isotropic flag of a represented unitary-five middle involution

The literal middle actor preserves the projective endpoints. Removing its
known graph factor and correcting the determinant of its unitary factor
reduces preservation of the vector-space flag to the proved inner-flag
theorem. The unitary cocycle descent basis pulls that flag back to a
coefficient-stable flag. Descent gives a totally isotropic line and plane
over the stored four-element fixed field, whose scalar extensions are
exactly the pulled-back subspaces.

The original base map carries their parabolic intersections with the
standard graph-fixed group onto the two endpoints of the same inner
centralizer, and retains the whole middle. Source: F.4.29(2), F.4.37(2),
printed pp.289,293 of refs/quasithin.pdf. The selected abstract actor's
unitary-twist representation, fixed-group flag transitivity and full
fixed-Sylow root geometry remain obligations; no representation or ambient
Sylow conclusion is asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.UnitaryFive ChapterF.SourceCompletion.UnitaryNonbinary
open Theory.SpecificGroups.UnitaryFive
open Descent GraphFixed

theorem unitary_preserves_native_flag (U : Model 4) (u : U.form.unitarySubgroup)
    (hu : unitaryConj U.form u ∈ Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U) :
    Preserves U.form u (line U.F) ∧ Preserves U.form u (plane U.F) := by
  let d := flagDetCorrection U.form U.matrix u
  let g := flagSpecialCorrection U.form U.matrix u
  have hd : unitaryConj U.form d ∈ Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U :=
    ⟨unitaryConj_parabolic_of_preserves U.form d (line U.F)
      (flagDetCorrection_line U.form U.matrix u),
     unitaryConj_parabolic_of_preserves U.form d (plane U.F)
      (flagDetCorrection_plane U.form U.matrix u)⟩
  have hg : MulAut.conj (project U.form g) ∈ Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U := by
    have hh := (Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).mul_mem hu hd
    rw [←unitaryConj_mul] at hh
    have he : u*d=⟨g.val,g.property.1⟩ := rfl
    rwa [he,unitaryConj_special] at hh
  have hgf := UnitaryFullNormalizer.five_inner_flag U (project U.form g) hg
  exact ⟨preserves_of_specialCorrection U.form U.matrix u (line U.F)
      (flagDetCorrection_line U.form U.matrix u)
      ((project_mem_parabolic U.form (line U.F) g).mp hgf.1),
    preserves_of_specialCorrection U.form U.matrix u (plane U.F)
      (flagDetCorrection_plane U.form U.matrix u)
      ((project_mem_parabolic U.form (plane U.F) g).mp hgf.2)⟩

private theorem map_eq_of_preserves {B : Type*} [Group B] (P : Subgroup B)
    (a : MulAut B) (ha : ∀ x, a x∈P ↔ x∈P) : P.map a.toMonoidHom=P := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    exact (ha x).mpr hx
  · intro x hx
    obtain ⟨y,rfl⟩ := a.surjective x
    exact ⟨y,(ha y).mp hx,rfl⟩

theorem middle_unitary_twist_preserves_flag (U : Model 4) (E : FiveExtension U)
    (f : E.middle) (u : U.form.unitarySubgroup)
    (hf : f.val=unitaryConj U.form u*projectiveAut U.form U.matrix) :
    Preserves U.form u (line U.F) ∧ Preserves U.form u (plane U.F) := by
  have ha : f.val∈Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U :=
    ⟨map_eq_of_preserves U.leftParabolic f.val
        (E.middle_preserves_left (five_conj_injective U) f),
      map_eq_of_preserves U.rightParabolic f.val
        (E.middle_preserves_right (five_conj_injective U) f)⟩
  have hs : projectiveAut U.form U.matrix∈Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U :=
    graph_flag U.form U.matrix
  apply unitary_preserves_native_flag U u
  rw [hf] at ha
  simpa only [mul_inv_cancel_right] using
    (Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).mul_mem ha
      ((Chapter5.UnitaryNativeLift.Five.flagAutomorphisms U).inv_mem hs)

/-- A represented middle involution has an actual isotropic fixed-field flag.
Its endpoint centralizers use the original extension and literal base map. -/
theorem unitary_twist_descended_flag (U : Model 4) (E : FiveExtension U)
    (f : E.middle) (hf2 : f^2=1) (u : U.form.unitarySubgroup)
    (hf : f.val=unitaryConj U.form u*projectiveAut U.form U.matrix) :
    ∃ v : U.form.unitarySubgroup,
      let b := unitaryConj U.form v
      let W₀ := (line U.F).comap (unitaryLinear U.form v).toLinearMap
      let W₁ := (plane U.F).comap (unitaryLinear U.form v).toLinearMap
      let V₀ := FixedFlag.coordinates U.form W₀
      let V₁ := FixedFlag.coordinates U.form W₁
      f.val=b*projectiveAut U.form U.matrix*b⁻¹ ∧
      (∀ x, U.form.conj ∘ x ∈ W₀ ↔ x ∈ W₀) ∧
      (∀ x, U.form.conj ∘ x ∈ W₁ ↔ x ∈ W₁) ∧
      FixedFlag.scalarSpan U.form V₀=W₀ ∧
      FixedFlag.scalarSpan U.form V₁=W₁ ∧
      V₀ ≤ V₁ ∧
      Module.finrank (FixedBy.subfield U.F U.form.conj) V₀=1 ∧
      Module.finrank (FixedBy.subfield U.F U.form.conj) V₁=2 ∧
      (∀ x y : V₁, dotProduct x.val y.val=0) := by
  have hσ : U.form.conj≠1 := by
    intro he
    obtain ⟨c,hc⟩ := U.exists_lineTraceOne
    have hfix : U.form.conj c=c := by rw [he]; rfl
    rw [hfix,CharTwo.add_self_eq_zero] at hc
    exact zero_ne_one hc
  have hu2 : (unitaryConj U.form u*projectiveAut U.form U.matrix)^2=1 := by
    rw [←hf]
    exact congrArg Subtype.val hf2
  obtain ⟨v,hv⟩ := unitary_cocycle_coboundary U.form U.matrix hσ u
    (unitary_cocycle_of_twist_sq U.form U.matrix U.conjugation U.local_field_card u hu2)
  have hflag := middle_unitary_twist_preserves_flag U E f u hf
  let W₀ := (line U.F).comap (unitaryLinear U.form v).toLinearMap
  let W₁ := (plane U.F).comap (unitaryLinear U.form v).toLinearMap
  have h₀ := coboundary_comap_conj U.form u v hv (line U.F) hflag.1 (conj_line U.form)
  have h₁ := coboundary_comap_conj U.form u v hv (plane U.F) hflag.2 (conj_plane U.form)
  have hgraph : f.val=unitaryConj U.form v*projectiveAut U.form U.matrix*(unitaryConj U.form v)⁻¹ :=
    hf.trans (conjugate_graph_of_coboundary U.form U.matrix u v hv)
  refine ⟨v,hgraph,h₀,h₁,FixedFlag.scalarSpan_coordinates U.form hσ W₀ h₀,
    FixedFlag.scalarSpan_coordinates U.form hσ W₁ h₁,FixedFlag.coordinates_mono U.form
    (Submodule.comap_mono (line_le_plane U.F)),?_,?_,?_⟩
  · rw [FixedFlag.finrank_coordinates U.form hσ W₀ h₀,unitary_comap_finrank,finrank_line]
  · rw [FixedFlag.finrank_coordinates U.form hσ W₁ h₁,unitary_comap_finrank,finrank_plane]
  · apply FixedFlag.dot_zero
    apply unitary_comap_isotropic U.form U.matrix v (plane U.F)
    intro x hx y hy
    exact plane_isotropic U.F U.form.conj ⟨x,hx⟩ ⟨y,hy⟩

/-- The same fixed-group equivalence retains both endpoints and the whole middle. -/
theorem unitary_conjugate_graph_endpoints (U : Model 4) (E : FiveExtension U)
    (f : E.middle) (v : U.form.unitarySubgroup)
    (hgraph : f.val=unitaryConj U.form v*projectiveAut U.form U.matrix*(unitaryConj U.form v)⁻¹) :
    let b := unitaryConj U.form v
    let W₀ := (line U.F).comap (unitaryLinear U.form v).toLinearMap
    let W₁ := (plane U.F).comap (unitaryLinear U.form v).toLinearMap
    let j := inclusion (inf_le_left.trans E.left_le : E.middle ≤ E.carrier)
      ∃ e : (projectiveAut U.form U.matrix).fixedSubgroup ≃*
          (E.baseHom.range ⊓ centralizer ({j f} : Set E.carrier) : Subgroup E.carrier),
        (∀ x, (e x).val=E.baseHom (b x.val)) ∧
        (∀ x, (e x).val∈E.family false ↔ x.val∈parabolic U.form W₀) ∧
        (∀ x, (e x).val∈E.family true ↔ x.val∈parabolic U.form W₁) ∧
        (∀ x, (e x).val∈E.middle.subgroupOf E.carrier ↔
          x.val∈parabolic U.form W₀ ⊓ parabolic U.form W₁) := by
  let W₀ := (line U.F).comap (unitaryLinear U.form v).toLinearMap
  let W₁ := (plane U.F).comap (unitaryLinear U.form v).toLinearMap
  let j := inclusion (inf_le_left.trans E.left_le : E.middle ≤ E.carrier)
  let e := conjugateGraphInnerEquiv U E (j f) (unitaryConj U.form v) hgraph
  have hleft (x : (projectiveAut U.form U.matrix).fixedSubgroup) :
      (e x).val∈E.family false ↔ x.val∈parabolic U.form W₀ := by
    dsimp only [e]
    rw [conjugateGraphInnerEquiv_mem_endpoint U E (j f) (unitaryConj U.form v) hgraph x false]
    change x.val∈(parabolic U.form (line U.F)).comap (unitaryConj U.form v).toMonoidHom ↔ _
    rw [unitaryConj_parabolic_comap]
  have hright (x : (projectiveAut U.form U.matrix).fixedSubgroup) :
      (e x).val∈E.family true ↔ x.val∈parabolic U.form W₁ := by
    dsimp only [e]
    rw [conjugateGraphInnerEquiv_mem_endpoint U E (j f) (unitaryConj U.form v) hgraph x true]
    change x.val∈(parabolic U.form (plane U.F)).comap (unitaryConj U.form v).toMonoidHom ↔ _
    rw [unitaryConj_parabolic_comap]
  refine ⟨e,conjugateGraphInnerEquiv_apply U E (j f) (unitaryConj U.form v) hgraph,
    hleft,hright,?_⟩
  intro x
  exact and_congr (hleft x) (hright x)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
