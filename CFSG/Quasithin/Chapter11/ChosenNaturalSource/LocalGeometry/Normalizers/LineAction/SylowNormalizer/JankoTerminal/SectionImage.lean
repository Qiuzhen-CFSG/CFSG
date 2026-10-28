module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoTerminal.Displacement
public import Theory.SpecificGroups.Janko1.PerfectSubgroupCore
public import Theory.GroupTheory.Commutator.CentralSylowTransfer
public import Theory.GroupTheory.PCoreSurjective

/-!
# The actual rank-one image in the exceptional J₁ quotient

A perfect subgroup of J₁ has central two-core by the small-Sylow theorem.
Central Sylow transfer then kills this core, since the certified Sylow
subgroups are elementary abelian. Applied to the actual image of the flag
residual Y in K/O₂(K), this identifies the restricted kernel with O₂(Y).
The resulting equivalence preserves the original quotient map and proves
that C_{A ∩ L}(Y/O₂(Y)) fixes this same residual image pointwise.

This supplies the section-identification step in the terminal argument.
The J₁ configuration and the remaining field-four normality and exclusion
steps remain with qt-d-1222-natural-line-action.

Source: Aschbacher--Smith, 3.3.16, printed p.591.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative

private theorem perfect_janko_subgroup_core (B : Subgroup Janko1.Model)
    [Group.IsPerfect B] : pCore 2 B = ⊥ := by
  let P : Sylow 2 B := Classical.choice inferInstance
  obtain ⟨U,hU⟩ := (P.isPGroup'.map B.subtype).exists_le_sylow
  let : IsElementaryAbelian 2 U := Janko1.SylowTwo.elementary U
  have hc : ⁅(P : Subgroup B),(P : Subgroup B)⁆ = ⊥ := by
    apply le_bot_iff.mp
    rw [commutator_le]
    intro x hx y hy
    apply mem_bot.mpr
    apply Subtype.val_injective
    have hxy := congrArg (fun u : U => (u : Janko1.Model))
      (mul_comm (⟨x,hU (mem_map_of_mem B.subtype hx)⟩ : U)
        ⟨y,hU (mem_map_of_mem B.subtype hy)⟩)
    exact commutatorElement_eq_one_iff_mul_comm.mpr hxy
  apply bot_unique
  intro x hx
  have h := center_inf_commutator_inf_sylow_le_commutator P
    ⟨⟨Janko1.perfect_subgroup_pCore_two_le_center B hx,
      Group.IsPerfect.mem_commutator⟩,pCore_isPGroup.le_sylow_of_normal P hx⟩
  exact hc ▸ h

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c}
    {A : OddSupplement T} (E : JankoConfiguration S f A)
namespace JankoConfiguration
/-- The original inclusion followed by the actual component quotient. -/
def residualProjection : f.Li E.index →* (E.component ⧸ pCore 2 E.component) :=
  (QuotientGroup.mk' (pCore 2 E.component)).comp (inclusion E.contains.le)

/-- The image of the original flag residual in the component quotient. -/
def residualImage : Subgroup (E.component ⧸ pCore 2 E.component) :=
  E.residualProjection.range

/-- The actual image has trivial two-core. -/
theorem residualImage_core_eq_bot : pCore 2 E.residualImage = ⊥ := by
  let : Group.IsPerfect (f.Li E.index) := localResidual_perfect _
  let : Group.IsPerfect E.residualImage := Group.IsPerfect.range E.residualProjection
  obtain ⟨e⟩ := E.model
  let B := E.residualImage.map e.toMonoidHom
  let d : E.residualImage ≃* B := e.subgroupMap E.residualImage
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := d.toMonoidHom) d.surjective
  have hb : pCore 2 B = ⊥ := perfect_janko_subgroup_core B
  apply ((pCore 2 E.residualImage).map_eq_bot_iff_of_injective (f := d.toMonoidHom) d.injective).mp
  rw [pCore_map_iso 2 d,hb]

/-- No larger or smaller denominator occurs in the restricted quotient map. -/
theorem residualProjection_kernel : E.residualProjection.ker = pCore 2 (f.Li E.index) := by
  have hk : IsPGroup 2 E.residualProjection.ker := by
    change IsPGroup 2 (((QuotientGroup.mk' (pCore 2 E.component)).comp
      (inclusion E.contains.le)).ker)
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective E.contains.le)
  have hr : IsPGroup 2 E.residualProjection.rangeRestrict.ker := by
    rwa [MonoidHom.ker_rangeRestrict]
  have h := E.residualProjection.rangeRestrict.comap_pCore_of_ker_isPGroup
    E.residualProjection.rangeRestrict_surjective hr
  rw [show pCore 2 E.residualProjection.range = ⊥ from E.residualImage_core_eq_bot] at h
  simpa only [MonoidHom.comap_bot, MonoidHom.ker_rangeRestrict] using h

/-- The intrinsic residual quotient is the actual image inside K/O₂(K). -/
def residualQuotientEquiv :
    (f.Li E.index ⧸ pCore 2 (f.Li E.index)) ≃* E.residualImage :=
  (QuotientGroup.quotientMulEquivOfEq E.residualProjection_kernel.symm).trans
    (QuotientGroup.quotientKerEquivRange E.residualProjection)

/-- The section equivalence agrees with projection on every representative. -/
theorem residualQuotientEquiv_mk (y : f.Li E.index) :
    E.residualQuotientEquiv (QuotientGroup.mk' (pCore 2 (f.Li E.index)) y) =
      E.residualProjection.rangeRestrict y := rfl

/-- The actual residual image is PSL₂(4), with the original quotient marking. -/
theorem residualImage_isPSL2Four : ClassicalGroup.IsPSL E.residualImage 2 4 := by
  obtain ⟨F,hF,hfin,hcard,⟨d⟩⟩ :=
    (invariantFlag_geometry D S f).2.2.model E.index
  refine ⟨F,hF,hfin,?_,⟨E.residualQuotientEquiv.symm.trans d⟩⟩
  norm_num only [E.degree_eq_two] at hcard
  exact hcard

/-- The literal two-core of Y is contained in the literal two-core of K. -/
theorem residual_core_le_component_core :
    (f.Li E.index).pCoreIn 2 ≤ E.component.pCoreIn 2 := by
  rintro _ ⟨y,hy,rfl⟩
  have hk : y ∈ E.residualProjection.ker := E.residualProjection_kernel.symm ▸ hy
  have hyK : inclusion E.contains.le y ∈ pCore 2 E.component :=
    (QuotientGroup.eq_one_iff _).mp hk
  exact mem_map_of_mem E.component.subtype hyK

/-- Centralizing Y/O₂(Y) fixes its same image in K/O₂(K). -/
theorem sectionCentralizer_fixes_residualImage {x : G}
    (hx : x ∈ E.sectionCentralizer) (hxK : x ∈ normalizer (E.component : Set G))
    (y : f.Li E.index) :
    coreQuotientAction E.component ⟨x,hxK⟩ (E.residualProjection y) =
      E.residualProjection y := by
  obtain ⟨a,ha,hax⟩ := hx
  have hfix := DFunLike.congr_fun (show coreQuotientAction (f.Li E.index) a = 1 from ha)
    (QuotientGroup.mk' (pCore 2 (f.Li E.index)) y)
  have heq : QuotientGroup.mk' (pCore 2 (f.Li E.index))
      ((f.Li E.index).normalizerMonoidHom a y) =
      QuotientGroup.mk' (pCore 2 (f.Li E.index)) y := by
    simpa only [coreQuotientAction,MonoidHom.comp_apply,quotientAut_apply_mk,MulAut.one_apply] using hfix
  have him := congrArg (fun z => (E.residualQuotientEquiv z).val) heq
  rw [E.residualQuotientEquiv_mk,E.residualQuotientEquiv_mk] at him
  change E.residualProjection ((f.Li E.index).normalizerMonoidHom a y) =
    E.residualProjection y at him
  rw [show E.residualProjection y = QuotientGroup.mk' (pCore 2 E.component)
    (inclusion E.contains.le y) from rfl,coreQuotientAction,MonoidHom.comp_apply,quotientAut_apply_mk]
  change _ = E.residualProjection y
  rw [← him]
  change QuotientGroup.mk' (pCore 2 E.component) _ =
    QuotientGroup.mk' (pCore 2 E.component) _
  congr 1
  apply Subtype.ext
  change x * (y : G) * x⁻¹ = (a : G) * (y : G) * (a : G)⁻¹
  change (a : G) = x at hax
  rw [hax]

/-- The odd section centralizer acts trivially on the actual residual image. -/
theorem oddSectionCentralizer_fixes_residualImage
    (x : E.oddSectionCentralizer) (y : E.residualImage) :
    coreQuotientAction E.component
      ⟨x, ((normal_subgroupOf_iff_le_normalizer E.normal_component.1.1).mp
        E.normal_component.2) (mem_sup_right x.property.1.1)⟩ y = y := by
  obtain ⟨z,hz⟩ := y.property
  simpa only [hz] using E.sectionCentralizer_fixes_residualImage x.property.2
    (((normal_subgroupOf_iff_le_normalizer E.normal_component.1.1).mp
      E.normal_component.2) (mem_sup_right x.property.1.1)) z

end JankoConfiguration
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
