module

public import CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry.ModelReduction
public import Theory.Representation.G2BinaryIsotropicThree.OffenderSpaces


/-!
# The actual unitary conjugate intersection is its commutator

Compare the two centralizer coranks to choose an offender direction. The
proved G₂ offender classification gives a single involution whose displacement
range fills the fixed three-space. Lifting that involution through the original
induced automizer identifies the actual fixed subgroup with [V,U]. Under the
source containment [V,U]≤V∩U, this is also V∩U, of order eight.

For U=Vᵍ the second natural action is transported through the literal ambient
conjugation. Thus the final theorem has no offender, image-classification,
orientation, or intersection conclusion among its assumptions.

Source: Aschbacher–Smith 13.3.12(4), printed p.890, the first application of
B.4.6(13). Aligning the original point and three-space remains the next step.
-/

public section

open Subgroup Module Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Atlas.G2.Natural.BinaryIsotropicThree
variable {G : Type*} [Group G] {V U : Subgroup G}
  [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 U]

theorem commutator_eq_fixed_of_offender
    (E : Additive V≃ₗ[ZMod 2] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hA : IsOffender rho ((inducedAutomizer V U).map f))
    (hc : ⁅V,U⁆≤V⊓U) : ⁅V,U⁆=V⊓centralizer (U:Set G) := by
  have hUN : U≤normalizer (V:Set G) := le_normalizer_iff_commutator_le_left.mpr (hc.trans inf_le_left)
  apply le_antisymm
  · exact le_inf (hc.trans inf_le_left)
      ((hc.trans inf_le_right).trans (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance))
  · intro v hv
    let w : Additive V := Additive.ofMul ⟨v,hv.1⟩
    have hw : E w∈fixedSpace rho ((inducedAutomizer V U).map f) := by
      rw [←fixedSpace_map_equivariant (automizerRepresentation V) rho f E he]
      exact ⟨w,(mem_fixedSpace_inducedAutomizer V U hUN w).mpr hv.2,rfl⟩
    obtain ⟨t,ht,hfix⟩ := offender_fixed_is_single_displacement _ hA
    rw [hfix] at hw
    obtain ⟨x,hx⟩ := hw
    obtain ⟨a,ha,rfl⟩ := ht
    obtain ⟨n,hn,hna⟩ := ha
    let y := E.symm x
    have hd : automizerRepresentation V a y-y=w := by
      apply E.injective
      rw [map_sub,he,E.apply_symm_apply]
      exact hx
    rw [←hna] at hd
    have hvcomm : ⁅n.val,y.toMul.val⁆=v := by
      have hv := congrArg (fun z : Additive V=>z.toMul.val) hd
      change (V.normalizerMonoidHom n y.toMul / y.toMul).val=v at hv
      rw [Subgroup.coe_div,Subgroup.normalizerMonoidHom_apply_apply_coe,div_eq_mul_inv] at hv
      simpa only [commutatorElement_def,mul_assoc] using hv
    rw [←hvcomm,Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hn y.toMul.property

theorem intersection_eq_commutator_of_offender
    (E : Additive V≃ₗ[ZMod 2] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hA : IsOffender rho ((inducedAutomizer V U).map f))
    (hc : ⁅V,U⁆≤V⊓U) : V⊓U=⁅V,U⁆ := by
  apply le_antisymm
  · rw [commutator_eq_fixed_of_offender E f he hA hc]
    exact inf_le_inf_left V (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)
  · exact hc
variable [Finite G]

theorem intersection_card_of_offender
    (E : Additive V≃ₗ[ZMod 2] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hA : IsOffender rho ((inducedAutomizer V U).map f))
    (hc : ⁅V,U⁆≤V⊓U) : Nat.card (V⊓U : Subgroup G)=8 := by
  have hUN : U≤normalizer (V:Set G) := le_normalizer_iff_commutator_le_left.mpr (hc.trans inf_le_left)
  have hnative : fixedCodim rho ((inducedAutomizer V U).map f)=3 := by
    have hh := Atlas.G2.NaturalOffenders.natural_offender_fixedCodim
      (F:=K) (n:=1) (by norm_num) (by decide) _
      ((Atlas.G2.NaturalOffenders.natural_offender_iff _).mpr hA)
    rw [Atlas.G2.NaturalOffenders.natural_fixedCodim_eq] at hh
    exact hh
  have hcost : subgroupCorank V (V⊓centralizer (U:Set G))=3 := by
    rw [←fixedCodim_inducedAutomizer V U hUN,
      fixedCodim_map_equivariant (automizerRepresentation V) rho f E he]
    exact hnative
  have hfix : V⊓U=V⊓centralizer (U:Set G) :=
    (intersection_eq_commutator_of_offender E f he hA hc).trans
      (commutator_eq_fixed_of_offender E f he hA hc)
  have hdim := ambientSpace_finrank_add_corank (V:=V) (V⊓U)
  have hvdim : finrank (ZMod 2) (Additive V)=6 := E.finrank_eq.trans (by simp [W])
  rw [hfix,hcost,hvdim] at hdim
  have hr : finrank (ZMod 2) (ambientSpace (V:=V) (V⊓U))=3 := by rw [hfix];omega
  have hh := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=ambientSpace (V:=V) (V⊓U))
  rw [hr,Nat.card_zmod] at hh
  have hcE : Nat.card (ambientSpace (V:=V) (V⊓U))=Nat.card (V⊓U : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show V⊓U≤V from inf_le_left)).toEquiv
  rw [←hcE,hh]
  decide

theorem image_offender_of_corank_comparison
    (E : Additive V≃ₗ[ZMod 2] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hc : ⁅V,U⁆≤V⊓U) (hne : ⁅V,U⁆≠⊥)
    (hcost : subgroupCorank V (V⊓centralizer (U:Set G))≤
      subgroupCorank U (U⊓centralizer (V:Set G))) :
    IsOffender rho ((inducedAutomizer V U).map f) := by
  have hUN : U≤normalizer (V:Set G) := le_normalizer_iff_commutator_le_left.mpr (hc.trans inf_le_left)
  have hf : Function.Injective f := by
    intro a b hab
    apply automizerRepresentation_injective V
    apply LinearMap.ext
    intro v
    apply E.injective
    rw [he,he,hab]
  apply IsOffender.map_equivariant (automizerRepresentation V) rho f hf E he
  refine ⟨⟨inducedAutomizer_ne_bot_of_commutator_ne_bot hUN hne,
    inducedAutomizer_elementary V U hUN⟩,?_⟩
  rw [fixedCodim_inducedAutomizer V U hUN,rank_inducedAutomizer V U hUN]
  exact hcost

theorem intersection_eq_fixed_of_corank_comparison
    (E : Additive V≃ₗ[ZMod 2] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hc : ⁅V,U⁆≤V⊓U) (hne : ⁅V,U⁆≠⊥)
    (hcost : subgroupCorank V (V⊓centralizer (U:Set G))≤
      subgroupCorank U (U⊓centralizer (V:Set G))) :
    V⊓U=⁅V,U⁆ ∧ ⁅V,U⁆=V⊓centralizer (U:Set G) := by
  have ho := image_offender_of_corank_comparison E f he hc hne hcost
  exact ⟨intersection_eq_commutator_of_offender E f he ho hc,
    commutator_eq_fixed_of_offender E f he ho hc⟩

theorem intersection_geometry_of_two_natural_actions
    (EV : Additive V≃ₗ[ZMod 2] W) (fV : Automizer V→*Atlas.G2.Model K)
    (heV : ∀a v,EV (automizerRepresentation V a v)=rho (fV a) (EV v))
    (EU : Additive U≃ₗ[ZMod 2] W) (fU : Automizer U→*Atlas.G2.Model K)
    (heU : ∀a v,EU (automizerRepresentation U a v)=rho (fU a) (EU v))
    (hc : ⁅V,U⁆≤V⊓U) (hne : ⁅V,U⁆≠⊥) :
    V⊓U=⁅V,U⁆ ∧ Nat.card (V⊓U : Subgroup G)=8 := by
  rcases le_total (subgroupCorank V (V⊓centralizer (U:Set G)))
    (subgroupCorank U (U⊓centralizer (V:Set G))) with hh|hh
  · have ho := image_offender_of_corank_comparison EV fV heV hc hne hh
    exact ⟨intersection_eq_commutator_of_offender EV fV heV ho hc,
      intersection_card_of_offender EV fV heV ho hc⟩
  · have hc' : ⁅U,V⁆≤U⊓V := by simpa only [Subgroup.commutator_comm,inf_comm] using hc
    have hn' : ⁅U,V⁆≠⊥ := by simpa only [Subgroup.commutator_comm] using hne
    have ho := image_offender_of_corank_comparison EU fU heU hc' hn' hh
    simpa only [Subgroup.commutator_comm,inf_comm] using
      And.intro (intersection_eq_commutator_of_offender EU fU heU ho hc')
        (intersection_card_of_offender EU fU heU ho hc')

omit [IsElementaryAbelian 2 U] in
theorem intersection_geometry_of_conjugate
    (E : Additive V≃ₗ[ZMod 2] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (g : G) (hc : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≠⊥) :
    V⊓V.map (MulAut.conj g).toMonoidHom=⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ∧
      Nat.card (V⊓V.map (MulAut.conj g).toMonoidHom : Subgroup G)=8 := by
  let U := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  let e := automizerMapEquiv V (MulAut.conj g)
  let eV := automizerModuleEquiv V (MulAut.conj g)
  let EU := eV.symm.trans E
  let fU := f.comp e.symm.toMonoidHom
  apply intersection_geometry_of_two_natural_actions E f he EU fU _ hc hne
  intro a v
  change E (eV.symm (automizerRepresentation U a v))=rho (f (e.symm a)) (E (eV.symm v))
  rw [←he]
  apply congrArg E
  apply eV.injective
  rw [eV.apply_symm_apply]
  have hh := automizerRepresentation_equivariant V (MulAut.conj g) (e.symm a) (eV.symm v)
  simpa only [eV,e,LinearEquiv.apply_symm_apply,MulEquiv.apply_symm_apply] using hh.symm
end CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
