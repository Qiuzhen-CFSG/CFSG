module

public import CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry.StandardConjugator
public import Theory.Representation.G2BinaryIsotropicThree.OffenderOrbits
public import CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry.ThreeSpaces
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Transport.Foundations
import all CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry.ThreeSpaces

/-!
# Original unitary intersecting-pair escape

An offender fixed three-space lies in the actual derived-group orbit of the
standard three-space. Lift its conjugator through the original induced
automizer. Apply this twice, to the pair and to its inverse conjugate, to
replace the ambient conjugator while preserving the first module and making
it normalize the standard intersection. The paired hyperplane calculation
then fixes the distinguished point and produces the required escaping
three-space centralizer.

The source endpoints retain the original E.6.1 hypotheses and natural normal
layer. They assume neither an offender nor a position for the intersection.
The final contrapositive is the literal consumer for the 13.3.15 centralizer
bound. The internal ThreeSpaces import only proves public behavior identities
for its existing standardThree definition; its private body stays private.

Source: Aschbacher–Smith 13.3.12(4), printed pp.889–890.
-/

public section

open Subgroup Module Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Atlas.G2.Natural.BinaryIsotropicThree
variable {G : Type*} [Group G] [Finite G] {V U L : Subgroup G}
 [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 U]

omit [Finite G] [IsElementaryAbelian 2 U] in
theorem standardThree_le (E : Additive V≃ₗ[K] W) : standardThree E≤V :=
  ambientGroup_le_module _

omit [Finite G] [IsElementaryAbelian 2 U] in
theorem standardThree_space (E : Additive V≃ₗ[K] W) :
    (ambientSpace (V:=V) (standardThree E)).map E.toLinearMap=target false := by
  change (ambientSpace (ambientGroup ((target false).comap E.toLinearMap))).map E.toLinearMap=_
  rw [ambientSpace_ambientGroup,Submodule.map_comap_eq_of_surjective E.surjective]

omit [Finite G] in
theorem exists_local_standard_intersection
    (E : Additive V≃ₗ[K] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hderived : commutator (Atlas.G2.Model K)≤(inducedAutomizer V L).map f)
    (hA : IsOffender rho ((inducedAutomizer V U).map f))
    (hc : ⁅V,U⁆≤V⊓U) :
    ∃n∈L,n∈normalizer (V:Set G) ∧
      (standardThree E).map (MulAut.conj n).toMonoidHom=V⊓U := by
  have hUN : U≤normalizer (V:Set G) := le_normalizer_iff_commutator_le_left.mpr (hc.trans inf_le_left)
  have hfixR : V⊓U=V⊓centralizer (U:Set G) :=
    (intersection_eq_commutator_of_offender E f he hA hc).trans
      (commutator_eq_fixed_of_offender E f he hA hc)
  have hfixed : (ambientSpace (V:=V) (V⊓U)).map E.toLinearMap=
      fixedSpace rho ((inducedAutomizer V U).map f) := by
    rw [←fixedSpace_map_equivariant (automizerRepresentation V) rho f E he]
    congr 1
    rw [hfixR]
    ext v
    change v.toMul.val∈V⊓centralizer (U:Set G) ↔ _
    rw [mem_fixedSpace_inducedAutomizer V U hUN]
    exact and_iff_right v.toMul.property
  obtain ⟨d,hd⟩ := offender_fixed_space_derived_orbit _ hA
  obtain ⟨a,ha,hfa⟩ := hderived d.property
  obtain ⟨n,hn,hna⟩ := ha
  have hn' : V.normalizerMonoidHom.rangeRestrict n=a := hna
  have hSV := standardThree_le E
  have hmapV : (standardThree E).map (MulAut.conj n.val).toMonoidHom≤V :=
    (Subgroup.map_mono hSV).trans_eq (Subgroup.mem_normalizer_iff_map_conj_eq.mp n.property)
  refine ⟨n.val,hn,n.property,?_⟩
  have hchart : (ambientSpace (V:=V) ((standardThree E).map (MulAut.conj n.val).toMonoidHom)).map E.toLinearMap=
      (ambientSpace (V:=V) (V⊓U)).map E.toLinearMap := by
    rw [ambientSpace_conjugate hSV n,hn',←Submodule.map_comp]
    have hlin : E.toLinearMap.comp (automizerRepresentation V a)=(rho (f a)).comp E.toLinearMap :=
      LinearMap.ext (he a)
    rw [hlin,Submodule.map_comp,standardThree_space,hfa,←hd,hfixed]
  have hspaces := Submodule.map_injective_of_injective E.injective hchart
  rw [←ambientGroup_ambientSpace hmapV,←ambientGroup_ambientSpace (show V⊓U≤V from inf_le_left),hspaces]
omit [IsElementaryAbelian 2 U] in
theorem image_offender_of_conjugate
    (E : Additive V≃ₗ[K] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (g : G) (hc : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≠⊥) :
    IsOffender rho ((inducedAutomizer V (V.map (MulAut.conj g).toMonoidHom)).map f) := by
  let U := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  let e := automizerMapEquiv V (MulAut.conj g)
  let eV := automizerModuleEquiv V (MulAut.conj g)
  let EU := eV.symm.trans E
  let fU := f.comp e.symm.toMonoidHom
  apply image_offender_of_two_natural_actions E f he EU fU _ hc hne
  intro a v
  change E (eV.symm (automizerRepresentation U a v))=rho (f (e.symm a)) (E (eV.symm v))
  rw [←he]
  apply congrArg E
  apply eV.injective
  rw [eV.apply_symm_apply]
  have hh := automizerRepresentation_equivariant V (MulAut.conj g) (e.symm a) (eV.symm v)
  simpa only [eV,e,LinearEquiv.apply_symm_apply,MulEquiv.apply_symm_apply] using hh.symm

omit [IsElementaryAbelian 2 U] in
theorem source_escape_of_noncommuting_intersection
    {K₀ : GroupClass} {T : Sylow 2 G} {M : Subgroup G}
    (h : ChapterE.Section06.HypothesisE61 K₀ T M V)
    (E : Additive V≃ₗ[K] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hderived : commutator (Atlas.G2.Model K)≤(inducedAutomizer V L).map f)
    (hLM : L≤M) (g : G)
    (hc : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≠⊥) :
    ¬centralizer (standardThree E:Set G)≤M := by
  have horbit (x : G)
      (hx : ⁅V,V.map (MulAut.conj x).toMonoidHom⁆≤V⊓V.map (MulAut.conj x).toMonoidHom)
      (hnx : ⁅V,V.map (MulAut.conj x).toMonoidHom⁆≠⊥) :
      ∃n∈L,n∈normalizer (V:Set G) ∧
        (standardThree E).map (MulAut.conj n).toMonoidHom=V⊓V.map (MulAut.conj x).toMonoidHom := by
    let : IsElementaryAbelian 2 (V.map (MulAut.conj x).toMonoidHom) := IsElementaryAbelian.map _
    exact exists_local_standard_intersection E f he hderived
      (image_offender_of_conjugate E f he x hx hnx) hx
  obtain ⟨n,hnL,hnN,hnI⟩ := horbit g hc hne
  have hnVi := Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.inv_mem _ hnN)
  change V.map (MulAut.conj n⁻¹).toMonoidHom=V at hnVi
  have hnS : (V⊓V.map (MulAut.conj g).toMonoidHom).map (MulAut.conj n⁻¹).toMonoidHom=standardThree E := by
    rw [←hnI,offender_map_conj_inverse]
  let x := n⁻¹*g
  have hxI : V⊓V.map (MulAut.conj x).toMonoidHom=standardThree E := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj n⁻¹).injective,hnVi,offender_map_conj_map] at hnS
    exact hnS
  have hxmap : (⁅V,V.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj n⁻¹).toMonoidHom=
      ⁅V,V.map (MulAut.conj x).toMonoidHom⁆ := by
    rw [Subgroup.map_commutator,hnVi,offender_map_conj_map]
  have hx : ⁅V,V.map (MulAut.conj x).toMonoidHom⁆≤V⊓V.map (MulAut.conj x).toMonoidHom := by
    rw [hxI,←hnS,←hxmap]
    exact Subgroup.map_mono hc
  have hnx : ⁅V,V.map (MulAut.conj x).toMonoidHom⁆≠⊥ := by
    rw [←hxmap]
    exact fun hh=>hne ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj n⁻¹).injective).mp hh)
  have hximap : (⁅V,V.map (MulAut.conj x).toMonoidHom⁆).map (MulAut.conj x⁻¹).toMonoidHom=
      ⁅V,V.map (MulAut.conj x⁻¹).toMonoidHom⁆ := by
    rw [Subgroup.map_commutator,offender_map_conj_inverse,Subgroup.commutator_comm]
  have hxiI : (V⊓V.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom=
      V⊓V.map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj x⁻¹).injective,offender_map_conj_inverse,inf_comm]
  have hxi : ⁅V,V.map (MulAut.conj x⁻¹).toMonoidHom⁆≤V⊓V.map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [←hximap,←hxiI]
    exact Subgroup.map_mono hx
  have hnxi : ⁅V,V.map (MulAut.conj x⁻¹).toMonoidHom⁆≠⊥ := by
    rw [←hximap]
    exact fun hh=>hnx ((Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj x⁻¹).injective).mp hh)
  obtain ⟨m,hmL,hmN,hmI⟩ := horbit x⁻¹ hxi hnxi
  have hmV := Subgroup.mem_normalizer_iff_map_conj_eq.mp hmN
  change V.map (MulAut.conj m).toMonoidHom=V at hmV
  have hsame : V.map (MulAut.conj (x*m)).toMonoidHom=V.map (MulAut.conj x).toMonoidHom := by
    rw [←offender_map_conj_map,hmV]
  have hkN : x*m∈normalizer (standardThree E:Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    change (standardThree E).map (MulAut.conj (x*m)).toMonoidHom=standardThree E
    rw [←offender_map_conj_map,hmI,Subgroup.map_inf _ _ _ (MulAut.conj x).injective]
    have hh := offender_map_conj_inverse V x⁻¹
    simp only [inv_inv] at hh
    rw [hh,inf_comm,hxI]
  exact source_escape_of_standard_intersection h E f he hderived hLM (x*m) hkN
    (by rw [hsame,hxI]) (standardThree_space E) (by rwa [hsame]) (by rwa [hsame])
omit [IsElementaryAbelian 2 U] in
theorem source_noncommuting_intersection_geometry
    {K₀ : GroupClass} {T : Sylow 2 G} {M : Subgroup G}
    (h : ChapterE.Section06.HypothesisE61 K₀ T M V)
    (E : Additive V≃ₗ[K] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hderived : commutator (Atlas.G2.Model K)≤(inducedAutomizer V L).map f)
    (hLM : L≤M) (g : G)
    (hc : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≠⊥) :
    (V⊓V.map (MulAut.conj g).toMonoidHom=⁅V,V.map (MulAut.conj g).toMonoidHom⁆) ∧
    (⁅V,V.map (MulAut.conj g).toMonoidHom⁆=V⊓centralizer (V.map (MulAut.conj g).toMonoidHom:Set G)) ∧
    (∃n∈L,n∈normalizer (V:Set G) ∧ (standardThree E).map (MulAut.conj n).toMonoidHom=
      V⊓V.map (MulAut.conj g).toMonoidHom) ∧ ¬centralizer (standardThree E:Set G)≤M := by
  let : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  have hA := image_offender_of_conjugate E f he g hc hne
  exact ⟨intersection_eq_commutator_of_offender E f he hA hc,
    commutator_eq_fixed_of_offender E f he hA hc,
    exists_local_standard_intersection E f he hderived hA hc,
    source_escape_of_noncommuting_intersection h E f he hderived hLM g hc hne⟩

omit [IsElementaryAbelian 2 U] in
theorem source_commuting_intersections_of_three_centralizer
    {K₀ : GroupClass} {T : Sylow 2 G} {M : Subgroup G}
    (h : ChapterE.Section06.HypothesisE61 K₀ T M V)
    (E : Additive V≃ₗ[K] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hderived : commutator (Atlas.G2.Model K)≤(inducedAutomizer V L).map f)
    (hLM : L≤M) (hC : centralizer (standardThree E:Set G)≤M)
    (g : G) (hc : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom) :
    ⁅V,V.map (MulAut.conj g).toMonoidHom⁆=⊥ := by
  by_contra hne
  exact source_escape_of_noncommuting_intersection h E f he hderived hLM g hc hne hC

omit [IsElementaryAbelian 2 U] in
theorem source_escape_of_noncommuting_intersection_of_normal_layer
    {K₀ : GroupClass} {T : Sylow 2 G} {M : Subgroup G}
    (h : ChapterE.Section06.HypothesisE61 K₀ T M V)
    (hLN : L≤normalizer (V:Set G)) (hNL : normalizer (V:Set G)≤normalizer (L:Set G))
    (e : inducedAutomizer V L≃*Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive V≃ₗ[K]Atlas.G2.Natural.Space K)
    (he0 : ∀(l:inducedAutomizer V L) v,E0 (automizerRepresentation V l v)=
      Atlas.G2.Natural.derivedAction K (e l) (E0 v))
    (hLM : L≤M) (g : G)
    (hc : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≠⊥) :
    ¬centralizer (standardThree (E0.trans (Atlas.G2.Restricted.NaturalCoordinates.equiv K)):Set G)≤M := by
  let I:=inducedAutomizer V L
  let : (L.subgroupOf (normalizer (V:Set G))).Normal:=
    (normal_subgroupOf_iff_le_normalizer hLN).mpr hNL
  let : I.Normal:=Subgroup.Normal.map inferInstance V.normalizerMonoidHom.rangeRestrict
    V.normalizerMonoidHom.rangeRestrict_surjective
  obtain ⟨f,_,hl,hfull⟩:=Atlas.G2.Natural.BinaryNormalizer.ambient_embedding
    (automizerRepresentation V) I e E0 he0 (automizerRepresentation_injective V)
  let E:=E0.trans (Atlas.G2.Restricted.NaturalCoordinates.equiv K)
  have he:∀a v,E (automizerRepresentation V a v)=rho (f a) (E v) := by
    intro a v
    change Atlas.G2.Restricted.NaturalCoordinates.equiv K (E0 (automizerRepresentation V a v))=_
    rw [hfull]
    exact (Atlas.G2.Restricted.NaturalCoordinates.repEquiv K).isIntertwining (f a) (E0 v)
  have hd:commutator (Atlas.G2.Model K)≤I.map f := by
    intro a ha
    obtain ⟨i,hi⟩:=e.surjective ⟨a,ha⟩
    exact ⟨i,i.prop,(hl i).trans (congrArg Subtype.val hi)⟩
  exact source_escape_of_noncommuting_intersection h E f he hd hLM g hc hne
end CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
