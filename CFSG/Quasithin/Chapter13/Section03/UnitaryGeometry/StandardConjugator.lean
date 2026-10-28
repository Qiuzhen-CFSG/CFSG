module

public import CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry.PairPoint
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry.IntrinsicPoint
import all CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF


/-!
# Final standard three-space escape

The paired intrinsic hyperplanes identify the distinguished point in the
original module and its conjugate. Thus a conjugator preserving their
standard intersection normalizes its order-two point and fixes that point.
The actual local point stabilizer then factors this conjugator, producing
an element of the three-space centralizer outside the distinguished maximal.

The internal AutomizerFF import is used only to identify its module transport
with the original ambient conjugation; no private name enters a public type.

Source: Aschbacher–Smith 13.3.12(4), printed p.890.
-/

public section

open Subgroup Module Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
open Atlas.G2.Natural.BinaryIsotropicThree
variable {G : Type*} [Group G] [Finite G] {V R : Subgroup G} [IsElementaryAbelian 2 V]

theorem conjugator_fixes_point_of_standard_intersection
    (E : Additive V≃ₗ[K] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (g : G) (hgR : g∈normalizer (R:Set G))
    (hI : V⊓V.map (MulAut.conj g).toMonoidHom=R)
    (hR : (ambientSpace (V:=V) R).map E.toLinearMap=target false)
    (hc : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≠⊥) :
    Commute g (E.symm firstVector).toMul.val := by
  let U := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  let e := automizerMapEquiv V (MulAut.conj g)
  let eV := automizerModuleEquiv V (MulAut.conj g)
  let EU := eV.symm.trans E
  let fU := f.comp e.symm.toMonoidHom
  have heU (a : Automizer U) (v : Additive U) :
      EU (automizerRepresentation U a v)=rho (fU a) (EU v) := by
    change E (eV.symm (automizerRepresentation U a v))=rho (f (e.symm a)) (E (eV.symm v))
    rw [←he]
    apply congrArg E
    apply eV.injective
    rw [eV.apply_symm_apply]
    have hh := automizerRepresentation_equivariant V (MulAut.conj g) (e.symm a) (eV.symm v)
    simpa only [eV,e,LinearEquiv.apply_symm_apply,MulEquiv.apply_symm_apply] using hh.symm
  have hspaces : (ambientSpace (V:=U) R).map eV.symm.toLinearMap=ambientSpace (V:=V) R := by
    ext v
    constructor
    · rintro ⟨w,hw,rfl⟩
      change (eV.symm w).toMul.val∈R
      have hw' : w.toMul.val∈R := hw
      have hlin : (eV.symm w).toMul.val=g⁻¹*w.toMul.val*g := by
        have hh := congrArg (fun v : Additive U=>v.toMul.val) (eV.apply_symm_apply w)
        change g*(eV.symm w).toMul.val*g⁻¹=w.toMul.val at hh
        calc
          _=g⁻¹*(g*(eV.symm w).toMul.val*g⁻¹)*g := by group
          _=_ := by rw [hh]
      rw [hlin]
      simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgR) w.toMul.val).mp hw'
    · intro hv
      refine ⟨eV v,?_,eV.symm_apply_apply v⟩
      change g*v.toMul.val*g⁻¹∈R
      exact (Subgroup.mem_normalizer_iff.mp hgR v.toMul.val).mp hv
  have hRU : (ambientSpace (V:=U) R).map EU.toLinearMap=target false := by
    change (ambientSpace (V:=U) R).map (E.toLinearMap.comp eV.symm.toLinearMap)=_
    rw [Submodule.map_comp,hspaces,hR]
  have hz := common_pair_point_of_two_natural_actions E f he EU fU heU hc hne
    (hI ▸ hR) (hI ▸ hRU)
  let p := (E.symm firstVector).toMul.val
  have hp2 : p^2=1 := elemPow_eq_one_of_isElementaryAbelian p (E.symm firstVector).toMul.property
  have hp1 : p≠1 := by
    intro hh
    have hz : E.symm firstVector=0 := congrArg Additive.ofMul (Subtype.ext hh)
    have hx := congrArg E hz
    have hc0 := congrFun hx 0
    simp [firstVector] at hc0
  have hporder : orderOf p=2 := orderOf_eq_prime hp2 hp1
  have hcZ : Nat.card (zpowers p)=2 := by rw [Nat.card_zpowers,hporder]
  have hgpoint : (EU.symm firstVector).toMul.val=g*p*g⁻¹ := by rfl
  have hnZ : g∈normalizer (zpowers p:Set G) := by
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    change zpowers (g*p*g⁻¹)=zpowers p
    rw [hgpoint] at hz
    exact hz.symm
  have hcg := Subgroup.normalizer_le_centralizer_of_card_two (zpowers p) hcZ hnZ
  exact ((Subgroup.mem_centralizer_iff.mp hcg) p (mem_zpowers p)).symm

variable {K₀ : GroupClass} {T : Sylow 2 G} {M L : Subgroup G}

theorem source_escape_of_standard_intersection
    (h : ChapterE.Section06.HypothesisE61 K₀ T M V)
    (E : Additive V≃ₗ[K] W) (f : Automizer V→*Atlas.G2.Model K)
    (he : ∀a v,E (automizerRepresentation V a v)=rho (f a) (E v))
    (hderived : commutator (Atlas.G2.Model K)≤(inducedAutomizer V L).map f)
    (hLM : L≤M) (g : G) (hgR : g∈normalizer (R:Set G))
    (hI : V⊓V.map (MulAut.conj g).toMonoidHom=R)
    (hR : (ambientSpace (V:=V) R).map E.toLinearMap=target false)
    (hc : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hne : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆≠⊥) :
    ¬centralizer (R:Set G)≤M := by
  have hRV : R≤V := hI ▸ inf_le_left
  let := IsElementaryAbelian.of_le (p:=2) hRV
  obtain ⟨F,hF⟩ := exists_three_coordinates hRV E hR
  have hp : (F.symm ![1,0,0]).toMul.val=(E.symm firstVector).toMul.val := by
    have hh := hF (F.symm ![1,0,0])
    rw [F.apply_symm_apply] at hh
    exact congrArg (fun v : Additive V=>v.toMul.val)
      (E.injective (hh.trans (E.apply_symm_apply _).symm))
  apply centralizer_three_escape_of_noncommuting_conjugate h.ti hRV E F hF f he _ hLM g hgR _ hne
  · intro d
    exact hderived d.property
  · rw [hp]
    exact conjugator_fixes_point_of_standard_intersection E f he g hgR hI hR hc hne
end CFSG.Quasithin.Chapter13.Section03.UnitaryGeometry
