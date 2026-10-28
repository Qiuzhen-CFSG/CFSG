module
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Inner
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.Janko2.Fusion
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.Janko2.InnerFusion.SimpleFactor

/-!
# Central-class fusion for components of inner J₂ involution centralizers

For the central involution representative there are no components, by the
self-centralizing normal two-kernel. In the other centralizer, the actual
isomorphism with E₄ × A₅ preserves the checked embedding of the simple factor.
Perfectness kills the E₄ projection of a component. Its involutions therefore
belong to the marked A₅ factor, whose explicit words are checked conjugates
of `FirstFusion.t`. Finally, transport by the actual inner conjugator keeps
track of the inclusion in the unchanged degree-100 J₂ carrier.

This proves the inner case of the component-fusion obligation used in
Aschbacher–Smith 16.3.4, printed p.1178 / PDF p.1195, using the centralizer
alternatives of 16.1.5(8), printed p.1172. The ambient Sylow argument and the
outer-automorphism case have separate owners.
-/

open Subgroup Theory.GroupTheory
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open Sporadic.LeechRelated.J2.GeneratorPair.SecondOrbitCertificate
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open J2Inner J2Inner.NoncentralData

namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
private theorem noncentral_component_fusion
    (D : Subgroup (Subgroup.centralizer ({a} : Set Carrier)))
    (hD : IsComponent _ D) (x : D) (hx : orderOf x = 2) :
    IsConj FirstFusion.t ((x : Subgroup.centralizer ({a} : Set Carrier)) : Carrier) := by
  let := hD.2
  let f : D →* E4 := (MonoidHom.fst E4 A5).comp
    (a_centralizer_equiv.toMonoidHom.comp D.subtype)
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hf : (a_centralizer_equiv (x : Subgroup.centralizer ({a} : Set Carrier))).1 = 1 :=
    congrArg Subtype.val (Subsingleton.elim (f.rangeRestrict x) 1)
  obtain ⟨i, hi⟩ := simpleEquiv.surjective
    (a_centralizer_equiv (x : Subgroup.centralizer ({a} : Set Carrier))).2
  have he : a_centralizer_equiv (x : Subgroup.centralizer ({a} : Set Carrier)) =
      (1, simpleEquiv i) := Prod.ext hf hi.symm
  have ho : orderOf (simpleEquiv i) = 2 := by
    have h := (a_centralizer_equiv.orderOf_eq
      (x : Subgroup.centralizer ({a} : Set Carrier))).trans ((orderOf_coe x).trans hx)
    simpa only [he, Prod.orderOf_mk, orderOf_one, Nat.lcm_one_left] using h
  have hw := congrArg (fun y => (a_centralizer_equiv.symm y).val) he
  rw [a_centralizer_equiv.symm_apply_apply, a_centralizer_equiv_symm_simple] at hw
  rw [hw]
  exact J2InnerFusion.simple_involution_fusion i ho

private theorem fusion_transport (q g : Carrier)
    (hq : ∀ D : Subgroup (centralizer ({q} : Set Carrier)), IsComponent _ D →
      ∀ x : D, orderOf x = 2 → IsConj FirstFusion.t ((x : centralizer ({q} : Set Carrier)) : Carrier)) :
    J2ComponentInvolutionFusion (MulAut.congr (MulAut.conj g) (MulAut.conj q)) := by
  let c := MulAut.conj g
  let r := MulAut.congr c (MulAut.conj q)
  have hf : (MulAut.conj q).fixedSubgroup.map c.toMonoidHom = r.fixedSubgroup := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      change c ((MulAut.conj q) (c.symm (c u))) = c u
      rw [c.symm_apply_apply, (MulAut.mem_fixedSubgroup _ _).mp hu]
    · intro hw
      refine ⟨c.symm w, (MulAut.mem_fixedSubgroup _ _).mpr ?_, c.apply_symm_apply w⟩
      apply c.injective
      rw [c.apply_symm_apply]
      exact (MulAut.mem_fixedSubgroup r w).mp hw
  let e : centralizer ({q} : Set Carrier) ≃* r.fixedSubgroup :=
    (MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj q)).symm.trans
      ((c.subgroupMap (MulAut.conj q).fixedSubgroup).trans (MulEquiv.subgroupCongr hf))
  intro D hD x hx
  let D0 := D.map e.symm.toMonoidHom
  let y : D0 := ⟨e.symm (x : r.fixedSubgroup), mem_map_of_mem _ x.property⟩
  have hy : orderOf y = 2 := (orderOf_coe y).symm.trans
    ((e.symm.orderOf_eq (x : r.fixedSubgroup)).trans ((orderOf_coe x).trans hx))
  refine (hq D0 (hD.map_equiv e.symm) y hy).trans ?_
  apply isConj_iff.mpr
  refine ⟨g, ?_⟩
  change (e (e.symm (x : r.fixedSubgroup)) : Carrier) = _
  rw [e.apply_symm_apply]

/-- Every involution in an actual component fixed by an inner involution of J₂
is conjugate, inside J₂ itself, to the central representative. -/
public theorem j2_inner_component_involution_fusion (r : MulAut Carrier)
    (hr : orderOf r = 2) (hi : ∃ g : Carrier, r = MulAut.conj g) :
    J2ComponentInvolutionFusion r := by
  rcases J2Reduction.inner_involution_representatives r hr hi with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact fusion_transport a g noncentral_component_fusion
  · apply fusion_transport FirstFusion.t g
    intro D hD
    exact (t_selfCentralizing.not_isComponent D hD).elim

end CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
