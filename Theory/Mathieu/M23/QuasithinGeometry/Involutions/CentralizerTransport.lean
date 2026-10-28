module

public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerKernel
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Exhaustive transport and component exclusion for M23 involutions

Involution fusion identifies every element centralizer with the certified
representative centralizer. Since M23 is centerless, the conjugating element
of an inner automorphism of order two is itself an involution. Thus the same
identification applies to all inner involutory automorphisms.

The genuine self-centralizing normal binary kernel excludes components:
a component either lies in or centralizes that kernel, and either alternative
would make a nontrivial perfect group solvable. This uses the proved faithful
kernel action, rather than inferring the assertion from an extension shape.
The exact sequence also transports through any supplied quotient-model
isomorphism. Innerness of arbitrary automorphisms and identification of the
seven-point image with PSL3(2) remain separate model obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.5(6)
and its use in 16.1.7–8, printed pp.1171–1173.
-/

public section

open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M23Geometry.InvolutionCentralizer

/-- Exhaustive fusion transports every involution centralizer to the representative. -/
theorem centralizer_equiv_representative {t : M23} (ht : orderOf t = 2) :
    Nonempty (centralizer ({t} : Set M23) ≃* representativeCentralizer) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (involutions_isConj t involutionRepresentative ht involutionRepresentative_order)
  have hg' : MulAut.conj g t = involutionRepresentative := hg
  exact ⟨(MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj t)).symm.trans
    ((MulAut.fixedSubgroupCongr (MulAut.conj g) (MulAut.conj t)).trans
      (MulEquiv.subgroupCongr (by
        rw [MulAut.congr_conj, hg', MulAut.fixedSubgroup_conj])))⟩

/-- Centerlessness reduces inner involutory automorphisms to element involutions. -/
theorem fixedSubgroup_equiv_representative_of_inner (r : MulAut M23)
    (hr : orderOf r = 2) (hi : ∃ g, r = MulAut.conj g) :
    Nonempty (r.fixedSubgroup ≃* representativeCentralizer) := by
  obtain ⟨g, rfl⟩ := hi
  have hg : orderOf g = 2 :=
    (orderOf_injective MulAut.conj
      (MulAut.conj_injective_of_center_eq_bot m23_center_eq_bot) g).symm.trans hr
  obtain ⟨e⟩ := centralizer_equiv_representative hg
  exact ⟨(MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj g)).trans e⟩

/-- The faithful binary kernel action rules out components in the representative centralizer. -/
theorem representative_no_component (K : Subgroup representativeCentralizer) :
    ¬ IsComponent representativeCentralizer K := by
  intro hK
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have hKQ : K ≤ kernel := by
    rcases hK.normal_dichotomy kernel with hle | hc
    · exact hle
    · exact (commutator_eq_bot_iff_le_centralizer.mp hc).trans kernel_selfCentralizing
  let : Group.IsNilpotent K := (kernel_isTwoGroup.to_le hKQ).isNilpotent
  exact Group.IsPerfect.not_isSolvable K inferInstance

/-- No element involution centralizer in the actual M23 has a component. -/
theorem centralizer_no_component {t : M23} (ht : orderOf t = 2)
    (K : Subgroup (centralizer ({t} : Set M23))) :
    ¬ IsComponent (centralizer ({t} : Set M23)) K := by
  obtain ⟨e⟩ := centralizer_equiv_representative ht
  intro hK
  exact representative_no_component (K.map e.toMonoidHom) (hK.map_equiv e)

/-- The same exclusion holds for each inner involutory automorphism. -/
theorem fixedSubgroup_no_component_of_inner (r : MulAut M23)
    (hr : orderOf r = 2) (hi : ∃ g, r = MulAut.conj g)
    (K : Subgroup r.fixedSubgroup) : ¬ IsComponent r.fixedSubgroup K := by
  obtain ⟨e⟩ := fixedSubgroup_equiv_representative_of_inner r hr hi
  intro hK
  exact representative_no_component (K.map e.toMonoidHom) (hK.map_equiv e)

/-- Transport the genuine exact sequence through middle- and quotient-group isomorphisms. -/
noncomputable def extensionOfEquiv {C Q : Type*} [Group C] [Group Q]
    (e : C ≃* representativeCentralizer) (q : action.range ≃* Q) :
    GroupExtension (Fin 4 → Multiplicative (ZMod 2)) C Q where
  inl := e.symm.toMonoidHom.comp extension.inl
  rightHom := q.toMonoidHom.comp (extension.rightHom.comp e.toMonoidHom)
  inl_injective := e.symm.injective.comp extension.inl_injective
  range_inl_eq_ker_rightHom := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      change q (extension.rightHom (e (e.symm (extension.inl v)))) = 1
      rw [e.apply_symm_apply, extension.rightHom_inl, map_one]
    · intro hx
      have hx' : extension.rightHom (e x) = 1 := by
        apply q.injective
        exact hx.trans (map_one q).symm
      have hm : e x ∈ extension.inl.range := by
        rw [extension.range_inl_eq_ker_rightHom]
        exact hx'
      obtain ⟨v, hv⟩ := hm
      exact ⟨v, by change e.symm (extension.inl v) = x; rw [hv, e.symm_apply_apply]⟩
  rightHom_surjective := q.surjective.comp (extension.rightHom_surjective.comp e.surjective)

end Sporadic.Mathieu.M23Geometry.InvolutionCentralizer
