module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.SylowModels.ModelFacts
public import CFSG.Quasithin.Chapter16.Section03.Basic
public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Intrinsic.Action
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.GeneratorPair.FirstFusion.Representative

/-!
# The intrinsic fusion obligation for the J₂ branch of 16.3.4

The remaining model assertion concerns actual components of fixed subgroups
of involutory automorphisms. The ambient commutator hypothesis makes the
induced action nontrivial, hence of order two. Actual fixed-subgroup and
component isomorphisms then transport intrinsic fusion back to L inside K.

`J2ComponentInvolutionFusion` is a specification, not a proved fusion table.
Its inner and outer cases remain separate obligations. Source:
Aschbacher–Smith, proof of 16.3.4, printed p.1178 / PDF p.1195, using 16.1.5(8).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
open Subgroup Theory.GroupTheory ClassificationModels
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.GeneratorPair
open ComponentTransfer.Intrinsic
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z t i : G} {L K : Subgroup G}

/-- The intrinsic remaining fusion calculation, stated for actual components. -/
def J2ComponentInvolutionFusion (r : MulAut Carrier) : Prop :=
  ∀ D : Subgroup r.fixedSubgroup, IsComponent r.fixedSubgroup D →
    ∀ x : D, orderOf x = 2 → IsConj FirstFusion.t ((x : r.fixedSubgroup) : Carrier)

omit [Finite G] in
private theorem setup_normalizes (h : ExclusionSetup T z L K t i) : i ∈ normalizer K :=
  (le_normalizer_iff_commutator_le_left.mpr h.commutator_eq.le) (mem_zpowers i)

omit [Finite G] in
private theorem setup_action_order (h : ExclusionSetup T z L K t i) :
    orderOf (action (setup_normalizes h)) = 2 := by
  let hn := setup_normalizes h
  have hs : action hn ^ 2 = 1 := by
    change K.normalizerMonoidHom (⟨i, hn⟩ : normalizer K) ^ 2 = 1
    rw [← map_pow, show (⟨i, hn⟩ : normalizer K) ^ 2 = 1 from
      Subtype.ext (h.involution_i ▸ pow_orderOf_eq_one i), map_one]
  apply orderOf_eq_prime hs
  intro he
  have hiC : i ∈ centralizer (K : Set G) := by
    intro x hx
    have hh := congrArg Subtype.val (DFunLike.congr_fun he ⟨x, hx⟩)
    change i * x * i⁻¹ = x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hb : ⁅zpowers i, K⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (zpowers_le.mpr hiC)
  rw [commutator_comm, h.commutator_eq] at hb
  exact IsComponentIn.ne_bot h.componentK hb

omit [Finite G] in
/-- Intrinsic component fusion transports through the actual ambient involution action. -/
theorem j2_element_fusion_of_component_fusion
    (h : ExclusionSetup T z L K t i) (eK : K ≃* SporadicName.j2.Carrier)
    (fusion : ∀ r : MulAut Carrier, orderOf r = 2 → J2ComponentInvolutionFusion r)
    (v : L) (hv : orderOf v = 2) :
    IsConj FirstFusion.t (eK (Subgroup.inclusion (h.componentL.1.trans inf_le_left) v)) := by
  let hn := setup_normalizes h
  let a := action hn
  let r := MulAut.congr eK a
  have hr : orderOf r = 2 := ((MulAut.congr eK).orderOf_eq a).trans (setup_action_order h)
  have hf : a.fixedSubgroup.map eK.toMonoidHom = r.fixedSubgroup := by
    ext w
    constructor
    · rintro ⟨u, hu, rfl⟩
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      change eK (a (eK.symm (eK u))) = eK u
      rw [eK.symm_apply_apply, (MulAut.mem_fixedSubgroup a u).mp hu]
    · intro hw
      refine ⟨eK.symm w, (MulAut.mem_fixedSubgroup _ _).mpr ?_, eK.apply_symm_apply w⟩
      apply eK.injective
      change eK (a (eK.symm w)) = eK (eK.symm w)
      rw [eK.apply_symm_apply]
      exact (MulAut.mem_fixedSubgroup r w).mp hw
  let C := K ⊓ involutionCentralizer i
  let f : C ≃* r.fixedSubgroup :=
    (centralizerEquivFixed hn).trans
      ((eK.subgroupMap a.fixedSubgroup).trans (MulEquiv.subgroupCongr hf))
  let D := (L.subgroupOf C).map f.toMonoidHom
  have hD : IsComponent r.fixedSubgroup D := h.componentL.2.map_equiv f
  let y : L.subgroupOf C := ⟨⟨v, h.componentL.1 v.property⟩, v.property⟩
  let x : D := ⟨f y, mem_map_of_mem f.toMonoidHom y.property⟩
  have hy : orderOf y = 2 :=
    ((subgroupOfEquivOfLe h.componentL.1).orderOf_eq y).symm.trans hv
  have hx : orderOf x = 2 := (orderOf_coe x).symm.trans ((f.orderOf_eq y).trans
    ((orderOf_coe y).trans hy))
  exact fusion r hr D hD x hx

end CFSG.Quasithin.Chapter16.FourGroupTransfer.SylowModels
