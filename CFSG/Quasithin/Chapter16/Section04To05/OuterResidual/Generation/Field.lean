module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.Basic
public import Theory.SpecificGroups.PSL2.FieldCentralizerGeneration

/-!
# Actual field actions in the residual-transfer configuration

A binary field involution is represented by an isomorphism of L itself with
PSL₂(2ⁿ), n > 2, intertwining conjugation by r with entrywise application of a
nonidentity field involution. This retains the action, not just the fixed-group
isomorphism type. Matrix transvections prove centralizer generation in that
model. Transport preserves the embedded centralizers, and perfectness of the
fixed subgroup shows that those involutions lie in the actual residual Lᵣ.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Lemma 16.4.8, printed p.1188. The model sieve and the component-placement
argument are separate obligations; neither is part of the definition below.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual
open Subgroup Theory.GroupTheory ComponentTransfer

/-- A concrete action witness for the unique remaining field branch. -/
def IsBinaryFieldInvolution {A : Type*} [Group A] (a : MulAut A) : Prop :=
  ∃ (n : ℕ) (_ : 2 < n) (e : A ≃* Theory.PSL2.BinaryGroup n)
    (σ : Theory.PSL2.BinaryField n ≃+* Theory.PSL2.BinaryField n),
      orderOf σ = 2 ∧ MulAut.congr e a = Theory.PSL2.fieldAut σ

/-- Absorb the inner conjugation of a field action into the actual model isomorphism. -/
theorem isBinaryFieldInvolution_of_conjugate_field {A : Type*} [Group A]
    (a : MulAut A) {n : ℕ} (hn : 2 < n) (e : A ≃* Theory.PSL2.BinaryGroup n)
    (σ : Theory.PSL2.BinaryField n ≃+* Theory.PSL2.BinaryField n) (hσ : orderOf σ = 2)
    (c : Theory.PSL2.BinaryGroup n)
    (he : MulAut.congr e a = MulAut.congr (MulAut.conj c) (Theory.PSL2.fieldAut σ)) :
    IsBinaryFieldInvolution a := by
  refine ⟨n, hn, e.trans (MulAut.conj c).symm, σ, hσ, ?_⟩
  ext x
  have hx := congrArg (fun b : MulAut (Theory.PSL2.BinaryGroup n) =>
    (MulAut.conj c).symm (b (MulAut.conj c x))) he
  change (MulAut.conj c).symm (e (a (e.symm (MulAut.conj c x)))) =
    (MulAut.conj c).symm ((MulAut.conj c)
      (Theory.PSL2.fieldAut σ ((MulAut.conj c).symm (MulAut.conj c x)))) at hx
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply] at hx
  exact hx

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- A full fixed residual identifies Lᵣ with C_L(r), preserving its embedding. -/
theorem involutionResidual_eq_centralizer_of_fixed_residual_top
    (h : IntersectionSetup T z L g R) (hr : r ∈ R)
    (htop : pResidual 2 (involutionAction h hr).fixedSubgroup = ⊤) :
    involutionResidual L r = L ⊓ involutionCentralizer r := by
  have hc : pResidual 2 (centralizerIn L r) = ⊤ := by
    apply Subgroup.map_injective
      (f := (Intrinsic.centralizerEquivFixed
        (h.sylow_normalizes (h.le_sylow hr))).toMonoidHom)
      (Intrinsic.centralizerEquivFixed (h.sylow_normalizes (h.le_sylow hr))).injective
    rw [map_pResidual, htop,
      map_top_of_surjective _ (Intrinsic.centralizerEquivFixed
        (h.sylow_normalizes (h.le_sylow hr))).surjective]
  change (pResidual 2 (centralizerIn L r)).map _ = _
  rw [hc, ← MonoidHom.range_eq_map, range_subtype]
  rfl

/-- Transport centralizer generation along an isomorphism intertwining the actions. -/
theorem centralizers_generate_of_fixed_model
    (h : IntersectionSetup T z L g R) (hr : r ∈ R)
    {A : Type*} [Group A] (e : L ≃* A) (a : MulAut A)
    (he : MulAut.congr e (involutionAction h hr) = a)
    (hgen : (⨆ (j : A) (_ : j ∈ a.fixedSubgroup) (_ : orderOf j = 2),
      centralizer ({j} : Set A)) = ⊤) :
    (⨆ (j : G) (_ : j ∈ L ⊓ involutionCentralizer r) (_ : orderOf j = 2),
      L ⊓ involutionCentralizer j) = L := by
  let S : Subgroup G := ⨆ (j : G) (_ : j ∈ L ⊓ involutionCentralizer r)
    (_ : orderOf j = 2), L ⊓ involutionCentralizer j
  let f : A →* G := L.subtype.comp e.symm.toMonoidHom
  have htop : ⊤ ≤ S.comap f := by
    rw [← hgen]
    refine iSup_le fun j => iSup_le fun hj => iSup_le fun hj2 => ?_
    have hfix : e.symm j ∈ (involutionAction h hr).fixedSubgroup := by
      rw [MulAut.mem_fixedSubgroup]
      apply e.injective
      have hx := congrArg (fun b : MulAut A => b j) he
      change e (involutionAction h hr (e.symm j)) = a j at hx
      simpa only [e.apply_symm_apply] using hx.trans ((MulAut.mem_fixedSubgroup a j).mp hj)
    have hjr : f j ∈ L ⊓ involutionCentralizer r :=
      ⟨(e.symm j).property, (Intrinsic.mem_fixed_action
        (h.sylow_normalizes (h.le_sylow hr)) (e.symm j)).mp hfix⟩
    have horder : orderOf (f j) = 2 := by
      rw [orderOf_injective f (L.subtype_injective.comp e.symm.injective), hj2]
    intro x hx
    change f x ∈ S
    refine mem_iSup_of_mem (f j) (mem_iSup_of_mem hjr (mem_iSup_of_mem horder ?_))
    refine ⟨(e.symm x).property, ?_⟩
    change f x ∈ centralizer ({f j} : Set G)
    rw [mem_centralizer_singleton_iff]
    simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hx)
  apply le_antisymm
  · exact iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => inf_le_left
  · intro x hx
    have hm := htop (show e ⟨x, hx⟩ ∈ ⊤ from trivial)
    change f (e ⟨x, hx⟩) ∈ S at hm
    simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply, subtype_apply] using hm

/-- In the field branch with n > 2 the centralizer is already two-perfect. -/
theorem involutionResidual_eq_centralizer_of_binaryField
    (h : IntersectionSetup T z L g R) (hr : r ∈ R)
    (hfield : IsBinaryFieldInvolution (involutionAction h hr)) :
    involutionResidual L r = L ⊓ involutionCentralizer r := by
  obtain ⟨n, hn, e, σ, hσ, he⟩ := hfield
  have hs : Function.Involutive σ := by
    intro x
    have hp := pow_orderOf_eq_one σ
    rw [hσ] at hp
    exact DFunLike.congr_fun hp x
  have hne : σ ≠ RingEquiv.refl _ := by
    intro hz
    have hz' : σ = 1 := hz
    rw [hz', orderOf_one] at hσ
    contradiction
  have ht := Theory.PSL2.binary_fixed_twoResidual_eq_top hn σ hs hne
  let c : (involutionAction h hr).fixedSubgroup ≃*
      (Theory.PSL2.fieldAut σ).fixedSubgroup :=
    (MulAut.fixedSubgroupCongr e (involutionAction h hr)).trans
      (MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup he))
  have ha : pResidual 2 (involutionAction h hr).fixedSubgroup = ⊤ := by
    apply Subgroup.map_injective (f := c.toMonoidHom) c.injective
    rw [map_pResidual, ht, map_top_of_surjective _ c.surjective]
  exact involutionResidual_eq_centralizer_of_fixed_residual_top h hr ha

/-- The source generation equality, proved from the actual field action. -/
theorem involutionResidual_centralizers_generate_of_binaryField
    (h : IntersectionSetup T z L g R) (hr : r ∈ R)
    (hfield : IsBinaryFieldInvolution (involutionAction h hr)) :
    (⨆ (j : G) (_ : j ∈ involutionResidual L r) (_ : orderOf j = 2),
      L ⊓ involutionCentralizer j) = L := by
  rw [involutionResidual_eq_centralizer_of_binaryField h hr hfield]
  obtain ⟨n, hn, e, σ, hσ, he⟩ := hfield
  exact centralizers_generate_of_fixed_model h hr e (Theory.PSL2.fieldAut σ) he
    (Theory.PSL2.field_fixed_centralizers_generate σ)

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual
