module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Action
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.InvolutionLifting
public import Theory.SpecificGroups.PSL3Two.InvolutionConjugacy
public import Theory.GroupTheory.PCoreImage

/-!
# The lifted involution and quotient fusion in the HS normalizer

The earlier residual-image equality transports O₂(O²(C_K(u))) through the
central two-kernel. A two-central model witness in that core and outside the
model normalizer core consequently lifts to an involution j in the actual
core, with involutory images in both M/Q and M/E.

The actual SL₃(2) quotient has one involution class, so its conjugators lift
to M. Combining this with fixed-displacement coset fusion sends every
involution of M outside Q into the original centralizer core by K-conjugacy.
The linear displacement premise is discharged in the parent Nonsplit module.

Source: Aschbacher–Smith I.2.2(5), final HS paragraph, printed p.412 / PDF p.423.
-/

@[expose] public section

open scoped IsMulCommutative
open Subgroup
namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Nonsplit
open Sporadic.LeechRelated.HS.BlockNormalizer
open Theory.GroupTheory.DoubleCoverCentralizer
variable {K : Type*} [Group K] [Finite K]

omit [Finite K] in
theorem E_le_Q (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier) : E e ≤ Q e := by
  rintro _ ⟨q, _, rfl⟩
  exact q.property

omit [Finite K] in
theorem order_two_mod_core
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (j : M e) (hj : j ^ 2 = 1) (hjQ : j ∉ Q e) :
    orderOf (QuotientGroup.mk' (Q e) j) = 2 ∧
      orderOf (QuotientGroup.mk' (E e) j) = 2 := by
  constructor
  · apply orderOf_eq_prime (by rw [← map_pow, hj, map_one])
    exact fun h => hjQ ((QuotientGroup.eq_one_iff j).mp h)
  · apply orderOf_eq_prime (by rw [← map_pow, hj, map_one])
    exact fun h => hjQ (E_le_Q e ((QuotientGroup.eq_one_iff j).mp h))

/-- The earlier residual-image equality transports the actual two-core;
no separate surjectivity assumption on R is needed. -/
theorem core_map_of_residual_map
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (hX : (Theory.GroupTheory.centralizerTwoResidual u).map (modelMap e) =
      Theory.GroupTheory.centralizerTwoResidual (modelMap e u)) :
    (centralizerCore u).map (modelMap e) = centralizerCore (modelMap e u) := by
  have hk : IsPGroup 2 (modelMap e).ker := IsPGroup.of_card (n := 1)
    (by rw [modelMap_ker, hZ, pow_one])
  change ((Theory.GroupTheory.centralizerTwoResidual u).pCoreIn 2).map (modelMap e) =
    (Theory.GroupTheory.centralizerTwoResidual (modelMap e u)).pCoreIn 2
  rw [map_pCoreIn_of_ker_isPGroup _ hk, hX]

/-- Lift the model witness through the actual centralizer-core image. Its
order comes from two-central lifting; its position outside Q comes from
core-preimage equality, not from a noncentral-lifting assumption. -/
theorem exists_core_involution
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (hXmap : (Theory.GroupTheory.centralizerTwoResidual u).map (modelMap e) =
      Theory.GroupTheory.centralizerTwoResidual (modelMap e u))
    (j₀ : baseNormalizer) (hj₀ : orderOf j₀ = 2)
    (hj₀c : TwoCentral (j₀ : Sporadic.LeechRelated.HS.Carrier))
    (hj₀R : (j₀ : Sporadic.LeechRelated.HS.Carrier) ∈ centralizerCore (modelMap e u))
    (hj₀Q : j₀ ∉ pCore 2 baseNormalizer) :
    ∃ j : M e, (j : K) ∈ centralizerCore u ∧ orderOf j = 2 ∧
      localMap e j = j₀ ∧ j ∉ Q e ∧
      orderOf (QuotientGroup.mk' (Q e) j) = 2 ∧
      orderOf (QuotientGroup.mk' (E e) j) = 2 := by
  have hRmap := core_map_of_residual_map e hZ u hXmap
  obtain ⟨j, hjR, hjimage⟩ := hRmap.symm ▸ hj₀R
  have hjM : j ∈ M e := by
    change modelMap e j ∈ baseNormalizer
    rw [hjimage]
    exact j₀.property
  let jM : M e := ⟨j, hjM⟩
  have hj2 : orderOf jM = 2 := by
    rw [← Subgroup.orderOf_coe jM]
    exact order_two_of_twoCentral_image e hZ j
      (by rw [hjimage, Subgroup.orderOf_coe, hj₀]) (hjimage.symm ▸ hj₀c)
  have hjlocal : localMap e jM = j₀ := Subtype.ext hjimage
  have hjQ : jM ∉ Q e := by
    rw [Q_eq_model_core_preimage e hZ]
    change localMap e jM ∉ pCore 2 baseNormalizer
    rwa [hjlocal]
  exact ⟨jM, hjR, hj2, hjlocal, hjQ,
    order_two_mod_core e jM (by simpa only [hj2] using pow_orderOf_eq_one jM) hjQ⟩

/-- The unique involution class in the actual quotient, with its conjugator
lifted to M. No model-class fusion premise is needed. -/
theorem quotient_involutions_conjugate
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2)
    (a b : M e ⧸ Q e) (ha : orderOf a = 2) (hb : orderOf b = 2) :
    ∃ m : M e, QuotientGroup.mk' (Q e) m * a *
      (QuotientGroup.mk' (Q e) m)⁻¹ = b := by
  let f := (normalizerQuotientEquiv e hZ).trans Matrix.PSL3Two.equiv
  have hc := Matrix.PSL3Two.isConj_of_orderOf_eq_two (f a) (f b)
    ((f.orderOf_eq a).trans ha) ((f.orderOf_eq b).trans hb)
  have hab : IsConj a b := by
    simpa only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using
      f.symm.toMonoidHom.map_isConj hc
  obtain ⟨m, hm⟩ := isConj_iff.mp hab
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Q e) m
  exact ⟨m, hm⟩

/-- Extend the one-coset fusion theorem to every involution outside Q. -/
theorem conjugate_into_core_of_displacement
    (e : (K ⧸ center K) ≃* Sporadic.LeechRelated.HS.Carrier)
    (hZ : Nat.card (center K) = 2) (u : K)
    (j : M e) (hjR : (j : K) ∈ centralizerCore u)
    (hjQ : orderOf (QuotientGroup.mk' (Q e) j) = 2)
    (hjE : orderOf (QuotientGroup.mk' (E e) j) = 2)
    (hER : E e ≤ (centralizerCore u).subgroupOf (M e))
    (hfixed : ∀ v : Additive (Qbar e),
      frattiniRepresentation e (QuotientGroup.mk' (Q e) j) v = v →
      ∃ w : Additive (Qbar e),
        frattiniRepresentation e (QuotientGroup.mk' (Q e) j) w - w = v)
    (x : M e) (hx : x ^ 2 = 1) (hxQ : x ∉ Q e) :
    ∃ y ∈ centralizerCore u, IsConj (x : K) y := by
  have hx2 := (order_two_mod_core e x hx hxQ).1
  obtain ⟨m, hm⟩ := quotient_involutions_conjugate e hZ _ _ hx2 hjQ
  let a : M e := m * x * m⁻¹
  have ha2 : a ^ 2 = 1 := by
    change (MulAut.conj m x) ^ 2 = 1
    rw [← map_pow, hx, map_one]
  have hacoset : QuotientGroup.mk' (Q e) a = QuotientGroup.mk' (Q e) j := by
    simpa only [a, map_mul, map_inv] using hm
  obtain ⟨y, hy, hay⟩ := conjugate_into_centralizerCore e u j hjR hER hjE
    (fixed_le_commutator_of_frattini_displacement e j hfixed) a ha2 hacoset
  refine ⟨y, hy, IsConj.trans ?_ hay⟩
  exact isConj_iff.mpr ⟨(m : K), rfl⟩
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Nonsplit
