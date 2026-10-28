module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.ExchangedModel.ActionModel
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.ExchangedModel.OriginalAction
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.ExchangedModel.JointCore
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Actions.MovedInterval
public import Theory.Representation.OrthogonalFourPlusMatrix.InvolutionResidual.Swapping

/-!
# The exchanged moved section and the symmetric lift

The common core gives moved cardinality greater than four. The literal
residual image is nonsolvable and commutes with z; the order-five matrix
calculation then gives moved order sixteen and irreducibility. Transporting
these conclusions through the actual quotient maps proves the invariant
interval and applies symmetric_lift_of_exchanged_moved_section.

Consequently Uˣ normalizes D and C_D(Uˣ)=⟨zˣ⟩. The earlier case-(3)
and original diagonal-action markings remain explicit source inputs.
The component-interchange assertion is separate: the stronger moved-space
theorem allows this symmetric-lift deduction without assuming interchange.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ExchangedModel
open ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G]

namespace CaseThreeAction
variable {H U : Subgroup G} (m : CaseThreeAction H U)

/-- Rank four and irreducibility for the actual central-quotient commutator.
The original common residual, rather than an independently chosen A₅, acts. -/
theorem moved_section [Finite G] [IsExtraspecial 2 U]
    (a : H) (ha : orderOf (a:G) = 2)
    (C : Subgroup G) (hCH : C ≤ H) (hCa : C ≤ centralizer ({(a:G)} : Set G))
    (hn : ¬ Group.IsSolvable (pResidual 2 C))
    (hr : 4 < Nat.card (((⁅U,zpowers (a:G)⁆).subgroupOf U).map
      (QuotientGroup.mk' (center U)))) :
    Nat.card (((⁅U,zpowers (a:G)⁆).subgroupOf U).map (QuotientGroup.mk' (center U))) = 16 ∧
    ∀ F : Subgroup (U ⧸ center U),
      F ≤ ((⁅U,zpowers (a:G)⁆).subgroupOf U).map (QuotientGroup.mk' (center U)) →
      (∀ c : pResidual 2 C, ∀ v ∈ F, m.quotientAction (inclusion hCH c) v ∈ F) →
      F = ⊥ ∨ F = ((⁅U,zpowers (a:G)⁆).subgroupOf U).map (QuotientGroup.mk' (center U)) := by
  let f := m.residualMap C hCH
  let R := f.range
  let t := m.action a
  let W := ((⁅U,zpowers (a:G)⁆).subgroupOf U).map (QuotientGroup.mk' (center U))
  have ht : t ^ 2 = 1 := by
    have ha2 : a ^ 2 = 1 := Subtype.ext (ha ▸ pow_orderOf_eq_one (a:G))
    change (m.action a) ^ 2 = 1
    rw [← map_pow, ha2, map_one]
  have hc : ∀ r : R, Commute t (Binary.linearAction (r : Binary.G)) := by
    intro r
    obtain ⟨c,hc⟩ := r.property
    have hcomm : Commute a (inclusion hCH (c : C)) := by
      apply Subtype.ext
      exact (mem_centralizer_singleton_iff.mp (hCa c.val.property)).symm
    change Commute (m.action a) (Binary.linearAction r.val)
    rw [← hc, m.residualMap_spec]
    exact hcomm.map m.action
  have he : Nat.card (LinearMap.range (t.toLinearMap - LinearMap.id)) = Nat.card W := by
    rw [← m.subspace_moved a ha]
    exact m.subspace_card W
  obtain ⟨hd,hi⟩ := Binary.InvolutionResidual.Swapping.moved_finrank_and_irreducible t ht R
    (m.residualMap_nonsolvable C hCH hn) hc
    ((Binary.InvolutionResidual.Swapping.four_lt_moved_card_iff t).mp (he ▸ hr))
  refine ⟨?_, ?_⟩
  · rw [← he, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    norm_num
  · intro F hF hFstable
    have hle : m.subspace F ≤ LinearMap.range (t.toLinearMap - LinearMap.id) := by
      rw [← m.subspace_moved a ha]
      exact m.subspace_mono hF
    have hstable : ∀ (r : R) (v : Binary.V), v ∈ m.subspace F →
        Binary.action (r : Binary.G) v ∈ m.subspace F := by
      intro r v hv
      obtain ⟨c,hc⟩ := r.property
      have hlin : Binary.linearAction r.val = m.action (inclusion hCH (c:C)) := by
        rw [← hc]
        exact m.residualMap_spec C hCH c
      change Binary.linearAction r.val v ∈ m.subspace F
      rw [hlin]
      exact m.subspace_invariant F _ (hFstable c) v hv
    rcases hi (m.subspace F) hle hstable with hbot | htop
    · exact Or.inl (m.subspace_injective (hbot.trans m.subspace_bot.symm))
    · exact Or.inr (m.subspace_injective (htop.trans (m.subspace_moved a ha).symm))

end CaseThreeAction

/-- The common residual is the original literal diagonal residual. -/
private theorem residual_nonsolvable_of_diagonal (z i : G)
    (hn : ¬ Group.IsSolvable (diagonalResidual (centralizer ({z}:Set G)) i)) :
    ¬ Group.IsSolvable (pResidual 2 (centralizer ({z}:Set G) ⊓ centralizer ({i}:Set G) : Subgroup G)) := by
  intro hs
  let _ := hs
  let C := centralizer ({z}:Set G) ⊓ centralizer ({i}:Set G)
  let e := (pResidual 2 C).equivMapOfInjective C.subtype C.subtype_injective
  exact hn (Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective)

/-- Source case (3), the common core, and the original nonsolvable K₀ give
both premises of the symmetric elementary-lift theorem. -/
theorem exchanged_moved_section [Finite G]
    (U : Subgroup G) [IsExtraspecial 2 U] (z x : G)
    (hz : orderOf z = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hUcard : Nat.card U = 512)
    (hiz : conjugateElement z x ∈ centralizer ({z} : Set G))
    (hDcard : Nat.card (centralizerLift U z (conjugateElement z x)) = 64)
    (hDcore : (centralizer ({z} : Set G) ⊓
      centralizer ({conjugateElement z x} : Set G)).pCoreIn 2 =
        centralizerLift U z (conjugateElement z x))
    (m : CaseThreeAction (centralizer ({conjugateElement z x}:Set G)) (conjugateCore U x))
    (hn : ¬ Group.IsSolvable
      (diagonalResidual (centralizer ({z}:Set G)) (conjugateElement z x))) :
    Nat.card (((⁅conjugateCore U x,zpowers z⁆).subgroupOf (conjugateCore U x)).map
      (QuotientGroup.mk' (center (conjugateCore U x)))) = 16 ∧
    ∀ E : Subgroup G, zpowers (conjugateElement z x) ≤ E →
      E ≤ liftBase (conjugateCore U x) (conjugateElement z x) z →
      diagonalResidual (centralizer ({z}:Set G)) (conjugateElement z x) ≤
        normalizer (E:Set G) →
      E = zpowers (conjugateElement z x) ∨
        E = liftBase (conjugateCore U x) (conjugateElement z x) z := by
  let V := conjugateCore U x
  let i := conjugateElement z x
  let C := centralizer ({z}:Set G) ⊓ centralizer ({i}:Set G)
  let K := diagonalResidual (centralizer ({z}:Set G)) i
  let e := U.equivMapOfInjective (MulAut.conj x⁻¹).toMonoidHom (MulAut.conj x⁻¹).injective
  let _ : IsExtraspecial 2 V := IsExtraspecial.of_mulEquiv e inferInstance
  have hzH : z ∈ centralizer ({i}:Set G) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hiz).symm
  let a : centralizer ({i}:Set G) := ⟨z,hzH⟩
  have hKC : K ≤ C := map_subtype_le _
  have hKH : K ≤ centralizer ({i}:Set G) := hKC.trans inf_le_right
  have hr := exchanged_moved_card_gt_four U z x hUcore hUcard hiz hDcard hDcore
  obtain ⟨hmoved,hirr⟩ := m.moved_section a hz C inf_le_right inf_le_left
    (residual_nonsolvable_of_diagonal z i hn) hr
  refine ⟨hmoved, ?_⟩
  let ρ := m.quotientAction.comp (inclusion hKH)
  apply liftBase_invariant_interval_of_moved_image V K i z (conjugateCore_center U z x hZ)
    (m.normalizes hzH) (hKH.trans m.normalizes) hmoved ρ
  · intro k u
    exact m.quotientAction_apply (inclusion hKH k) u
  · intro F hF hstable
    apply hirr F hF
    intro c v hv
    let k : K := ⟨(c:C), mem_map_of_mem C.subtype c.property⟩
    exact hstable k v hv

/-- Application to the actual common lift. No normalization or fixed-line
conclusion, nor either moved-section conclusion, is assumed. -/
theorem symmetric_lift [Finite G]
    (U : Subgroup G) [IsExtraspecial 2 U] (z x : G)
    (hz : orderOf z = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hUcard : Nat.card U = 512)
    (hiz : conjugateElement z x ∈ centralizer ({z} : Set G))
    (hDcard : Nat.card (centralizerLift U z (conjugateElement z x)) = 64)
    (hDcore : (centralizer ({z} : Set G) ⊓
      centralizer ({conjugateElement z x} : Set G)).pCoreIn 2 =
        centralizerLift U z (conjugateElement z x))
    (m : CaseThreeAction (centralizer ({conjugateElement z x}:Set G)) (conjugateCore U x))
    (hn : ¬ Group.IsSolvable
      (diagonalResidual (centralizer ({z}:Set G)) (conjugateElement z x))) :
    centralizerLift (conjugateCore U x) (conjugateElement z x) z =
      centralizerLift U z (conjugateElement z x) ∧
    conjugateCore U x ≤ normalizer (centralizerLift U z (conjugateElement z x):Set G) ∧
    centralizerLift U z (conjugateElement z x) ⊓ centralizer (conjugateCore U x:Set G) =
      zpowers (conjugateElement z x) := by
  obtain ⟨hm,hi⟩ := exchanged_moved_section U z x hz hZ hUcore hUcard hiz hDcard hDcore m hn
  exact symmetric_lift_of_exchanged_moved_section U z x hz hZ hUcore hiz hDcard hDcore hm hi

/-- The source-facing symmetric lift, with nonsolvability discharged by the
original marked A₅ quotient. The coordinate inputs are earlier case-(3) and
selection data; all exchanged moved-section conclusions are proved here. -/
theorem symmetric_lift_of_marked_actions [Finite G]
    (U : Subgroup G) [IsExtraspecial 2 U] (z x : G)
    (hz : orderOf z = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hUcard : Nat.card U = 512)
    (hiz : conjugateElement z x ∈ centralizer ({z} : Set G))
    (hDcard : Nat.card (centralizerLift U z (conjugateElement z x)) = 64)
    (hDcore : (centralizer ({z} : Set G) ⊓
      centralizer ({conjugateElement z x} : Set G)).pCoreIn 2 =
        centralizerLift U z (conjugateElement z x))
    (m : CaseThreeAction (centralizer ({conjugateElement z x}:Set G)) (conjugateCore U x))
    (d : OriginalMovedAction U z (conjugateElement z x)) :
    centralizerLift (conjugateCore U x) (conjugateElement z x) z =
      centralizerLift U z (conjugateElement z x) ∧
    conjugateCore U x ≤ normalizer (centralizerLift U z (conjugateElement z x):Set G) ∧
    centralizerLift U z (conjugateElement z x) ⊓ centralizer (conjugateCore U x:Set G) =
      zpowers (conjugateElement z x) :=
  symmetric_lift U z x hz hZ hUcore hUcard hiz hDcard hDcore m d.nonsolvable

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ExchangedModel
