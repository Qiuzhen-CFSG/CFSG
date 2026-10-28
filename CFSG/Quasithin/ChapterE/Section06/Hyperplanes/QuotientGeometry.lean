module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Preliminaries
public import Theory.GroupTheory.Signalizer.Defs


/-!
# The actual quotient and actor in E.6.20

For U₀ ≤ V, put H₀ = C_G(U₀). The subgroup U₀ is central in H₀, and
its quotient image V* is multiplicatively equivalent to V/U₀. We construct
the quotient, the image, that equivalence, and the conjugation action of V*
on H₀/U₀. In corank three V* is elementary abelian of order eight, exactly
the actor required by the solvable signalizer theorem. The action is supplied
as a named instance value, so later arguments retain this specific action.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the construction
in the proof of E.6.20, printed pp.252–253 (PDF pp.263–264). This module is
quotient geometry, not a claim that the odd-core signalizer has been balanced
or that the global odd core has vanished.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes
variable {G : Type*} [Group G] (V U₀ : Subgroup G)

def quotientKernel : Subgroup (centralizer (U₀ : Set G)) :=
  U₀.subgroupOf (centralizer (U₀ : Set G))

theorem quotientKernel_le_center : quotientKernel U₀ ≤ center (centralizer (U₀ : Set G)) := by
  intro u hu
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (x.property u.val hu).symm

instance quotientKernel_normal : (quotientKernel U₀).Normal where
  conj_mem u hu x := by
    have hc := mem_center_iff.mp (quotientKernel_le_center U₀ hu) x
    simpa only [hc, mul_inv_cancel_right] using hu

abbrev CentralizerQuotient := centralizer (U₀ : Set G) ⧸ quotientKernel U₀

def quotientActor : Subgroup (CentralizerQuotient U₀) :=
  (V.subgroupOf (centralizer (U₀ : Set G))).map (QuotientGroup.mk' (quotientKernel U₀))

@[reducible] def quotientAction : MulDistribMulAction (quotientActor V U₀) (CentralizerQuotient U₀) :=
  MulDistribMulAction.compHom (CentralizerQuotient U₀)
    (MulAut.conj.comp (quotientActor V U₀).subtype)

theorem quotientAction_smul (a : quotientActor V U₀) (x : CentralizerQuotient U₀) :
    (quotientAction V U₀).smul a x = (a : CentralizerQuotient U₀) * x * (a : CentralizerQuotient U₀)⁻¹ := rfl

variable [IsElementaryAbelian 2 V]

/-- Under the source containment, the quotient kernel is exactly U₀, embedded in G. -/
theorem quotientKernel_map (hU : U₀ ≤ V) :
    (quotientKernel U₀).map (centralizer (U₀ : Set G)).subtype = U₀ :=
  Subgroup.map_subgroupOf_eq_of_le
    (hU.trans (V.le_centralizer.trans (Subgroup.centralizer_le hU)))

/-- The central kernel in E.6.20 is a two-group. -/
theorem quotientKernel_isPGroup (hU : U₀ ≤ V) : IsPGroup 2 (quotientKernel U₀) :=
  ((IsElementaryAbelian.isPGroup 2 V).to_le hU).comap_subtype

def quotientActorMap (hU : U₀ ≤ V) : V →* CentralizerQuotient U₀ :=
  (QuotientGroup.mk' (quotientKernel U₀)).comp
    (inclusion (V.le_centralizer.trans (Subgroup.centralizer_le hU)))

theorem quotientActorMap_ker (hU : U₀ ≤ V) :
    (quotientActorMap V U₀ hU).ker = U₀.subgroupOf V := by
  ext v
  change QuotientGroup.mk' (quotientKernel U₀) _ = 1 ↔ (v : G) ∈ U₀
  exact QuotientGroup.eq_one_iff _

theorem quotientActorMap_range (hU : U₀ ≤ V) :
    (quotientActorMap V U₀ hU).range = quotientActor V U₀ := by
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨⟨v, V.le_centralizer.trans (Subgroup.centralizer_le hU) v.property⟩,
      v.property, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

noncomputable def quotientActorEquiv (hU : U₀ ≤ V) :
    (V ⧸ U₀.subgroupOf V) ≃* quotientActor V U₀ :=
  (QuotientGroup.quotientMulEquivOfEq (quotientActorMap_ker V U₀ hU).symm).trans
    ((QuotientGroup.quotientKerEquivRange (quotientActorMap V U₀ hU)).trans
      (MulEquiv.subgroupCongr (quotientActorMap_range V U₀ hU)))

theorem quotientActor_elementary (hU : U₀ ≤ V) :
    IsElementaryAbelian 2 (quotientActor V U₀) :=
  IsElementaryAbelian.of_surjective (quotientActorEquiv V U₀ hU).toMonoidHom
    (quotientActorEquiv V U₀ hU).surjective

theorem quotientActor_card [Finite G] (hU : U₀ ≤ V) :
    Nat.card (quotientActor V U₀) = 2 ^ subgroupCorank V U₀ := by
  rw [← Nat.card_congr (quotientActorEquiv V U₀ hU).toEquiv]
  change U₀.relIndex V = _
  rw [subgroupCorank_eq_quotient_finrank]
  exact Subgroup.relIndex_eq_two_pow_quotient_finrank V U₀

theorem quotientActor_card_eight [Finite G] (hU : U₀ ≤ V)
    (hc : subgroupCorank V U₀ = 3) : Nat.card (quotientActor V U₀) = 8 := by
  rw [quotientActor_card V U₀ hU, hc]
  norm_num

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes
