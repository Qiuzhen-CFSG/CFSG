module

public import Theory.GroupTheory.PerfectCentralCoverFixedResidual
public import Theory.SpecificGroups.SymmetricEight.CentralPairResidual
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Two-central fixed residuals in central covers of A₈

Sylow conjugacy carries the original two-central involution to the four
pair interchanges. The two-residual of its centralizer has a two-core of
order 32. Residual surjectivity through a perfect central two-cover
therefore forces 32 to divide the original fixed residual order.
This excludes an order dividing 48, including nonsplit central covers.

Application: RecognitionFixedResidual eliminates the literal PSL₄(2) row
using the proved exceptional A₈ equivalence.
Source: Aschbacher--Smith 14.3.22, printed p.999, model inspection.
-/

public section
open Subgroup
namespace AlternatingEight
open Theory.GroupTheory.DoubleCoverCentralizer
open Theory.SpecificGroups.SymmetricEight.CentralPair
open PerfectCentralCovering

theorem thirtyTwo_dvd_twoCentral_fixedResidual (t : alternatingGroup (Fin 8))
    (ht : orderOf t = 2) (hc : TwoCentral t) :
    32 ∣ Nat.card (pResidual 2 (centralizer ({t} : Set (alternatingGroup (Fin 8))))) := by
  obtain ⟨P,hP,hZ⟩ := hc
  obtain ⟨g,hg⟩ := central_in_sylow_conjugate P t hP (by
    intro he; simp [he] at ht) (by
      intro x hx
      exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_center_iff.mp hZ ⟨x,hx⟩)))
  let e := Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv
    (MulAut.conj g) z
  have hd := (pCore 2 (pResidual 2
    (Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.pairStabilizer.subgroupOf
      (alternatingGroup (Fin 8))))).card_subgroup_dvd_card
  rw [residual_twoCore_card, ←centralizer_z] at hd
  have hr : Nat.card (pResidual 2 (centralizer ({z} : Set A8))) =
      Nat.card (pResidual 2 (centralizer ({(MulAut.conj g) z} : Set A8))) := by
    rw [←map_pResidual 2 e,card_map_of_injective e.injective]
  rw [←hg,←hr]
  exact hd

variable {E : Type*} [Group E] [Finite E]
theorem no_eight_cover_of_small_fixedResidual (f : Cover E (alternatingGroup (Fin 8)))
    (hk : f.toMonoidHom.ker = center E) (hp : IsPGroup 2 f.toMonoidHom.ker)
    (α : MulAut E) (hα : orderOf α = 2)
    (hi : ∃ x, α = MulAut.conj x) (P : Sylow 2 E)
    (hfix : ∀ x : P, α (x : E) = x)
    (hsmall : Nat.card (pResidual 2 α.fixedSubgroup) ∣ 48) : False := by
  let := f.isPerfect
  let : Group.IsPerfect (alternatingGroup (Fin 8)) := Group.IsPerfect.ofSurjective f.surjective
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by norm_num)
  obtain ⟨t,ht,hc,hd⟩ := f.exists_twoCentral_fixedResidual_dvd hk hp
    center_eq_bot_of_simple_perfect α hα hi P hfix
  exact (by decide : ¬32 ∣ 48)
    ((thirtyTwo_dvd_twoCentral_fixedResidual t ht hc).trans (hd.trans hsmall))
end AlternatingEight
