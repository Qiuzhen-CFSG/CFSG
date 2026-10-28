module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.NonabelianCenter.Layers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.CentralModule
public import Theory.GroupTheory.PerfectSmallTwoAction

/-!
# A lower bound for the intrinsic moving omega-center

Put V = Ω₁Z(O₂(J)), D = [O₂(J),L], and W = Ω₁Z(D), with the
omega-centers embedded in J by their actual subtype maps. Normality gives
[V,L] ≤ V ∩ D ≤ W. If L centralizes W, the three-subgroups lemma and
perfectness force L to centralize V, contrary to MS3. Thus [W,L] is
nontrivial, and the perfect-action bound gives |[W,L]| ≥ 8.

This works without assuming D nonabelian. It supplies only the lower bound:
MS3-driven upper control and the index-one-or-four conclusion remain open.
In particular, no identification of W with V is made.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.31(MS3)
and the intrinsic core in C.1.34, printed pp.135–137.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS
open Subgroup Stellmacher
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R)
include h

/-- The moving part of Ω₁Z(O₂(J)) lies in the actual Ω₁Z([O₂(J),L]). -/
theorem Input.centralMoving_le_coreCenterOmega :
    ⁅centralModule J, L⁆ ≤ omegaOneCenterAmbient (commutatorCore L) := by
  let := centralModule_normal J
  let := h.component_normal
  have hVN : centralModule J ≤ pCore 2 J := fun v hv => (mem_centralModule J v).mp hv |>.1
  have hDN : commutatorCore L ≤ pCore 2 J := commutator_le_left _ _
  intro v hv
  have hvV := commutator_le_left (centralModule J) L hv
  obtain ⟨_, hv2, hvc⟩ := (mem_centralModule J v).mp hvV
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨commutator_mono hVN le_rfl hv, hv2, fun d hd => hvc d (hDN hd)⟩

/-- MS3 and perfectness force nontrivial action on the intrinsic omega-center. -/
theorem Input.coreCenterOmega_commutator_ne_bot :
    ⁅omegaOneCenterAmbient (commutatorCore L), L⁆ ≠ ⊥ := by
  let := h.component.perfect
  intro hz
  have hs : ⁅⁅centralModule J, L⁆, L⁆ = ⊥ := le_bot_iff.mp
    (hz ▸ commutator_mono h.centralMoving_le_coreCenterOmega (le_refl L))
  have hs' : ⁅⁅L, centralModule J⁆, L⁆ = ⊥ := by
    rwa [commutator_comm L (centralModule J)]
  have hh : ⁅⁅L, L⁆, centralModule J⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate hs' hs
  rw [commutator_eq_self] at hh
  exact h.component_not_centralizes (commutator_eq_bot_iff_le_centralizer.mp hh)

/-- The intrinsic moving omega-center has at least eight elements. The
reverse bound and the relative-index alternative are not asserted. -/
theorem Input.coreCenterOmega_commutator_card_ge_eight :
    8 ≤ Nat.card (⁅omegaOneCenterAmbient (commutatorCore L), L⁆ : Subgroup J) := by
  let := h.component.perfect
  let := h.component_normal
  let := h.coreCenterOmega_ambient_normal
  apply commutator_card_ge_eight_of_isPerfect L
    (omegaOneCenterAmbient (commutatorCore L)) _ h.coreCenterOmega_commutator_ne_bot
  let := omegaOneCenterAmbient_elementaryAbelian (commutatorCore L)
  exact IsElementaryAbelian.isPGroup 2 _

end CFSG.Quasithin.ChapterC.BinaryMS
