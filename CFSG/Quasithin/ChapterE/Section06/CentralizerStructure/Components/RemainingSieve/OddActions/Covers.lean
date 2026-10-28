module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceInputs
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Covers
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore

/-!
# The M₁₁ cover reduction in E.6.8

Quasisimplicity makes O₂(L) central. Applying the universal trivial-kernel
bound for M₁₁ to the literal map L → L/O₂(L) ≃ M₁₁ removes that kernel and
constructs an isomorphism of L itself with M₁₁.

The multiplier bound remains an explicit input here. It is owned by the
Mathieu multiplier development; these conditional deductions do not establish
that bound or the completed E.6.8 sporadic branch.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, I.1.3,
printed p.407, 1.1.5(3)(f), p.502, and E.6.8(5), p.248.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.OddActions
open Chapter1.XiEmbedding.InvariantThree.SporadicRemaining
universe u
variable {X : Type u} [Group X] [Finite X] [IsQuasisimple X]

/-- A trivial universal central-kernel bound removes the actual two-core. -/
theorem m11_core_eq_bot_of_multiplier
    (hbound : CentralKernelDivides.{u,0} Sporadic.Mathieu.M11 1)
    (e : (X ⧸ pCore 2 X) ≃* Sporadic.Mathieu.M11) : pCore 2 X = ⊥ := by
  let f : X →* Sporadic.Mathieu.M11 := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  have hk : f.ker = pCore 2 X := by
    ext x
    change e (QuotientGroup.mk' (pCore 2 X) x) = 1 ↔ x ∈ pCore 2 X
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hd := hbound X f (e.surjective.comp (QuotientGroup.mk'_surjective _))
    (hk.trans_le (IsQuasisimple.pCore_le_center 2))
  rw [hk] at hd
  exact (pCore 2 X).eq_bot_of_card_eq (Nat.dvd_one.mp hd)

/-- Once the core is removed, the source quotient identifies the group itself. -/
theorem m11_model_of_multiplier
    (hbound : CentralKernelDivides.{u,0} Sporadic.Mathieu.M11 1)
    (e : (X ⧸ pCore 2 X) ≃* Sporadic.Mathieu.M11) :
    Nonempty (X ≃* Sporadic.Mathieu.M11) := by
  have hk := m11_core_eq_bot_of_multiplier hbound e
  exact ⟨(QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hk.symm)).trans e⟩

variable {G : Type u} [Group G] [Finite G] {U L : Subgroup G}

/-- Apply the cover reduction to a component with relative subnormality in C_G(U). -/
theorem component_m11_model_of_multiplier
    (hbound : CentralKernelDivides.{u,0} Sporadic.Mathieu.M11 1)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : Nonempty ((L ⧸ pCore 2 L) ≃* Sporadic.Mathieu.M11)) :
    Nonempty (L ≃* Sporadic.Mathieu.M11) := by
  let _ := hL.2.2
  let _ := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hL.1)
  obtain ⟨e⟩ := hm
  exact m11_model_of_multiplier hbound e

end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve.OddActions
