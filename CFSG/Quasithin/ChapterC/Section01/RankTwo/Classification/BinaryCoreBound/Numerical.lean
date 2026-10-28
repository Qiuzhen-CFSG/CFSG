module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Head

/-!
# Numerical assembly from binary elementary core models

For the actual commutator core D = [O₂(J), L], the remaining local rigidity
argument can be separated into two independent branches: elementary models
of dimensions 3, 4, or 6 when D is abelian, and elementary models of dimensions
3 or 5 for Z(D) when D is nonabelian. Cardinality of the actual model carriers
then gives the required numerical disjunction.

This module proves only that conditional arithmetic assembly. The two model
hypotheses are not proved here and are not part of `BinaryMS.Input`. They must
be discharged from the genuine MS conditions before exporting the source
bound. In particular, an FF-module on Ω₁Z(O₂(J)) does not supply either model.

Source motivation: the n = 1 alternatives in Aschbacher–Smith C.1.34,
combined manuscript (1 March 2004), printed pp.136–137.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS
open Subgroup
universe u
variable {J : Type u} [Group J] [Finite J]

private theorem card_of_elementary_model {K : Type*} [Group K] {d : ℕ}
    (he : Nonempty (K ≃* Multiplicative (Fin d → ZMod 2))) : Nat.card K = 2 ^ d := by
  obtain ⟨e⟩ := he
  rw [Nat.card_congr e.toEquiv]
  change Nat.card (Fin d → ZMod 2) = _
  simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]

/-- Conditional numerical assembly from actual group isomorphisms in each
commutativity branch. This does not assert either branch's local rigidity. -/
theorem commutatorCore_bound_of_elementary_models (L : Subgroup J)
    (habel : IsMulCommutative (commutatorCore L) →
      ∃ d : ℕ, (d = 3 ∨ d = 4 ∨ d = 6) ∧
        Nonempty (commutatorCore L ≃* Multiplicative (Fin d → ZMod 2)))
    (hnonabel : ¬ IsMulCommutative (commutatorCore L) →
      ∃ d : ℕ, (d = 3 ∨ d = 5) ∧
        Nonempty (center (commutatorCore L) ≃* Multiplicative (Fin d → ZMod 2))) :
    Nat.card (center (commutatorCore L)) ≤ 32 ∨ Nat.card (commutatorCore L) = 64 := by
  classical
  by_cases hc : IsMulCommutative (commutatorCore L)
  · obtain ⟨d, hd, he⟩ := habel hc
    have hn := card_of_elementary_model he
    have hz : Nat.card (center (commutatorCore L)) ≤ Nat.card (commutatorCore L) :=
      Nat.card_le_card_of_injective _ (center (commutatorCore L)).subtype_injective
    rcases hd with rfl | rfl | rfl
    · left; norm_num at hn; omega
    · left; norm_num at hn; omega
    · right; norm_num at hn; exact hn
  · obtain ⟨d, hd, he⟩ := hnonabel hc
    have hn := card_of_elementary_model he
    left
    rcases hd with rfl | rfl <;> norm_num at hn ⊢ <;> omega

end CFSG.Quasithin.ChapterC.BinaryMS
