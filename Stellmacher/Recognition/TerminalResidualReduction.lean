module

public import Stellmacher.Recognition.SylowSpectrum
public import Stellmacher.Recognition.SemidihedralRecognition
public import Stellmacher.Recognition.Sylow32Exclusion
public import Stellmacher.Recognition.GTwoSixtyFourExclusion

/-!
# The remaining unconditional simple N₂ recognition alternatives

A finite nonsolvable simple N₂ group is already a catalogue model, has the
actual G₂ local type with its supplied Sylow of order 32, has the actual
`LargeTerminalContext` with that Sylow of order 2048 or 4096, or has an
involution whose full centralizer has nontrivial odd core. Both unresolved
local branches retain trivial odd cores in every two-local subgroup. The
large context retains its original embeddings and all its local hypotheses.

Starting from `simple_nTwo_terminal_reduction`, recognize the semidihedral
branch using its retained odd-core hypotheses and exclude the maximal
C₂ × S₄ order-32 branch by transfer. The G₂ Sylow spectrum and the completed
order-64 exclusion leave order 32. The large-context spectrum is the proved
2048/4096 disjunction; no endpoint is discarded here.

The remaining public consumer contracts are as follows. In each contract,
`G` is a group with `[Finite G] [IsSimpleGroup G]`,
`hns : ¬ Group.IsSolvable G`, and `hN : IsNTwoGroup G`.
Write `hcore : ∀ U : Subgroup G, IsTwoLocal U → pPrimeCore 2 U = ⊥`.

* `ng-gtwo-card32-recognition`: given `hcore`,
  `hType : IsOfGTwoTwoDerivedType G`, `S : Sylow 2 G`, and
  `hcard : Nat.card S = 32`, prove `ABG.IsPSU3 G 3` (an actual model
  isomorphism). This enters the catalogue by `IsNGroupModel.unitaryThree`.
* `ng-large-sylow-2048`: given `hcore`, `S : Sylow 2 G`, and
  `ctx : LargeTerminalContext S`, prove `Nat.card S = 2048`.
  The existing `LargeTerminalContext.parrott_hypotheses_of_sylow_card`
  then supplies `∃ z : G, Subgroup.zpowers z =
  omegaOneCenter (S : Subgroup G) ∧ ParrottCentralizerHypotheses z`.
  `ng-parrott-tits-recognition` takes such a `z` and
  `ParrottCentralizerHypotheses z`, with the common ambient hypotheses,
  and must prove `Nonempty (G ≃* Tits.ParrottGroup)`. This enters the
  catalogue by `IsNGroupModel.tits`.
* `ng-odd-core-recognition`: given `t : G`, `orderOf t = 2`, and
  `pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥`, prove
  `IsNTwoGroupModel G`. This branch has no `hcore` assumption and must
  be recognized, not declared impossible.

These four goals are not premises of the reduction. Final classification
names remain reserved for unconditional model recognition after they are
proved. Source: Stellmacher, Theorem 2 and Section 11; the recognition,
transfer, and Sylow bounds are proved in the imported owner modules.
-/

namespace Stellmacher.Recognition
universe u

/-- Unconditional residual recognition, retaining the supplied Sylow, the
actual local configurations, and the genuine global odd-core alternative. -/
public theorem simple_nTwo_terminal_residual_reduction
    {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : IsNTwoGroup G) (S : Sylow 2 G) :
    IsNTwoGroupModel G ∨
    ((∀ U : Subgroup G, IsTwoLocal U → pPrimeCore 2 U = ⊥) ∧
      ((IsOfGTwoTwoDerivedType G ∧ Nat.card S = 32) ∨
        (Nonempty (LargeTerminalContext S) ∧
          (Nat.card S = 2048 ∨ Nat.card S = 4096)))) ∨
    (∃ t : G, orderOf t = 2 ∧
      pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥) := by
  rcases simple_nTwo_terminal_reduction hns hN S with
    hModel | ⟨hcore, hGTwo | hLarge | hSemi | h32⟩ | hOdd
  · exact Or.inl hModel
  · rcases sylow_card_of_gTwoTwoDerived_type S hGTwo with h32 | h64
    · exact Or.inr (Or.inl ⟨hcore, Or.inl ⟨hGTwo, h32⟩⟩)
    · exact (gTwo_card64_exclusion hns hN hcore hGTwo S h64).elim
  · obtain ⟨ctx⟩ := hLarge
    exact Or.inr (Or.inl ⟨hcore, Or.inr ⟨⟨ctx⟩, ctx.sylow_card⟩⟩)
  · exact Or.inl (isNTwoGroupModel_of_simple_nTwo_semidihedral S hSemi hN hcore)
  · obtain ⟨hOrder, P, hP, hModel⟩ := h32
    exact (not_sylow32_maximal_c2s4 hns hN S hOrder P hP hModel).elim
  · exact Or.inr (Or.inr hOdd)

end Stellmacher.Recognition
