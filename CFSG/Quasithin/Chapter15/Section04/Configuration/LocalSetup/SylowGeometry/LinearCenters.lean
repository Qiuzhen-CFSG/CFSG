module

public import Theory.SpecificGroups.BinaryLinear.SylowCenters
public import CFSG.Quasithin.ClassicalModels
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The Sylow-center bound in the linear component case

In the component case of Aschbacher–Smith 15.4.20 (combined manuscript of
1 March 2004, printed p.1164), the linear component is PSL₄(2) or PSL₅(2).
Its Sylow two-subgroups have centers of order at most two. Combined with
`LocalSetup.faithful_inner_action_card_le_sylow_center`, this rules out the
source's faithful inner action of a central four-group fixing the Sylow
subgroup pointwise.

The model witness in `ClassicalGroup.IsPSL` uses an arbitrary finite field of
order two. We identify that field with `ZMod 2`, transport the genuine
projective quotient by the existing entrywise field equivalence, and then
apply the concrete binary bound. Source-case assembly and the inner-action
hypotheses remain with the owner of 15.4.20.
-/

open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup

/-- The concrete center bound required in the linear component case of 15.4.20,
including the arbitrary finite-field witness in the source model predicate. -/
public theorem binary_linear_sylow_center_card_le_two {H : Type*} [Group H] [Finite H]
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hH : ClassicalGroup.IsPSL H n 2)
    (S : Sylow 2 H) : Nat.card (Subgroup.center S) ≤ 2 := by
  have hdim : 2 ≤ n := by rcases hn with rfl | rfl <;> decide
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hH
  let : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = Fintype.card (ZMod 2) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard'
  let eH : H ≃* PSL(n, ZMod 2) := e.trans (Atlas.fieldEquivPSL n eF)
  rw [BinaryLinear.sylow_center_card_congr eH S]
  exact BinaryLinear.psl_sylow_center_card_le_two hdim _

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
