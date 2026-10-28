module

public import Theory.Representation.ReeF4.FixedSpaceBounds.Estimate.BasicInvolutions.BinaryOddElements.TorusCoverage.OrbitBalance
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4ChevalleySplitTorus
public import Theory.SpecificGroups.ReeF4.ExceptionalEndomorphism.WordRelations.Faithfulness.ShortOperators.Geometry

/-!
# The actual roots behind the two F4 weight tables

The simple-coroot pairings distinguish the actual real-coordinate F4 roots.
Their reflection law agrees with the integral reflection used by the published
short and long tables. Root routes and preservation of root length show that
each actual root belongs to the appropriate table. Conversely, reversing the
word for entry ten realizes each highest weight from a simple root, and the
published words then realize all twenty-four entries. Injectivity of the
pairings proves that each entry occurs exactly once.

The two equivalences and their weight specifications feed the ideal and
quotient displacement counts in `WeightCensus`. This is the root-datum census
used in the Guralnick--Malle II Lemma 8.8 fixed-space argument (internal p.57),
with the F4 conventions of GLS3, Sections 1.14 and 2.8.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction ReeF4.WordRelations
open ReeF4.BinaryDegree.ExceptionalTensor ReeF4.BinaryDegree.ExceptionalTensor.ZeroAndMiddle
open scoped Classical Matrix
noncomputable section
namespace ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Balance.WeightCensus

private def rootWeight (r : typeF4Roots) : CorootWeight := F4Chevalley.basisWeight (Sum.inr r)

private theorem rootWeight_injective : Function.Injective rootWeight := by
  intro r s h
  apply typeF4RootPairing_base.injective_pairingIn
  funext j
  obtain ⟨i, rfl⟩ := typeF4RootPairing_baseEquiv.surjective j
  exact congrFun h i

private theorem rootWeight_simple (i : Fin 4) :
    rootWeight (typeF4RootPairing_baseEquiv i).val = typeF4CartanMatrix i := by
  funext j
  exact typeF4RootPairing_base_cartan_apply i j

private theorem rootWeight_reflection (i : Fin 4) (r : typeF4Roots) :
    rootWeight (typeF4RootPairing.reflectionPerm (typeF4RootPairing_baseEquiv i).val r) =
      EndNode.reflectWeight i (rootWeight r) := by
  funext j
  change typeF4RootPairing.pairingIn ℤ (typeF4RootPairing.reflectionPerm _ r) _ =
    typeF4RootPairing.pairingIn ℤ r _ - typeF4RootPairing.pairingIn ℤ r _ * typeF4CartanMatrix i j
  rw [← typeF4RootPairing_base_cartan_apply i j]
  change typeF4RootPairing.pairingIn ℤ (typeF4RootPairing.reflectionPerm _ r) _ =
    typeF4RootPairing.pairingIn ℤ r _ - typeF4RootPairing.pairingIn ℤ r _ * typeF4RootPairing.pairingIn ℤ _ _
  apply Int.cast_injective (α := ℝ)
  push_cast
  have hcast (r s : typeF4Roots) :
      (typeF4RootPairing.pairingIn ℤ r s : ℝ) = typeF4RootPairing.pairing r s :=
    typeF4RootPairing.algebraMap_pairingIn ℤ r s
  simp only [hcast, RootPairing.pairing, RootPairing.root',
    RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]

private theorem short_closed : ∀ (i : Fin 4) (n : Fin 24),
    ∃ m, EndNode.reflectWeight i (EndNode.endOrbitWeight n) = EndNode.endOrbitWeight m := by decide

private theorem short_simple : ∀ i : Fin 4, 2 ≤ i.val →
    ∃ n : Fin 24, typeF4CartanMatrix i = EndNode.endOrbitWeight n := by decide

private theorem long_simple : ∀ i : Fin 4, ¬2 ≤ i.val →
    ∃ n : Fin 24, typeF4CartanMatrix i = longOrbitWeight n := by decide

private theorem reflectionWord_mem (W : Fin 24 → CorootWeight)
    (hc : ∀ i n, ∃ m, EndNode.reflectWeight i (W n) = W m)
    (w : List typeF4RootPairing_base.support) (r : typeF4Roots) (hr : ∃ n, rootWeight r = W n) :
    ∃ n, rootWeight (reflectionWord w r) = W n := by
  induction w with
  | nil => exact hr
  | cons i w ih =>
    obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
    obtain ⟨n, hn⟩ := ih
    simpa only [reflectionWord, rootWeight_reflection, hn] using hc j n

private theorem short_weight_mem (r : typeF4Roots) (hr : IsShortRoot r) :
    ∃ n, rootWeight r = EndNode.endOrbitWeight n := by
  let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  have hs : IsShortRoot z.simple.val :=
    (ShortOperators.isShortRoot_reflectionWord z.word z.simple.val).mp (z.target.symm ▸ hr)
  obtain ⟨i, hi⟩ := typeF4RootPairing_baseEquiv.surjective z.simple
  have hm : ∃ n, rootWeight z.simple.val = EndNode.endOrbitWeight n := by
    rw [← hi, rootWeight_simple]
    exact short_simple i ((ShortOperators.isShortRoot_simple i).mp (hi.symm ▸ hs))
  simpa only [z.target] using reflectionWord_mem _ short_closed z.word z.simple.val hm

private theorem long_weight_mem (r : typeF4Roots) (hr : ¬IsShortRoot r) :
    ∃ n, rootWeight r = longOrbitWeight n := by
  let z := rootRoute (P := typeF4RootPairing) (b := typeF4RootPairing_base) r
  have hs : ¬IsShortRoot z.simple.val :=
    (ShortOperators.isShortRoot_reflectionWord z.word z.simple.val).not.mp (z.target.symm ▸ hr)
  obtain ⟨i, hi⟩ := typeF4RootPairing_baseEquiv.surjective z.simple
  have hm : ∃ n, rootWeight z.simple.val = longOrbitWeight n := by
    rw [← hi, rootWeight_simple]
    exact long_simple i ((ShortOperators.isShortRoot_simple i).not.mp (hi.symm ▸ hs))
  simpa only [z.target] using
    reflectionWord_mem _ longOrbitWeight_reflection_closed z.word z.simple.val hm

private def reflectList (w : List (Fin 4)) (r : typeF4Roots) : typeF4Roots :=
  w.foldl (fun s i => typeF4RootPairing.reflectionPerm (typeF4RootPairing_baseEquiv i).val s) r

private theorem reflectList_weight (w : List (Fin 4)) (r : typeF4Roots) :
    rootWeight (reflectList w r) =
      w.foldl (fun μ i => EndNode.reflectWeight i μ) (rootWeight r) := by
  induction w generalizing r with
  | nil => rfl
  | cons i w ih =>
    simpa only [reflectList, List.foldl_cons, rootWeight_reflection] using
      ih (typeF4RootPairing.reflectionPerm (typeF4RootPairing_baseEquiv i).val r)

private theorem reflectList_short (w : List (Fin 4)) (r : typeF4Roots) :
    IsShortRoot (reflectList w r) ↔ IsShortRoot r := by
  induction w generalizing r with
  | nil => rfl
  | cons i w ih =>
    exact (ih _).trans (ShortOperators.isShortRoot_reflection _ _)

private theorem short_highest_exists :
    ∃ r : typeF4Roots, IsShortRoot r ∧ rootWeight r = EndNode.endHighestWeight := by
  refine ⟨reflectList (EndNode.endOrbitWord 10).reverse
    (typeF4RootPairing_baseEquiv 3).val, ?_, ?_⟩
  · rw [reflectList_short, ShortOperators.isShortRoot_simple]
    decide
  · rw [reflectList_weight, rootWeight_simple]
    decide

private theorem long_highest_exists :
    ∃ r : typeF4Roots, ¬IsShortRoot r ∧ rootWeight r = ![1, 0, 0, 0] := by
  refine ⟨reflectList (longOrbitWord 10).reverse
    (typeF4RootPairing_baseEquiv 0).val, ?_, ?_⟩
  · rw [reflectList_short, ShortOperators.isShortRoot_simple]
    decide
  · rw [reflectList_weight, rootWeight_simple]
    decide

private theorem short_weight_exists (n : Fin 24) :
    ∃ r : {r : typeF4Roots // IsShortRoot r}, rootWeight r.val = EndNode.endOrbitWeight n := by
  obtain ⟨r, hr, hw⟩ := short_highest_exists
  refine ⟨⟨reflectList (EndNode.endOrbitWord n) r, (reflectList_short _ _).mpr hr⟩, ?_⟩
  change rootWeight (reflectList _ r) = _
  rw [reflectList_weight, hw, EndNode.endOrbitWord_spec]

private theorem long_weight_exists (n : Fin 24) :
    ∃ r : {r : typeF4Roots // ¬IsShortRoot r}, rootWeight r.val = longOrbitWeight n := by
  obtain ⟨r, hr, hw⟩ := long_highest_exists
  refine ⟨⟨reflectList (longOrbitWord n) r, (reflectList_short _ _).not.mpr hr⟩, ?_⟩
  change rootWeight (reflectList _ r) = _
  rw [reflectList_weight, hw, longOrbitWord_spec]

private def shortRoot (n : Fin 24) : {r : typeF4Roots // IsShortRoot r} :=
  (short_weight_exists n).choose

private theorem shortRoot_weight (n : Fin 24) :
    rootWeight (shortRoot n).val = EndNode.endOrbitWeight n :=
  (short_weight_exists n).choose_spec

private def longRoot (n : Fin 24) : {r : typeF4Roots // ¬IsShortRoot r} :=
  (long_weight_exists n).choose

private theorem longRoot_weight (n : Fin 24) :
    rootWeight (longRoot n).val = longOrbitWeight n :=
  (long_weight_exists n).choose_spec

/-- Each short root occurs exactly once in the published short-weight table. -/
def shortRootEquiv : Fin 24 ≃ {r : typeF4Roots // IsShortRoot r} :=
  Equiv.ofBijective shortRoot ⟨fun i j h => EndNode.endOrbitWeight_injective (by
    simpa only [shortRoot_weight] using congrArg (fun r => rootWeight r.val) h), by
    intro r
    obtain ⟨n, hn⟩ := short_weight_mem r.val r.property
    refine ⟨n, Subtype.ext (rootWeight_injective ?_)⟩
    exact (shortRoot_weight n).trans hn.symm⟩

/-- Each long root occurs exactly once in the published long-weight table. -/
def longRootEquiv : Fin 24 ≃ {r : typeF4Roots // ¬IsShortRoot r} :=
  Equiv.ofBijective longRoot ⟨fun i j h => longOrbitWeight_injective (by
    simpa only [longRoot_weight] using congrArg (fun r => rootWeight r.val) h), by
    intro r
    obtain ⟨n, hn⟩ := long_weight_mem r.val r.property
    refine ⟨n, Subtype.ext (rootWeight_injective ?_)⟩
    exact (longRoot_weight n).trans hn.symm⟩

theorem shortRootEquiv_weight (n : Fin 24) :
    F4Chevalley.basisWeight (Sum.inr (shortRootEquiv n).val) = EndNode.endOrbitWeight n :=
  shortRoot_weight n

theorem longRootEquiv_weight (n : Fin 24) :
    F4Chevalley.basisWeight (Sum.inr (longRootEquiv n).val) = longOrbitWeight n :=
  longRoot_weight n

end ReeF4.FixedSpaceEstimate.BasicInvolutions.BinaryOddElements.TorusCoverage.Balance.WeightCensus
