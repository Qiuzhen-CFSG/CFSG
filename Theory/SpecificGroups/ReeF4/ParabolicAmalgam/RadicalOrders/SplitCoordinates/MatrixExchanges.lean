module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.Collection
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.RootSums
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.Commuting
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.EqualLength
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.RadicalOrders.SplitCoordinates.MatrixExchanges.MixedLength

/-!
# Filtered exchanges for the supported F4 root matrices

The absent-root-sum case has an empty correction word, by integral operator
commutation and the divided-power formulas. In the root-sum cases a raw
matrix identity supplies the correction word. Every correction root in the
positive integral cone stays in the chosen support and has height strictly
above both inputs. Lifting the word through the subgroup and matrix-unit
coercions therefore gives exactly the adjacent-exchange premise used by
`wordInSubgroup_surjective_of_exchange`.

The equal-length and mixed-length root-sum identities discharge every matrix
calculation in `rootGenerator_exchange`. The result holds for every coefficient
field, including `m = 0`, and for the positive support and both radical supports.

Source: the Chevalley root collection underlying Aschbacher–Smith,
F.1.12(I)(5), printed p.263 (PDF p.274) of `refs/quasithin.pdf`.
-/

public section

open Theory.AlgebraicGroup StandardRootSystem
open FilteredCollection
namespace ReeF4.Parabolics.RadicalCoordinates
noncomputable section

/-- Lift a raw matrix exchange to the chosen root support. -/
theorem rootGenerator_exchange_of_matrixExchange (m : ℕ) {k : Support}
    (r s : Root k) (a b : CoefficientField m) (h : MatrixExchange r.val s.val a b) :
    ∃ correction : List (Root k × CoefficientField m),
      (∀ z ∈ correction,
        max (rootDegree r.val) (rootDegree s.val) < rootDegree z.1.val) ∧
      rootGeneratorInGroup m r.val a * rootGeneratorInGroup m s.val b =
        rootGeneratorInGroup m s.val b * rootGeneratorInGroup m r.val a *
          wordProduct (fun q : Root k => rootGeneratorInGroup m q.val) correction := by
  classical
  obtain ⟨c, hc, he⟩ := h
  let lift : {z // z ∈ c} → Root k × CoefficientField m := fun z =>
    (⟨z.val.1, (positiveCone_supported_degree r s (hc z.val z.property)).1⟩, z.val.2)
  refine ⟨c.attach.map lift, ?_, ?_⟩
  · intro z hz
    obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
    exact (positiveCone_supported_degree r s (hc w.val w.property)).2
  · apply Subtype.ext
    apply Units.ext
    change (F4Chevalley.rootCurve r.val a).val * (F4Chevalley.rootCurve s.val b).val = _
    rw [he]
    congr 1
    let ρ : SplitGroup m →* MatrixCarrier m :=
      (Units.coeHom (MatrixCarrier m)).comp (SplitGroup m).subtype
    change (c.map (fun z => (F4Chevalley.rootCurve z.1 z.2).val)).prod =
      ρ (wordProduct (fun q : Root k => rootGeneratorInGroup m q.val) (c.attach.map lift))
    simp only [wordProduct, map_list_prod, List.map_map]
    change (c.map (fun z => (F4Chevalley.rootCurve z.1 z.2).val)).prod =
      (c.attach.map (fun z => (F4Chevalley.rootCurve z.val.1 z.val.2).val)).prod
    simpa only [List.map_map, Function.comp_def] using
      (congrArg (fun l => (l.map (fun z : F4Chevalley.Root × CoefficientField m =>
        (F4Chevalley.rootCurve z.1 z.2).val)).prod) (List.attach_map_subtype_val c)).symm

/-- The empty correction word settles every pair whose root sum is absent. -/
theorem rootGenerator_exchange_of_no_sum (m : ℕ) {k : Support}
    (r s : Root k) (a b : CoefficientField m)
    (hsum : typeF4RootPairing.root r.val + typeF4RootPairing.root s.val ∉
      Set.range typeF4RootPairing.root) :
    ∃ correction : List (Root k × CoefficientField m),
      (∀ z ∈ correction,
        max (rootDegree r.val) (rootDegree s.val) < rootDegree z.1.val) ∧
      rootGeneratorInGroup m r.val a * rootGeneratorInGroup m s.val b =
        rootGeneratorInGroup m s.val b * rootGeneratorInGroup m r.val a *
          wordProduct (fun q : Root k => rootGeneratorInGroup m q.val) correction := by
  refine ⟨[], by simp, ?_⟩
  simpa only [wordProduct, List.map_nil, List.prod_nil, mul_one] using
    (rootGenerator_commute_of_no_sum m r s hsum a b).eq

/-- Raw root-sum matrix exchanges suffice for filtered exchanges: support
membership, degree bounds, and absent sums are discharged here. -/
theorem rootGenerator_exchange_of_rootSum_exchanges (m : ℕ)
    (hrootSum : ∀ (r s : F4Chevalley.Root),
      typeF4RootPairing_base.IsPos r → typeF4RootPairing_base.IsPos s → r ≠ s →
      typeF4RootPairing.root r + typeF4RootPairing.root s ∈ Set.range typeF4RootPairing.root →
      ∀ a b : CoefficientField m, MatrixExchange r s a b)
    {k : Support} (r s : Root k) (a b : CoefficientField m) (hrs : r ≠ s) :
    ∃ correction : List (Root k × CoefficientField m),
      (∀ z ∈ correction,
        max (rootDegree r.val) (rootDegree s.val) < rootDegree z.1.val) ∧
      rootGeneratorInGroup m r.val a * rootGeneratorInGroup m s.val b =
        rootGeneratorInGroup m s.val b * rootGeneratorInGroup m r.val a *
          wordProduct (fun q : Root k => rootGeneratorInGroup m q.val) correction := by
  classical
  by_cases hsum : typeF4RootPairing.root r.val + typeF4RootPairing.root s.val ∈
      Set.range typeF4RootPairing.root
  · exact rootGenerator_exchange_of_matrixExchange m r s a b
      (hrootSum r.val s.val (supported_isPos r) (supported_isPos s)
        (fun h => hrs (Subtype.ext h)) hsum a b)
  · exact rootGenerator_exchange_of_no_sum m r s a b hsum

/-- Any two distinct supported root generators admit an adjacent exchange with
corrections strictly above both heights. This is exactly the `hswap` premise of
`wordInSubgroup_surjective_of_exchange`, for all three supports and every `m`. -/
theorem rootGenerator_exchange (m : ℕ) {k : Support}
    (r s : Root k) (a b : CoefficientField m) (hrs : r ≠ s) :
    ∃ correction : List (Root k × CoefficientField m),
      (∀ z ∈ correction,
        max (rootDegree r.val) (rootDegree s.val) < rootDegree z.1.val) ∧
      rootGeneratorInGroup m r.val a * rootGeneratorInGroup m s.val b =
        rootGeneratorInGroup m s.val b * rootGeneratorInGroup m r.val a *
          wordProduct (fun q : Root k => rootGeneratorInGroup m q.val) correction := by
  apply rootGenerator_exchange_of_rootSum_exchanges m ?_ r s a b hrs
  intro r s hr hs hrs hsum a b
  by_cases hlen : IsLongRoot r ↔ IsLongRoot s
  · exact matrixExchange_of_equal_length_sum m r s hr hs hrs hlen hsum a b
  · exact matrixExchange_of_mixed_length_sum m r s hr hs hrs hlen hsum a b

end
end ReeF4.Parabolics.RadicalCoordinates
