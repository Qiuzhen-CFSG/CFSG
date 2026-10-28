module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.UnitaryClosure
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.FiniteClosure

/-!
# Applying the component exclusions to the literal Hall kernel

The selected elementary odd subgroup lies in both the ambient Hall image
and the original section centralizer. The explicit module-fixation premise
therefore makes it centralize the original full module, and its elementary
prime order supplies the required oddness. The unitary, alternating and
order obstructions apply with exactly these subgroup maps. In the large
unitary-four, binary linear and M24 rows, model outer action and residual
placement are discharged from covering uniqueness.

Source: Aschbacher--Smith 10.2.3(2), printed p.745, using 4.4.3 and
4.4.10--12, pp.621--622. These are conditional branch proofs. The earlier
module-fixation and covering-uniqueness premises remain with this task;
the generation-cap task retains final generation assembly.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  {H : Subgroup G} (Y : Subgroup H)
  (hfix : Y.map H.subtype ⊓ sectionCentralizer (localOrbit T L) ≤
    centralizer (D.fullModule : Set G))
  {p : ℕ} [Fact p.Prime] (hp : Odd p)
  (A : Subgroup G) (hA : IsElementaryAbelian p A)
  (hAY : A ≤ Y.map H.subtype) (hAC : A ≤ sectionCentralizer (localOrbit T L))
  (K : Subgroup (normalizer (A : Set G)))
  (hFK : ((solvableResidual
    (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (A : Set G)).subtype).subgroupOf
        (normalizer (A : Set G)) ≤ K)
include D hn hfix hp hA hAY hAC hFK

/-- The literal elementary Hall kernel satisfies the order
component exclusion after its module fixation and residual placement. -/
theorem source_hall_kernel_no_placed_order_component
    {q a b c : ℕ} (hq : q.Prime) (hc : Squarefree c)
    (hcard : Nat.card (K ⧸ center K) ∣ 2 ^ a * q ^ b * c) : False := by
  let := hA
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact hp.pow
  exact source_nonnormal_oddNormalizer_no_component_of_order D hn A hAC hodd
    ((le_inf hAY hAC).trans hfix) K hFK hq hc hcard

/-- The literal elementary Hall kernel satisfies the unitary-four
component exclusion after its module fixation and residual placement. -/
theorem source_hall_kernel_no_placed_unitary_four_component
    {a : ℕ} (ha : 0 < a)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ a)) : False := by
  let := hA
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact hp.pow
  exact source_nonnormal_oddNormalizer_no_placed_unitary_four_component D hn A hAC hodd
    ((le_inf hAY hAC).trans hfix) K hFK ha hm

/-- The literal elementary Hall kernel satisfies the unitary-five
component exclusion after its module fixation and residual placement. -/
theorem source_hall_kernel_no_placed_unitary_five_component
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 5 4) : False := by
  let := hA
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact hp.pow
  exact source_nonnormal_oddNormalizer_no_placed_unitary_five_component D hn A hAC hodd
    ((le_inf hAY hAC).trans hfix) K hFK hm

/-- The literal elementary Hall kernel satisfies the alternating
component exclusion after its module fixation and residual placement. -/
theorem source_hall_kernel_no_placed_alternating_component
    {n : ℕ} (hn9 : n ≤ 9)
    (e : K ⧸ center K ≃* alternatingGroup (Fin n)) : False := by
  let := hA
  have hodd : Odd (Nat.card A) := by
    obtain ⟨n,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact hp.pow
  exact source_nonnormal_oddNormalizer_no_placed_alternating_component D hn A hAC hodd
    ((le_inf hAY hAC).trans hfix) K hFK hn9 e

omit hFK in
/-- The binary linear rows for the literal elementary Hall kernel need
only the earlier module-fixation and covering-uniqueness inputs. -/
theorem source_hall_kernel_no_binary_linear_component
    (hu : UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (A : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (A : Set G))) D.maximalLocal)
    (hK : IsComponent (normalizer (A : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (A : Set G)).subtype ≤ D.maximalLocal)
    {n : ℕ} (hn45 : n = 4 ∨ n = 5)
    (hm : ClassicalGroup.IsPSL (K ⧸ center K) n 2) : False := by
  let := hA
  have hodd : Odd (Nat.card A) := by
    obtain ⟨k,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact hp.pow
  exact source_nonnormal_oddNormalizer_no_binary_linear_component D hn A hAC hodd
    ((le_inf hAY hAC).trans hfix) hu K hK hout hn45 hm

omit hFK in
/-- The M24 row for the literal elementary Hall kernel has its model
outer action and original residual placement discharged. -/
theorem source_hall_kernel_no_m24_component
    (hu : UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (A : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (A : Set G))) D.maximalLocal)
    (hK : IsComponent (normalizer (A : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (A : Set G)).subtype ≤ D.maximalLocal)
    (e : K ⧸ center K ≃* Sporadic.Mathieu.M24) : False := by
  let := hA
  have hodd : Odd (Nat.card A) := by
    obtain ⟨k,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact hp.pow
  exact source_nonnormal_oddNormalizer_no_m24_component D hn A hAC hodd
    ((le_inf hAY hAC).trans hfix) hu K hK hout e

omit hFK in
/-- The literal Hall-kernel application also discharges outer action and
component placement in the large unitary-four family. -/
theorem source_hall_kernel_no_large_unitary_four_component
    (hu : UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (A : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (A : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (A : Set G))) D.maximalLocal)
    (hK : IsComponent (normalizer (A : Set G)) K) [K.Normal]
    (hout : ¬ K.map (normalizer (A : Set G)).subtype ≤ D.maximalLocal)
    {n : ℕ} (hn' : 1 < n)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ n)) : False := by
  let := hA
  have hodd : Odd (Nat.card A) := by
    obtain ⟨k,he⟩ := (IsElementaryAbelian.isPGroup p A).exists_card_eq
    rw [he]
    exact hp.pow
  exact source_nonnormal_oddNormalizer_no_large_unitary_four_component D hn A hAC hodd
    ((le_inf hAY hAC).trans hfix) hu K hK hout hn' hm

end CFSG.Quasithin.Chapter10
