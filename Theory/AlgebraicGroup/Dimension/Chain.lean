module

public import Theory.AlgebraicGroup.Dimension.Finite
public import Theory.AlgebraicGroup.Dimension.Strict

universe u

/-! Ascending-chain and minimum conditions for algebraic varieties and closed subgroups -/

namespace Theory.AlgebraicGroup

open scoped TensorProduct Cardinal

open LinearMap Submodule

variable {k : Type u} [Field k]

/-- A monotone sequence of natural numbers bounded above is eventually
constant. -/
private lemma monotone_nat_eventually_constant_of_bounded
    (f : ℕ → ℕ) (hf : Monotone f) (B : ℕ) (hB : ∀ n, f n ≤ B) :
    ∃ n, ∀ m, n ≤ m → f m = f n := by
  have hrange : Set.range f ⊆ Set.Iic B := by
    rintro _ ⟨n, rfl⟩
    exact hB n
  have hfinite : (Set.range f).Finite := (Set.finite_Iic B).subset hrange
  obtain ⟨v, hv⟩ := hfinite.exists_maximal (Set.range_nonempty f)
  rcases hv.1 with ⟨n, rfl⟩
  refine ⟨n, fun m hnm => ?_⟩
  have hle : f n ≤ f m := hf hnm
  exact le_antisymm (hv.2 (Set.mem_range_self m) hle) hle

/-! ## (d) The maximum/minimum conditions

The point space of a presented variety is Noetherian (`Variety.noetherianSpace_point`),
so the family of closed subsets satisfies the minimum condition: every nonempty
family of closed sets contains a minimal member.  This is the Noetherianity
extraction behind the finiteness statements of Proposition 1.1.4(a).  The
maximum condition for connected closed subgroups follows instead from strict
dimension increase under proper inclusion and finiteness of dimension.
-/

/-- Proposition 1.1.6(d): every ascending sequence of connected closed
subgroups eventually stabilizes. -/
public theorem ascending_connectedClosedSubgroups_eventually_constant
    (G : Variety k) [AlgebraicGroup G]
    (H : ℕ → ClosedSubgroup G)
    (hmono : ∀ {n m}, n ≤ m → H n ≤ H m)
    (hconnected : ∀ n,
      _root_.IsConnected (H n : Set (Variety.Point G))) :
    ∃ n, ∀ m, n ≤ m → H m = H n := by
  let d : ℕ → ℕ := fun n => Cardinal.toNat
    (Variety.dimension (H n).carrierVariety)
  have hdmono : Monotone d := by
    intro n m hnm
    by_cases heq : H n = H m
    · simp [d, heq]
    · exact (Cardinal.toNat_lt_toNat
        (connected_closedSubgroup_dimension_lt_of_le_of_ne
          (H n) (H m) (hmono hnm) heq (hconnected n) (hconnected m))
        (variety_dimension_lt_aleph0 (H m).carrierVariety)).le
  let B := Cardinal.toNat (Variety.dimension G)
  have hdbound : ∀ n, d n ≤ B := by
    intro n
    exact Cardinal.toNat_le_toNat
      (closedSubvariety_dimension_le G (H n).isZariskiClosed)
      (variety_dimension_lt_aleph0 G)
  obtain ⟨n, hn⟩ := monotone_nat_eventually_constant_of_bounded
    d hdmono B hdbound
  refine ⟨n, fun m hnm => ?_⟩
  by_contra hne
  have hlt := connected_closedSubgroup_dimension_lt_of_le_of_ne
    (H n) (H m) (hmono hnm) (fun h => hne h.symm)
      (hconnected n) (hconnected m)
  have hnatlt : d n < d m := Cardinal.toNat_lt_toNat hlt
    (variety_dimension_lt_aleph0 (H m).carrierVariety)
  exact (ne_of_lt hnatlt) (hn m hnm).symm

/-- The closed subsets of the point space satisfy the minimum condition
(extracted from Noetherianity). -/
public theorem noetherian_closedSets_minimumCondition (V : Variety k)
    (F : Set (TopologicalSpace.Closeds (Variety.Point V))) (hF : F.Nonempty) :
    ∃ C ∈ F, ∀ D ∈ F, ¬ D < C := by
  exact WellFounded.has_min (α := TopologicalSpace.Closeds (Variety.Point V))
    (r := (· < ·)) wellFounded_lt F hF

end Theory.AlgebraicGroup
