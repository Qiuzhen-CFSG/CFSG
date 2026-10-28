module

public import Theory.Representation.BinaryPermutation.ThreeTensorDisplacement
public import Theory.Representation.BinaryPermutation.FiveLowRank
public import Theory.Representation.BinaryPermutation.FiveTensorQuadratic
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Low displacement in the binary A₅-module tensor alternatives

Any nonidentity S₃ component moves at least four dimensions. A pure S₅
component has twice its core displacement rank, so rank at most two forces
a single transposition and rank exactly two. Parity excludes that actor in
A₅ × S₃. The calculation proves more than the required involution case.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, 14.4.2(5)
and 14.4.6(a), printed pp.1006,1008. Here the A₅ module is the orthogonal
five-point augmentation core, not the scalar-restricted natural SL₂(4) module.
-/

@[expose] public section
open TensorProduct
namespace BinaryPermutation.FiveTensorLowRank
/-- The two actual binary tensor factors, in S₅ × S₃ order. -/
abbrev Space := core (Fin 5) ⊗[ZMod 2] core (Fin 3)
/-- The external action on those factors. -/
noncomputable abbrev action := FiveTensorQuadratic.tensorAction (coreRepresentation (Fin 3))

/-- Every nonidentity actor moving at most two dimensions is a pure transposition. -/
theorem inspection (g : Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)) (hg : g ≠ 1)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (action g - LinearMap.id)) ≤ 2) :
    (∃ i j : Fin 5, i ≠ j ∧ g = (Equiv.swap i j, 1)) ∧
      Module.finrank (ZMod 2) (LinearMap.range (action g - LinearMap.id)) = 2 := by
  have hs : g.2 = 1 := by
    by_contra hn
    have hd := ThreeTensor.dimension_le_displacement (coreRepresentation (Fin 5)) g hn
    rw [finrank_core] at hd
    change 4 ≤ Module.finrank (ZMod 2) (LinearMap.range (action g - LinearMap.id)) at hd
    have impossible : (4 : ℕ) ≤ 2 := hd.trans hr
    omega
  have hg' : g = (g.1, 1) := Prod.ext rfl hs
  have hfirst : g.1 ≠ 1 := by
    intro h
    apply hg
    exact Prod.ext h hs
  have hd : Module.finrank (ZMod 2) (LinearMap.range (action g - LinearMap.id)) =
      2 * Module.finrank (ZMod 2)
        (LinearMap.range (coreRepresentation (Fin 5) g.1 - LinearMap.id)) := by
    rw [hg']
    exact ThreeTensor.displacement_first (coreRepresentation (Fin 5)) g.1
  have hc : Module.finrank (ZMod 2)
      (LinearMap.range (coreRepresentation (Fin 5) g.1 - LinearMap.id)) ≤ 1 := by omega
  obtain ⟨i, j, hij, hf⟩ := (FiveLowRank.low_rank g.1 hc).resolve_left hfirst
  refine ⟨⟨i, j, hij, Prod.ext hf hs⟩, ?_⟩
  have hp := FiveLowRank.rank_pos g.1 hfirst
  omega

/-- The alternating-factor tensor action has no nonidentity actor of rank at most two. -/
theorem alternating_bound (g : alternatingGroup (Fin 5) × Equiv.Perm (Fin 3))
    (hg : g ≠ 1) :
    2 < Module.finrank (ZMod 2) (LinearMap.range (action (g.1.val, g.2) - LinearMap.id)) := by
  by_contra! hr
  have hne : (g.1.val, g.2) ≠ (1 : Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3)) := by
    intro he
    have h1 : g.1.val = 1 := congrArg Prod.fst he
    have h2 : g.2 = 1 := congrArg Prod.snd he
    exact hg (Prod.ext (Subtype.ext h1) h2)
  obtain ⟨⟨i, j, hij, he⟩, _⟩ := inspection (g.1.val, g.2) hne hr
  have hm := g.1.property
  have hf : g.1.val = Equiv.swap i j := congrArg Prod.fst he
  rw [Equiv.Perm.mem_alternatingGroup, hf, Equiv.Perm.sign_swap hij] at hm
  exact (by decide : (-1 : ℤˣ) ≠ 1) hm
end BinaryPermutation.FiveTensorLowRank
