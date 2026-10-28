module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.Contracts
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Using the internal decomposition in G.9.2

The inclusion-preserving equivalences imply that distinct factors commute,
their displacement spaces meet trivially, and each factor fixes the other
summands pointwise. Thus the witnesses carry the independent actions needed
in the Fitting application. The total dimension is the sum of the dimensions
of the actual displacement spaces.

These consequences use only the internal decomposition, not the model
classification or any additional faithfulness premise.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {H : Subgroup G} {r : ℕ}

theorem InternalDecomposition.factor_le (d : InternalDecomposition ρ H r)
    (i : Fin r) : d.factor i ≤ H := by
  intro g hg
  have he : (d.groupEquiv (Pi.mulSingle i ⟨g, hg⟩) : G) = g :=
    d.group_inclusion i ⟨g, hg⟩
  exact he ▸ (d.groupEquiv (Pi.mulSingle i ⟨g, hg⟩)).property

theorem InternalDecomposition.factors_commute (d : InternalDecomposition ρ H r)
    {i j : Fin r} (hij : i ≠ j) (g : d.factor i) (h : d.factor j) :
    Commute (g : G) (h : G) := by
  have hc := ((Pi.mulSingle_commute hij g h).map d.groupEquiv.toMonoidHom).map H.subtype
  change Commute (d.groupEquiv (Pi.mulSingle i g) : G)
    (d.groupEquiv (Pi.mulSingle j h) : G) at hc
  rwa [d.group_inclusion, d.group_inclusion] at hc

theorem InternalDecomposition.spaces_disjoint (d : InternalDecomposition ρ H r)
    {i j : Fin r} (hij : i ≠ j) :
    Disjoint (movedSpace ρ (d.factor i)) (movedSpace ρ (d.factor j)) := by
  apply Submodule.disjoint_def.mpr
  intro v hvi hvj
  have he : d.spaceEquiv (Pi.single i ⟨v, hvi⟩) =
      d.spaceEquiv (Pi.single j ⟨v, hvj⟩) := by
    rw [d.space_inclusion, d.space_inclusion]
  have hi := congrFun (d.spaceEquiv.injective he) i
  have hv : (⟨v, hvi⟩ : movedSpace ρ (d.factor i)) = 0 := by
    simpa only [Pi.single_eq_same, Pi.single_eq_of_ne hij] using hi
  exact congrArg Subtype.val hv

private theorem movedSpace_stable_of_centralizes (K : Subgroup G) (g : G)
    (hc : ∀ k : K, Commute g (k : G)) {v : V} (hv : v ∈ movedSpace ρ K) :
    ρ g v ∈ movedSpace ρ K := by
  change v ∈ Submodule.span (ZMod 2)
    (Set.range fun kv : K × V => ρ kv.1 kv.2 - kv.2) at hv
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨⟨k, w⟩, rfl⟩ := hw
    have he : ρ g (ρ k w) = ρ k (ρ g w) := by
      change (ρ g * ρ k) w = (ρ k * ρ g) w
      rw [← map_mul, ← map_mul, (hc k).eq]
    rw [map_sub, he]
    exact Representation.Coinvariants.sub_mem_ker (ρ := ρ.comp K.subtype) k (ρ g w)
  | zero => simp only [map_zero, Submodule.zero_mem]
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

/-- A factor is the identity on every other displacement summand. -/
theorem InternalDecomposition.cross_fix (d : InternalDecomposition ρ H r)
    {i j : Fin r} (hij : i ≠ j) (g : d.factor i)
    (v : movedSpace ρ (d.factor j)) : ρ g v = (v : V) := by
  apply sub_eq_zero.mp
  apply Submodule.disjoint_def.mp (d.spaces_disjoint hij)
  · exact Representation.Coinvariants.sub_mem_ker (ρ := ρ.comp (d.factor i).subtype) g v
  · exact Submodule.sub_mem _
      (movedSpace_stable_of_centralizes (d.factor j) g
        (fun h => d.factors_commute hij g h) v.property) v.property

theorem InternalDecomposition.finrank_eq_sum [FiniteDimensional (ZMod 2) V]
    (d : InternalDecomposition ρ H r) :
    Module.finrank (ZMod 2) V = ∑ i, Module.finrank (ZMod 2) (movedSpace ρ (d.factor i)) := by
  rw [← d.spaceEquiv.finrank_eq, Module.finrank_pi_fintype]

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity
