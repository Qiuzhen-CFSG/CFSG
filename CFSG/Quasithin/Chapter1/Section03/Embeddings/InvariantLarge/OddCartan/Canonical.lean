module

public import Theory.GroupTheory.SolvableResidual
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# The canonical centralizer residual

For a normal subgroup D and a subgroup S of the ambient group, S normalizes
C_D(Z(S)) and therefore its solvable residual. Intersecting that residual
with B gives a subgroup normalized by N_S(B). This requires neither a choice
of an SL₂ embedding nor a claim that an arbitrary such embedding is invariant.

The residual here is the terminal derived subgroup (the intersection of the
derived series). Its identification with an SL₂ and the cyclic decomposition
of B are separate concrete model calculations.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
proof of 1.3.4, printed pp. 510–511.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
variable {J : Type*} [Group J]

/-- The center of S, viewed in the ambient group. -/
def centerImage (S : Subgroup J) : Subgroup J := (center S).map S.subtype

/-- The centralizer inside D of the entire center of S. -/
def centralizerIn (D S : Subgroup J) : Subgroup J :=
  D ⊓ centralizer (centerImage S : Set J)

/-- The subgroup denoted `C_D(Z(S))^∞` in the source. -/
def canonicalResidual (D S : Subgroup J) : Subgroup J :=
  (solvableResidual (centralizerIn D S)).map (centralizerIn D S).subtype

/-- The canonical candidate for the invariant factor, as a subgroup of B. -/
def canonicalFactor (D S B : Subgroup J) : Subgroup B :=
  (canonicalResidual D S).subgroupOf B

/-- S centralizes its own center after inclusion in the ambient group. -/
theorem le_centralizer_centerImage (S : Subgroup J) :
    S ≤ centralizer (centerImage S : Set J) := by
  intro s hs z hz
  obtain ⟨z, hz, rfl⟩ := hz
  exact (congrArg Subtype.val ((mem_center_iff.mp hz) ⟨s, hs⟩)).symm

/-- Normality of D makes the relative centralizer S-invariant. -/
theorem le_normalizer_centralizerIn (D S : Subgroup J) [D.Normal] :
    S ≤ normalizer (centralizerIn D S) :=
  (le_inf (show S ≤ normalizer D from le_normalizer_of_normal)
    ((le_centralizer_centerImage S).trans (centralizer _).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf

/-- S normalizes the terminal derived subgroup of its relative centralizer. -/
theorem le_normalizer_canonicalResidual (D S : Subgroup J) [D.Normal] :
    S ≤ normalizer (canonicalResidual D S) := by
  apply le_normalizer_iff.mpr
  intro s hs x hx
  obtain ⟨x, hx, rfl⟩ := hx
  let f := (centralizerIn D S).normalizerMonoidHom
    ⟨s, le_normalizer_centralizerIn D S hs⟩
  have hf : f x ∈ solvableResidual (centralizerIn D S) :=
    map_solvableResidual_le f.toMonoidHom (mem_map_of_mem f.toMonoidHom hx)
  exact ⟨f x, hf, rfl⟩

/-- N_S(B) preserves the actual ambient image of the canonical factor. -/
theorem canonicalFactor_normalized (D S B : Subgroup J) [D.Normal] :
    S ⊓ normalizer B ≤ normalizer ((canonicalFactor D S B).map B.subtype) := by
  rw [canonicalFactor, subgroupOf_map_subtype]
  exact (le_inf (inf_le_left.trans (le_normalizer_canonicalResidual D S))
    inf_le_right).trans inf_normalizer_le_normalizer_inf

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
