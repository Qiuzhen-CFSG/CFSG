module

public import Theory.SpecificGroups.Rudvalis.Model.OuterNormalizer.Invariance
public import Mathlib.Data.List.Perm.Basic

/-!
# Color refinement for the concrete Rudvalis relation

Counting incoming neighbors in a preserved color cell gives another preserved coloring.
The counts use the packed orbital rows, whose equality with `adj` was proved
in `Invariance`. Lists enumerate cells without repetition; permutations of
these lists preserve the counts. Numerical trace certificates are separate.

This is the refinement argument for the degree-4060 ATLAS model used in
GLS3, Table 5.3r, printed p.279; see `Model.PermutationData` for the source
and point-action convention.
-/

namespace Rudvalis.OuterNormalizer.RigidityCertificate
open InvarianceCertificate

@[expose] public def neighborCount (s : List (Fin 4060)) (x : Fin 4060) : Nat :=
  s.countP (fun y => (row y).testBit x.val)

public theorem neighborCount_invariant (p : Equiv.Perm (Fin 4060))
    (hp : p ∈ relationAut) (s : List (Fin 4060)) (hs : s.Nodup)
    (hc : ∀ x, p x ∈ s ↔ x ∈ s) (x : Fin 4060) :
    neighborCount s (p x) = neighborCount s x := by
  have he : (s.map p).Perm s := by
    apply (List.perm_ext_iff_of_nodup (hs.map p.injective) hs).mpr
    intro y
    obtain ⟨z, rfl⟩ := p.surjective y
    simpa only [List.mem_map, p.injective.eq_iff, exists_eq_right] using (hc z).symm
  unfold neighborCount
  rw [← he.countP_eq, List.countP_map]
  apply List.countP_congr
  intro y _
  exact (cachedAdj_iff_adj _ _).trans ((hp y x).trans (cachedAdj_iff_adj y x).symm)

/-- Count the set bits at a vertex in a short, preselected list of rows. -/
@[expose] public def bitCount (rows : List Nat) (x : Fin 4060) : Nat :=
  rows.countP (fun r => r.testBit x.val)

public theorem bitCount_eq (s : List (Fin 4060)) (rows : List Nat)
    (h : rows = s.map row) (x : Fin 4060) : bitCount rows x = neighborCount s x := by
  rw [h]
  simp only [bitCount, neighborCount, List.countP_map, Function.comp_def]

/-- A color refinement by the number of neighbors in an invariant color cell
is again invariant. The concrete equations are separate finite certificates. -/
public theorem refine_preserved (p : Equiv.Perm (Fin 4060)) (hp : p ∈ relationAut)
    (old new : Fin 4060 → Nat) (s : List (Fin 4060)) (tag base : Nat)
    (hs : s.Nodup) (hc : ∀ x, x ∈ s ↔ old x = tag)
    (he : ∀ x, new x = old x * base + neighborCount s x)
    (ho : ∀ x, old (p x) = old x) : ∀ x, new (p x) = new x := by
  have hc' (x : Fin 4060) : p x ∈ s ↔ x ∈ s := by rw [hc, hc, ho]
  intro x
  rw [he, he, ho, neighborCount_invariant p hp s hs hc']

@[expose] public def initial (k : Nat) (x : Fin 4060) : Nat := min x.val k

public theorem initial_preserved (k : Nat) (p : Equiv.Perm (Fin 4060))
    (hp : ∀ x : Fin 4060, x.val < k → p x = x) :
    ∀ x, initial k (p x) = initial k x := by
  intro x
  by_cases hx : x.val < k
  · rw [hp x hx]
  · have hy : ¬ (p x).val < k := by
      intro hy
      have he := p.injective (hp (p x) hy)
      exact hx (he ▸ hy)
    simp only [initial, Nat.min_eq_right (Nat.le_of_not_gt hx),
      Nat.min_eq_right (Nat.le_of_not_gt hy)]
end Rudvalis.OuterNormalizer.RigidityCertificate
