module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.CompiledMarkedActions
public import Theory.SpecificGroups.Held.Model.FourPointBase

/-!
# Sound evaluation of Held column-0 certificates

The unchanged representative words are evaluated using certified ATLAS
actions. The compiled marked actions evaluate the positive subgroup words,
and the compiled seeds give the middle/move product on the four base points.
Equality of those four images implies equality in the actual Held carrier.

`block_sound` extracts each checked row and supplies both outer-factor
memberships. Source and candidate provenance: `DoubleCosets/source/README.md`.
The candidate triples alone have no mathematical authority.
-/

namespace Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0Certificate
open Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification
open CompiledActions

@[expose] public def repAct (j : Fin 4831) : Fin 2058 → Fin 2058 :=
  wordAction (packedAction packA) (packedAction packA) (packedAction packB)
    (packedAction packBi) (fastRepresentativeWord j)

private theorem repAct_eq (j : Fin 4831) (p : Fin 2058) :
    repAct j p = representation (representative j) p := by
  rw [representation_representative]
  change wordAction fastA (fastA⁻¹ : Equiv.Perm (Fin 2058)) fastB
    (fastB⁻¹ : Equiv.Perm (Fin 2058)) _ p = _
  rw [wordAction_eq, fastA_eq, fastB_eq]

/-- Compare precisely the four images that determine an element of Held. -/
@[expose] public def checkB (j : Fin 4831) (e : Bool) (k : Fin 4831)
    (l r : Fin 1024) : Bool :=
  (List.range 4).all fun p =>
    repAct j (seed 0 e ⟨p % 4, Nat.mod_lt _ (by decide)⟩) ==
      subgroupAction l (repAct k
        (subgroupAction r ⟨p % 2058, Nat.mod_lt _ (by decide)⟩))

set_option maxRecDepth 8192 in
private theorem checkB_eq {j : Fin 4831} {e : Bool} {k : Fin 4831} {l r : Fin 1024}
    (h : checkB j e k l r = true) : representative j * middle 0 e * move 0 =
      subgroupElement l * representative k * subgroupElement r := by
  apply Held.eq_of_four_point_images
  intro p
  have hp := List.all_eq_true.mp h p.val (List.mem_range.mpr p.isLt)
  have hlt : p.val < 2058 := by omega
  have hp' : (⟨p.val % 4, Nat.mod_lt _ (by decide)⟩ : Fin 4) = p :=
    Fin.ext (Nat.mod_eq_of_lt p.isLt)
  have heq := beq_iff_eq.mp hp
  simp only [hp', Nat.mod_eq_of_lt hlt, repAct_eq, subgroupAction_eq, seed_eq,
    map_mul, Equiv.Perm.mul_apply] at heq
  simpa only [map_mul, Equiv.Perm.mul_apply] using heq

/-- Two consecutive rows per representative, retaining the original indices. -/
@[expose] public def blockCheck (start count : ℕ)
    (witnesses : Array (Fin 4831 × Fin 1024 × Fin 1024)) : Bool :=
  (List.range count).all fun t => [false, true].all fun e =>
    let w := witnesses[t * 2 + e.toNat]!
    checkB ⟨(start + t) % 4831, Nat.mod_lt _ (by decide)⟩ e w.1 w.2.1 w.2.2

public theorem block_sound (start count : ℕ)
    (witnesses : Array (Fin 4831 × Fin 1024 × Fin 1024))
    (h : blockCheck start count witnesses = true)
    (j : Fin 4831) (hs : start ≤ j.val) (ht : j.val < start + count) (e : Bool) :
    Theory.GroupTheory.DoubleCosetTransitions.Covered markedSubgroup representative
      (representative j * middle 0 e * move 0) := by
  have hr : j.val - start < count := by omega
  have he : e ∈ [false, true] := by cases e <;> simp
  have hc := List.all_eq_true.mp
    (List.all_eq_true.mp h (j.val - start) (List.mem_range.mpr hr)) e he
  have hi : (⟨(start + (j.val - start)) % 4831, Nat.mod_lt _ (by decide)⟩ : Fin 4831) = j := by
    apply Fin.ext
    change (start + (j.val - start)) % 4831 = j.val
    omega
  rw [hi] at hc
  exact ⟨_, _, _, subgroupElement_mem _, subgroupElement_mem _, checkB_eq hc⟩

end Held.LocalPairs.PairCoverage.SylowOvergroups.DoubleCosets.Column0Certificate
