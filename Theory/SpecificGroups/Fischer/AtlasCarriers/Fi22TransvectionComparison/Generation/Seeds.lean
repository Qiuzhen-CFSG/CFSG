module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.SmallBase

/-!
# Six certified commuting roots for the Fi22 Schreier words

The six labels below are fixed by A. More importantly, their actual shared
conjugate words commute with A: we check this on the faithful 48 coordinates
and apply the proved equality criterion. Their generated subgroup therefore
lies in `commutingConjugateSubgroup`, independently of any equivariance,
coverage, or generation hypothesis.

These are inputs for the remaining Schreier membership certificates; their
generation of the full centralizer is not asserted here. The signed-word
lemma supplies literal products that a certificate may use.

Source: ATLAS F22G1-p3510B0 and GLS3 Table 5.3t, including the conjugation-action
paragraph in `refs/KGroup/GLS3/Chapter5(sec3-).tex`. Exploratory GAP uses one-based
labels [2, 11, 14, 20, 23, 32]; these definitions use the corresponding zero-based
labels and the existing left-action `conjugateAt` words.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation
open KernelCertificate SmallBase

/-- Six of the fixed shared root labels. -/
def seedIndex (k : Fin 6) : Fin 3510 := #[1, 10, 13, 19, 22, 31][k.val]!

/-- The exact shared conjugate, as an element of the actual carrier. -/
def seed (k : Fin 6) : Carrier := conjugateAt (seedIndex k)

theorem seedIndex_fixed (k : Fin 6) : inclusion atlasA (seedIndex k) = seedIndex k := by
  have h : ∀ k : Fin 6, fastA (seedIndex k) = seedIndex k := by decide +kernel
  rw [inclusion_atlasA, generatorA_apply_eq_fastA]
  exact h k

private def seedCheck (k : Fin 6) (n : Nat) : Bool :=
  let i : Fin 48 := ⟨n % 48, Nat.mod_lt _ (by decide)⟩
  decide (rootAction (seedIndex k) (fastA (basePoint i)) =
    fastA (rootAction (seedIndex k) (basePoint i)))

set_option maxRecDepth 4096 in
private theorem seedCheck_all :
    ∀ k : Fin 6, BitNetwork.check (seedCheck k) 0 48 = true := by
  decide +kernel

/-- Direct commutation certificates, with no labeling-equivariance premise. -/
theorem seed_centralizes (k : Fin 6) : seed k ∈ centralizerA := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply ext_of_first48
  intro i
  have h := BitNetwork.check_sound (seedCheck k) 0 48 (seedCheck_all k) i.val
    (Nat.zero_le _) i.isLt
  have hi : rootAction (seedIndex k) (fastA (basePoint i)) =
      fastA (rootAction (seedIndex k) (basePoint i)) := by
    simpa only [seedCheck, Nat.mod_eq_of_lt i.isLt, decide_eq_true_eq] using h
  simpa only [seed, map_mul, Equiv.Perm.mul_apply, inclusion_atlasA,
    ← rootAction_eq, generatorA_apply_eq_fastA] using hi

/-- Each seed is one of the generators of the actual commuting-conjugate subgroup. -/
theorem seed_mem (k : Fin 6) : seed k ∈ commutingConjugateSubgroup := by
  exact ⟨⟨seed k, seed_centralizes k⟩,
    Subgroup.subset_closure (conjugateAt_isConj (seedIndex k)), rfl⟩

/-- A small candidate subgroup for the remaining edge certificates. -/
def seedSubgroup : Subgroup Carrier := Subgroup.closure (Set.range seed)

theorem seedSubgroup_le : seedSubgroup ≤ commutingConjugateSubgroup := by
  rw [seedSubgroup, Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  exact seed_mem k

/-- A signed product of the six literal conjugate words; true means inverse. -/
def seedWord (w : List (Fin 6 × Bool)) : Carrier :=
  (w.map (fun kb => if kb.2 then (seed kb.1)⁻¹ else seed kb.1)).prod

theorem seedWord_mem (w : List (Fin 6 × Bool)) : seedWord w ∈ commutingConjugateSubgroup := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨⟨k, b⟩, _, rfl⟩ := List.mem_map.mp hg
  cases b
  · exact seed_mem k
  · exact Subgroup.inv_mem _ (seed_mem k)

/-- Edge equality against a signed seed word discharges the membership obligation. -/
theorem schreierEdge_mem_of_seedWord (s : Carrier) (x : Fin 3510)
    (w : List (Fin 6 × Bool))
    (h : ∀ i : Fin 48,
      inclusion (seedWord w) (basePoint i) =
        transportInverseAction (inclusion s x)
          (inclusion s (transportAction x (basePoint i)))) :
    (pointTransport (inclusion s x))⁻¹ * s * pointTransport x ∈
      commutingConjugateSubgroup := by
  rw [schreierEdge_eq_of_first48 s x (seedWord w) h]
  exact seedWord_mem w

end Sporadic.Fischer.Fi22.TransvectionComparison.Generation
