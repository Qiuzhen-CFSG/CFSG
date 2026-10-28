module

public import Theory.Representation.AlternatingSevenConjugatePair.SourceLineGeometry.Basic

/-!
# Stabilizer of the distinguished binary line

Two cubic norm relations show that the Sylow-fixed vector is fixed by the
extra pair exchange. Together with the Sylow group this generates the
syntheme stabilizer. Conversely, any further transposition would combine
with one of the three fixed disjoint transpositions to give a three-cycle.
Conjugating the three transpositions therefore forces every vector stabilizer
element to preserve their matching and its remaining point.

Source: Aschbacher–Smith, Lemma 14.4.11, printed p.1011/PDF p.1028.
-/

@[expose] public section
namespace Representation.AlternatingSevenConjugatePair.SourceLineGeometry
open BinaryOffender _root_.Equiv Subgroup
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
open Theory.SpecificGroups.SymmetricSeven.LocalResidualModels

local instance decidableThreeCycleStabilizer (t : S7) : Decidable t.IsThreeCycle :=
  inferInstanceAs (Decidable (t.cycleType = {3}))

private def exchange : S7 := swap 0 2 * swap 1 3
private def rotate : S7 := exchange * (swap 2 4 * swap 3 5)
private def partitionWord (i : Fin 3 × Fin 16) : S7 := rotate ^ i.1.val * sylowWord i.2

private theorem partitionWord_mem (i : Fin 3 × Fin 16) : partitionWord i ∈ synthemeOvergroup :=
  synthemeOvergroup.mul_mem (synthemeOvergroup.pow_mem (by decide) _)
    (sylowWord_mem i.2).2

private theorem partitionWord_injective : Function.Injective partitionWord := by decide +kernel

private theorem partitionWord_surjective : Function.Surjective
    (fun i => (⟨partitionWord i, partitionWord_mem i⟩ : synthemeOvergroup)) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr ?_ |>.2
  refine ⟨fun i j h => partitionWord_injective (congrArg Subtype.val h), ?_⟩
  rw [synthemeOvergroup_card, Nat.card_prod, Nat.card_fin, Nat.card_fin]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem exchange_fixes (D : Pair V) (s : V)
    (hs : ∀ t ∈ standardTwo, D.representation t s = s) :
    D.representation exchange s = s := by
  let u : S7 := swap 1 2
  let t : S7 := swap 0 1 * swap 1 2
  let r : S7 := swap 0 1 * swap 1 3
  have h₀ := orbit_norm D s standardTwo hs t 1 t u
    (by decide) (by decide) (by decide)
  have h₁ := orbit_norm D s standardTwo hs r u t exchange
    (by decide) (by decide) (by decide)
  simp only [map_one, Module.End.one_apply] at h₀
  apply add_right_cancel (b := D.representation t s + D.representation u s)
  calc
    D.representation exchange s + (D.representation t s + D.representation u s) = 0 := by
      simpa only [add_assoc, add_left_comm, add_comm] using h₁
    _ = s + (D.representation t s + D.representation u s) := by
      simpa only [add_assoc] using h₀.symm

/-- Every element of the actual syntheme stabilizer fixes the Sylow-fixed vector. -/
theorem syntheme_fixes (D : Pair V) (s : V)
    (hs : ∀ t ∈ standardTwo, D.representation t s = s) :
    ∀ g ∈ synthemeOvergroup, D.representation g s = s := by
  have hrot : D.representation rotate s = s := by
    change D.representation (exchange * (swap 2 4 * swap 3 5)) s = s
    rw [map_mul, Module.End.mul_apply, hs _ (by decide), exchange_fixes D s hs]
  have hp (n : ℕ) : D.representation (rotate ^ n) s = s := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, map_mul, Module.End.mul_apply, hrot, ih]
  intro g hg
  obtain ⟨i, hi⟩ := partitionWord_surjective ⟨g, hg⟩
  have hi' : partitionWord i = g := congrArg Subtype.val hi
  rw [← hi']
  change D.representation (rotate ^ i.1.val * sylowWord i.2) s = s
  rw [map_mul, Module.End.mul_apply, hs _ (sylowWord_mem _), hp]

private theorem swap_test : ∀ i j : Fin 7, i ≠ j →
    swap i j ≠ a → swap i j ≠ b → swap i j ≠ c →
    (a * swap i j).IsThreeCycle ∨ (b * swap i j).IsThreeCycle ∨
      (c * swap i j).IsThreeCycle := by decide +kernel

private theorem fixed_swap (D : Pair V) (s : V) (hne : s ≠ 0)
    (hs : ∀ t ∈ standardTwo, D.representation t s = s)
    (i j : Fin 7) (hij : i ≠ j) (hf : D.representation (swap i j) s = s) :
    swap i j = a ∨ swap i j = b ∨ swap i j = c := by
  by_contra hn
  have ha : swap i j ≠ a := fun h => hn (Or.inl h)
  have hb : swap i j ≠ b := fun h => hn (Or.inr (Or.inl h))
  have hc : swap i j ≠ c := fun h => hn (Or.inr (Or.inr h))
  rcases swap_test i j hij ha hb hc with ht | ht | ht
  · exact hne (threeCycle_fixedPointFree D _ ht s (by
      rw [map_mul, Module.End.mul_apply, hf, hs a (by decide)]))
  · exact hne (threeCycle_fixedPointFree D _ ht s (by
      rw [map_mul, Module.End.mul_apply, hf, hs b (by decide)]))
  · exact hne (threeCycle_fixedPointFree D _ ht s (by
      rw [map_mul, Module.End.mul_apply, hf, hs c (by decide)]))

private theorem mem_syntheme_of_swaps (g : S7)
    (h : ∀ i j : Fin 7, swap i j = a ∨ swap i j = b ∨ swap i j = c →
      swap (g i) (g j) = a ∨ swap (g i) (g j) = b ∨ swap (g i) (g j) = c) :
    g ∈ synthemeOvergroup := by
  let P : Finset (Finset (Fin 7)) := {{0,1},{2,3},{4,5}}
  have hp (i j : Fin 7) (hij : i ≠ j)
      (hmem : swap i j = a ∨ swap i j = b ∨ swap i j = c) :
      ({i,j} : Finset (Fin 7)).image g ∈ P := by
    have hs : (swap (g i) (g j)).support = {g i,g j} :=
      Perm.support_swap (g.injective.ne hij)
    rcases h i j hmem with he | he | he
    · have hh := congrArg (fun p : S7 => p.support) he
      rw [hs, show a.support = {2,3} by decide] at hh
      simpa only [Finset.image_insert, Finset.image_singleton, hh] using
        (show ({2,3} : Finset (Fin 7)) ∈ P by decide)
    · have hh := congrArg (fun p : S7 => p.support) he
      rw [hs, show b.support = {4,5} by decide] at hh
      simpa only [Finset.image_insert, Finset.image_singleton, hh] using
        (show ({4,5} : Finset (Fin 7)) ∈ P by decide)
    · have hh := congrArg (fun p : S7 => p.support) he
      rw [hs, show c.support = {0,1} by decide] at hh
      simpa only [Finset.image_insert, Finset.image_singleton, hh] using
        (show ({0,1} : Finset (Fin 7)) ∈ P by decide)
  have hP : P.image (fun t => t.image g) = P := by
    apply Finset.eq_of_subset_of_card_le
    · apply Finset.image_subset_iff.mpr
      intro t ht
      rcases (show t = {0,1} ∨ t = {2,3} ∨ t = {4,5} by simpa [P] using ht) with
        rfl | rfl | rfl
      · exact hp 0 1 (by decide) (Or.inr (Or.inr rfl))
      · exact hp 2 3 (by decide) (Or.inl rfl)
      · exact hp 4 5 (by decide) (Or.inr (Or.inl rfl))
    · rw [Finset.card_image_of_injective _ (Finset.image_injective g.injective)]
  have hu := congrArg (fun Q : Finset (Finset (Fin 7)) => Q.biUnion id) hP
  rw [Finset.image_biUnion] at hu
  have hu' : ({0,1,2,3,4,5} : Finset (Fin 7)).image g = {0,1,2,3,4,5} := by
    simpa [P, Finset.insert_comm] using hu
  have hc := congrArg (fun Q : Finset (Fin 7) => Finset.univ \ Q) hu'
  have hcomp : ({6} : Finset (Fin 7)).image g = {6} := by
    have he : ({6} : Finset (Fin 7)) = Finset.univ \ {0,1,2,3,4,5} := by decide
    rw [he, Finset.image_sdiff _ _ g.injective, Finset.image_univ_of_surjective g.surjective]
    exact hc
  exact ⟨by simpa using hcomp, hP⟩

/-- Exact vector stabilizer, hence exact binary line stabilizer, in the given pair. -/
theorem stabilizer_iff (D : Pair V) (s : V) (hne : s ≠ 0)
    (hs : ∀ t ∈ standardTwo, D.representation t s = s) (g : S7) :
    D.representation g s = s ↔ g ∈ synthemeOvergroup := by
  refine ⟨fun hg => ?_, syntheme_fixes D s hs g⟩
  have hgi : D.representation g⁻¹ s = s := by
    have hh := congrArg (D.representation g⁻¹) hg
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using hh.symm
  apply mem_syntheme_of_swaps g
  intro i j hij
  have hsij : D.representation (swap i j) s = s := by
    rcases hij with he | he | he <;> rw [he] <;> exact hs _ (by decide)
  have hneij : i ≠ j := by
    intro hh
    subst j
    rcases hij with he | he | he <;> simp only [swap_self] at he <;> revert he <;> decide
  apply fixed_swap D s hne hs (g i) (g j) (g.injective.ne hneij)
  have he : g * swap i j * g⁻¹ = swap (g i) (g j) := by
    simpa only [Perm.mul_def, Perm.inv_def, trans_assoc] using symm_trans_swap_trans i j g
  rw [← he, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hgi, hsij, hg]

/-- The third literal residual centralizes the distinguished line. -/
theorem third_fixes_line (D : Pair V) (s : V)
    (hs : ∀ t ∈ standardTwo, D.representation t s = s) :
    line s ≤ fixedSpace D.representation (residual synthemeOvergroup) := by
  apply Submodule.span_le.mpr
  intro v hv
  have hv' : v = s := hv
  subst v
  intro x
  exact syntheme_fixes D s hs x (Subgroup.map_subtype_le _ x.property)

end Representation.AlternatingSevenConjugatePair.SourceLineGeometry
