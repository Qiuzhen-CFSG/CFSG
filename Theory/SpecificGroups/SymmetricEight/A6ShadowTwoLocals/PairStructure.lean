module

public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.Basic
public import Mathlib.Algebra.Group.Subgroup.Order

/-!
# Maximality and characteristic two of the four-pair stabilizer

The subgroup fixing each of `{01,23,45,67}` has exponent two, is normalized
by the full pair stabilizer, and contains its ambient centralizer in S₈.
Adjoining the central C₂ factor puts this subgroup inside the relative
two-core and proves the core-centralizer bound.

For maximality, a permutation outside the stabilizer breaks some pair.
Conjugating that pair's transposition produces a cross-pair transposition.
Explicit pair-preserving permutations transport any cross-pair transposition
to `(02)`, so every strict overgroup contains all transpositions and equals S₈.
Surjective pullback along the second projection gives maximality in C₂ × S₈.
The finite checks concern points and explicit permutations, not an enumeration
of the subgroups of S₈.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 2.5.26, printed p.569 (PDF p.586), the pair
stabilizer among the two maximal proper 2-local overgroups in C₂ × S₈.
-/

public section

namespace Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
open Subgroup

/-- The partner of each point in the fixed pair partition. -/
private def mate : S8 :=
  Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5 * Equiv.swap 6 7

private theorem mate_ne : ∀ i : Fin 8, mate i ≠ i := by decide
private theorem same_pair : ∀ i j : Fin 8,
    j.val / 2 = i.val / 2 ↔ j = i ∨ j = mate i := by decide

/-- Permutations fixing each pair individually. -/
private def pairBase : Subgroup S8 where
  carrier := {g | ∀ i, (g i).val / 2 = i.val / 2}
  one_mem' := fun _ => rfl
  mul_mem' {g h} hg hh i := (hg (h i)).trans (hh i)
  inv_mem' {g} hg i := by simpa using (hg (g⁻¹ i)).symm

private theorem pairBase_le : pairBase ≤ pairStabilizer := by
  intro g hg i j
  change (g i).val / 2 = (g j).val / 2 ↔ i.val / 2 = j.val / 2
  rw [hg i, hg j]

private theorem pairBase_square (g : S8) (hg : g ∈ pairBase) : g ^ 2 = 1 := by
  apply Equiv.ext
  intro i
  simp only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  rcases (same_pair i (g i)).mp (hg i) with h | h
  · rw [h, h]
  · have hpair := (hg (g i)).trans (hg i)
    rcases (same_pair i (g (g i))).mp hpair with hh | hh
    · exact hh
    · have he : g (g i) = g i := hh.trans h.symm
      exact False.elim (mate_ne i (h.symm.trans (g.injective he)))

private theorem pairBase_normalizes : pairStabilizer ≤ normalizer (pairBase : Set S8) := by
  rw [le_normalizer_iff]
  intro g hg b hb i
  change (g (b (g⁻¹ i))).val / 2 = i.val / 2
  have hh := (hg (b (g⁻¹ i)) (g⁻¹ i)).mpr (hb (g⁻¹ i))
  simpa using hh

private theorem pairSwap_mem : ∀ i : Fin 8, Equiv.swap i (mate i) ∈ pairBase := by
  change ∀ i j : Fin 8, ((Equiv.swap i (mate i)) j).val / 2 = j.val / 2
  decide

private theorem centralizer_pairBase_le : centralizer (pairBase : Set S8) ≤ pairBase := by
  intro g hg i
  have hc := congrArg (fun f : S8 => f i)
    ((mem_centralizer_iff.mp hg) (Equiv.swap i (mate i)) (pairSwap_mem i))
  have he : Equiv.swap i (mate i) (g i) = g (mate i) := by simpa using hc
  have hn : Equiv.swap i (mate i) (g i) ≠ g i := by
    rw [he]
    exact g.injective.ne (mate_ne i)
  exact (same_pair i (g i)).mpr (Equiv.eq_or_eq_of_swap_apply_ne_self hn)

private def liftedBase : Subgroup X := (⊤ : Subgroup C2).prod pairBase

private theorem liftedBase_le : liftedBase ≤ pairOvergroup :=
  Subgroup.prod_mono le_rfl pairBase_le

private theorem liftedBase_isPGroup : IsPGroup 2 liftedBase := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  change (g.val.1 ^ 2, g.val.2 ^ 2) = (1, 1)
  exact Prod.ext ((by decide : ∀ c : C2, c ^ 2 = 1) g.val.1)
    (pairBase_square _ g.property.2)

private theorem liftedBase_normalizes : pairOvergroup ≤ normalizer (liftedBase : Set X) := by
  rw [le_normalizer_iff]
  intro g hg b hb
  exact ⟨mem_top _, (le_normalizer_iff.mp pairBase_normalizes) g.2 hg.2 b.2 hb.2⟩

private theorem centralizer_liftedBase_le : centralizer (liftedBase : Set X) ≤ liftedBase := by
  intro g hg
  refine ⟨mem_top _, centralizer_pairBase_le ?_⟩
  apply mem_centralizer_iff.mpr
  intro b hb
  exact congrArg Prod.snd ((mem_centralizer_iff.mp hg) (1, b) ⟨mem_top _, hb⟩)

/-- The lifted pair stabilizer has characteristic two, using its intrinsic two-core. -/
theorem pairOvergroup_core_centralizer_le :
    pairOvergroup ⊓ centralizer (pairOvergroup.pCoreIn 2 : Set X) ≤
      pairOvergroup.pCoreIn 2 := by
  have hB := le_pCoreIn_of_normalizes liftedBase_isPGroup liftedBase_le liftedBase_normalizes
  exact inf_le_right.trans ((centralizer_le hB).trans (centralizer_liftedBase_le.trans hB))

/-- Move one point to another, moving their partners with them. -/
private def pairMove (i j : Fin 8) : S8 :=
  if i.val / 2 = j.val / 2 then Equiv.swap i j
  else Equiv.swap i j * Equiv.swap (mate i) (mate j)

private theorem pairMove_mem : ∀ i j : Fin 8, pairMove i j ∈ pairStabilizer := by
  decide

/-- Normalize two points from distinct pairs to `0` and `2`. -/
private def crossTransport (i j : Fin 8) : S8 :=
  pairMove (pairMove i 0 j) 2 * pairMove i 0

private theorem crossTransport_mem (i j : Fin 8) : crossTransport i j ∈ pairStabilizer :=
  pairStabilizer.mul_mem (pairMove_mem _ _) (pairMove_mem _ _)

private theorem crossTransport_apply : ∀ i j : Fin 8, i.val / 2 ≠ j.val / 2 →
    crossTransport i j i = 0 ∧ crossTransport i j j = 2 := by
  decide

private theorem conjugate_swap_mem (H : Subgroup S8) {g : S8} (hg : g ∈ H)
    {i j : Fin 8} (hs : Equiv.swap i j ∈ H) : Equiv.swap (g i) (g j) ∈ H := by
  rw [Equiv.swap_apply_apply]
  exact H.mul_mem (H.mul_mem hg hs) (H.inv_mem hg)

private theorem pairStabilizer_of_mate (g : S8)
    (h : ∀ i, (g (mate i)).val / 2 = (g i).val / 2) : g ∈ pairStabilizer := by
  have hm : ∀ i, g (mate i) = mate (g i) := by
    intro i
    exact ((same_pair (g i) (g (mate i))).mp (h i)).resolve_left
      (g.injective.ne (mate_ne i))
  intro i j
  change (g i).val / 2 = (g j).val / 2 ↔ i.val / 2 = j.val / 2
  rw [same_pair (g j) (g i), same_pair j i, ← hm j,
    g.injective.eq_iff, g.injective.eq_iff]

private theorem cross_swap_mem_of_lt (H : Subgroup S8) (hH : pairStabilizer < H) :
    Equiv.swap (0 : Fin 8) 2 ∈ H := by
  classical
  obtain ⟨g, hg, hgp⟩ := SetLike.exists_of_lt hH
  have hbreak : ∃ i, (g i).val / 2 ≠ (g (mate i)).val / 2 := by
    by_contra! h
    exact hgp (pairStabilizer_of_mate g (fun i => (h i).symm))
  obtain ⟨i, hi⟩ := hbreak
  have hs := conjugate_swap_mem H hg (hH.le (pairBase_le (pairSwap_mem i)))
  have ht := conjugate_swap_mem H (hH.le (crossTransport_mem (g i) (g (mate i)))) hs
  rcases crossTransport_apply _ _ hi with ⟨h0, h2⟩
  simpa only [h0, h2] using ht

private theorem same_pair_swap_mem : ∀ i j : Fin 8, i.val / 2 = j.val / 2 →
    Equiv.swap i j ∈ pairStabilizer := by
  decide

private theorem all_swaps_mem (H : Subgroup S8) (hH : pairStabilizer ≤ H)
    (hs : Equiv.swap (0 : Fin 8) 2 ∈ H) (i j : Fin 8) : Equiv.swap i j ∈ H := by
  by_cases hij : i.val / 2 = j.val / 2
  · exact hH (same_pair_swap_mem i j hij)
  · let g := crossTransport i j
    have hg : g ∈ H := hH (crossTransport_mem i j)
    rcases crossTransport_apply i j hij with ⟨hi, hj⟩
    have hi' : g⁻¹ 0 = i := by rw [← hi]; exact g.symm_apply_apply i
    have hj' : g⁻¹ 2 = j := by rw [← hj]; exact g.symm_apply_apply j
    simpa only [hi', hj'] using conjugate_swap_mem H (H.inv_mem hg) hs

/-- The stabilizer of the four-pair partition is a maximal proper subgroup of S₈. -/
theorem pairStabilizer_isCoatom : IsCoatom pairStabilizer := by
  refine ⟨?_, fun H hH => ?_⟩
  · intro h
    apply pairOvergroup_ne_top
    simp [pairOvergroup, h]
  · have hs := all_swaps_mem H hH.le (cross_swap_mem_of_lt H hH)
    apply top_unique
    intro g _
    exact Equiv.Perm.swap_induction_on g H.one_mem
      (fun f i j _ hf => H.mul_mem (hs i j) hf)

/-- The lifted pair stabilizer is a maximal proper subgroup of C₂ × S₈. -/
theorem pairOvergroup_isCoatom : IsCoatom pairOvergroup := by
  rw [pairOvergroup, Subgroup.top_prod]
  exact Subgroup.isCoatom_comap_of_surjective
    (fun g => ⟨(1, g), rfl⟩) pairStabilizer_isCoatom

end Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
