module

public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.Basic

/-!
# No normal four-group in the four-pair stabilizer

Let P be the actual stabilizer of {01,23,45,67} in S₈. Conjugating by
its pair transpositions, which generate the elementary base of its two-core,
forces every normal subgroup of order four to fix each pair. Indeed a
permutation moving a pair produces a double pair-swap, whose P-orbit has
at least five elements. The same orbit obstruction applied to the sixteen
pair-flip patterns leaves only the identity and the simultaneous four-pair
flip. This contradicts order four.

The finite checks concern eight points, five specified conjugates and
sixteen base patterns; they do not enumerate the subgroup lattice of S₈.
The mate and pair-transport calculations adapt the private constructions
in `A6ShadowTwoLocals.PairStructure`, without changing its public boundary.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the
middle-node exclusion in 15.3.43, printed p.1140. The full pair stabilizer
is the Sylow extension of the component's even pair stabilizer.
-/

public section
open Subgroup Equiv
namespace Theory.SpecificGroups.SymmetricEight.PairFourGroupObstruction
open A6ShadowTwoLocals

private def mate : S8 := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7
private def flip (i : Fin 8) : S8 := swap i (mate i)
private theorem mate_ne : ∀ i : Fin 8, mate i ≠ i := by decide
private theorem same_pair : ∀ i j : Fin 8,
    j.val / 2 = i.val / 2 ↔ j = i ∨ j = mate i := by decide

/-- The elementary base fixes each of the four pairs individually. -/
@[expose] def pairBase : Subgroup S8 where
  carrier := {g | ∀ i, (g i).val / 2 = i.val / 2}
  one_mem' := fun _ => rfl
  mul_mem' {g h} hg hh i := (hg (h i)).trans (hh i)
  inv_mem' {g} hg i := by simpa using (hg (g⁻¹ i)).symm

theorem pairBase_le : pairBase ≤ pairStabilizer := by
  intro g hg i j
  change (g i).val / 2 = (g j).val / 2 ↔ i.val / 2 = j.val / 2
  rw [hg i, hg j]

theorem pairBase_isPGroup : IsPGroup 2 pairBase := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  change (g : S8) ^ 2 = 1
  apply Equiv.ext
  intro i
  simp only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  rcases (same_pair i (g.val i)).mp (g.property i) with h | h
  · rw [h, h]
  · have hpair := (g.property (g.val i)).trans (g.property i)
    rcases (same_pair i (g.val (g.val i))).mp hpair with hh | hh
    · exact hh
    · have he : g.val (g.val i) = g.val i := hh.trans h.symm
      exact False.elim (mate_ne i (h.symm.trans (g.val.injective he)))

theorem pairBase_normalizes : pairStabilizer ≤ normalizer (pairBase : Set S8) := by
  rw [le_normalizer_iff]
  intro g hg b hb i
  change (g (b (g⁻¹ i))).val / 2 = i.val / 2
  simpa using (hg (b (g⁻¹ i)) (g⁻¹ i)).mpr (hb (g⁻¹ i))

/-- The pair flips really belong to the intrinsic two-radical of the local group. -/
theorem pairBase_le_twoCore : pairBase ≤ pairStabilizer.pCoreIn 2 :=
  le_pCoreIn_of_normalizes pairBase_isPGroup pairBase_le pairBase_normalizes

private theorem flip_mem (i : Fin 8) : flip i ∈ pairStabilizer := by
  have hb : flip i ∈ pairBase := by
    have h : ∀ i j : Fin 8, ((flip i) j).val / 2 = j.val / 2 := by decide
    exact h i
  exact (pCoreIn_le 2 pairStabilizer) (pairBase_le_twoCore hb)

private theorem preserves_mate (g : S8) (hg : g ∈ pairStabilizer) (i : Fin 8) :
    g (mate i) = mate (g i) := by
  have hi : (mate i).val / 2 = i.val / 2 :=
    (same_pair i (mate i)).mpr (Or.inr rfl)
  exact ((same_pair (g i) (g (mate i))).mp ((hg _ _).mpr hi)).resolve_left
    (g.injective.ne (mate_ne i))

private theorem conjugate_flip (g : S8) (hg : g ∈ pairStabilizer) (i : Fin 8) :
    g * flip i * g⁻¹ = flip (g i) := by
  unfold flip
  rw [Equiv.mul_swap_eq_swap_mul, mul_inv_cancel_right, preserves_mate g hg]

private def movePair (i j : Fin 8) : S8 :=
  if i.val / 2 = j.val / 2 then swap i j
  else swap i j * swap (mate i) (mate j)
private def crossTransport (i j : Fin 8) : S8 :=
  movePair (movePair i 0 j) 2 * movePair i 0
private theorem cross_mem : ∀ i j : Fin 8, crossTransport i j ∈ pairStabilizer := by
  decide
private theorem cross_action : ∀ i j : Fin 8, i.val / 2 ≠ j.val / 2 →
    crossTransport i j i = 0 ∧ crossTransport i j j = 2 := by decide

private def orbitActor : Fin 5 → S8 :=
  ![1, swap 2 4 * swap 3 5, swap 2 6 * swap 3 7,
    swap 0 4 * swap 1 5, swap 0 6 * swap 1 7]
private def orbitElement (i : Fin 5) : S8 :=
  orbitActor i * (flip 0 * flip 2) * (orbitActor i)⁻¹
private theorem orbitActor_mem : ∀ i, orbitActor i ∈ pairStabilizer := by decide
private theorem orbitElement_injective : Function.Injective orbitElement := by decide

private theorem double_flip_not_mem (V : Subgroup S8) (hc : Nat.card V = 4)
    (hn : pairStabilizer ≤ normalizer (V : Set S8))
    {i j : Fin 8} (hij : i.val / 2 ≠ j.val / 2) : flip i * flip j ∉ V := by
  intro hm
  have h0 : flip 0 * flip 2 ∈ V := by
    have h := (hn (cross_mem i j) _).mp hm
    have he : crossTransport i j * (flip i * flip j) * (crossTransport i j)⁻¹ =
        flip 0 * flip 2 := by
      calc
        _ = (crossTransport i j * flip i * (crossTransport i j)⁻¹) *
            (crossTransport i j * flip j * (crossTransport i j)⁻¹) := by simp [mul_assoc]
        _ = _ := by rw [conjugate_flip _ (cross_mem i j),
          conjugate_flip _ (cross_mem i j), (cross_action i j hij).1, (cross_action i j hij).2]
    exact he ▸ h
  let f : Fin 5 → V := fun k => ⟨orbitElement k, (hn (orbitActor_mem k) _).mp h0⟩
  have hf : Function.Injective f := fun a b h =>
    orbitElement_injective (congrArg Subtype.val h)
  have hcard := Nat.card_le_card_of_injective f hf
  rw [hc, Nat.card_fin] at hcard
  omega

private theorem fixes_pairs (V : Subgroup S8) (hc : Nat.card V = 4)
    (hle : V ≤ pairStabilizer) (hn : pairStabilizer ≤ normalizer (V : Set S8))
    (v : S8) (hv : v ∈ V) (i : Fin 8) : (v i).val / 2 = i.val / 2 := by
  by_contra h
  apply double_flip_not_mem V hc hn h
  have hm := V.mul_mem hv ((hn (flip_mem i) _).mp (V.inv_mem hv))
  have he : v * (flip i * v⁻¹ * (flip i)⁻¹) = flip (v i) * flip i := by
    rw [← mul_assoc, ← mul_assoc, conjugate_flip v (hle hv)]
    congr 1
  exact he ▸ hm

private def basePerm (b : Fin 4 → Bool) : S8 :=
  (if b 0 then flip 0 else 1) * (if b 1 then flip 2 else 1) *
    (if b 2 then flip 4 else 1) * (if b 3 then flip 6 else 1)
private theorem base_even : ∀ b : Fin 4 → Bool, ∀ k : Fin 4,
    basePerm b ⟨2 * k.val, by omega⟩ =
      if b k then mate ⟨2 * k.val, by omega⟩ else ⟨2 * k.val, by omega⟩ := by decide
private theorem base_mem : ∀ b : Fin 4 → Bool, basePerm b ∈ pairStabilizer := by decide
private theorem point_cases : ∀ i : Fin 8, ∃ k : Fin 4,
    i = ⟨2 * k.val, by omega⟩ ∨ i = mate ⟨2 * k.val, by omega⟩ := by decide

private theorem base_of_fixes_pairs (v : S8) (hv : v ∈ pairStabilizer)
    (hf : ∀ i : Fin 8, (v i).val / 2 = i.val / 2) : ∃ b, v = basePerm b := by
  let b : Fin 4 → Bool := fun k => decide (v ⟨2 * k.val, by omega⟩ ≠ ⟨2 * k.val, by omega⟩)
  have he (k : Fin 4) : v ⟨2 * k.val, by omega⟩ = basePerm b ⟨2 * k.val, by omega⟩ := by
    rw [base_even]
    dsimp [b]
    simp only [decide_eq_true_eq]
    split_ifs with h
    · exact h
    · exact ((same_pair _ _).mp (hf _)).resolve_left h
  refine ⟨b, Equiv.ext fun i => ?_⟩
  obtain ⟨k, rfl | rfl⟩ := point_cases i
  · exact he k
  · rw [preserves_mate v hv, preserves_mate _ (base_mem b), he k]

private def baseActor : Fin 3 → S8 :=
  ![swap 0 2 * swap 1 3, swap 0 4 * swap 1 5, swap 0 6 * swap 1 7]
private theorem baseActor_mem : ∀ i, baseActor i ∈ pairStabilizer := by decide
private theorem base_noncentral : ∀ b : Fin 4 → Bool,
    basePerm b = 1 ∨ basePerm b = mate ∨
    ∃ k : Fin 3,
      baseActor k * basePerm b * (baseActor k)⁻¹ * (basePerm b)⁻¹ =
        flip 0 * flip (![2, 4, 6] k) := by
  decide

/-- A normal subgroup of order four cannot occur in the full pair stabilizer. -/
theorem no_normal_four (V : Subgroup S8) (hc : Nat.card V = 4)
    (hle : V ≤ pairStabilizer) (hn : pairStabilizer ≤ normalizer (V : Set S8)) : False := by
  have htwo (v : S8) (hv : v ∈ V) : v = 1 ∨ v = mate := by
    obtain ⟨b, rfl⟩ := base_of_fixes_pairs v (hle hv) (fixes_pairs V hc hle hn v hv)
    rcases base_noncentral b with he | he | ⟨k, he⟩
    · exact Or.inl he
    · exact Or.inr he
    · have hij : (0 : Fin 8).val / 2 ≠ (![2, 4, 6] k : Fin 8).val / 2 := by
        fin_cases k <;> decide
      exact False.elim (double_flip_not_mem V hc hn hij
        (he ▸ V.mul_mem ((hn (baseActor_mem k) _).mp hv) (V.inv_mem hv)))
  let f : V → ({1, mate} : Set S8) := fun v => ⟨v.val, by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using htwo v v.property⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (congrArg (fun x : ({1, mate} : Set S8) => x.val) h)
  have hh := Nat.card_le_card_of_injective f hf
  have ht : Nat.card ({1, mate} : Set S8) = 2 := by
    rw [Nat.card_eq_fintype_card]
    simp only [Fintype.card_ofFinset]
    decide
  rw [hc, ht] at hh
  omega
end Theory.SpecificGroups.SymmetricEight.PairFourGroupObstruction
