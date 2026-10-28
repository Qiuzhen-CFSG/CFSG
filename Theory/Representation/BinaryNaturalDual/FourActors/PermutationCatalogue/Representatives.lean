module

public import Theory.Representation.BinaryNaturalDual.FourActors.Model
public import Theory.Representation.BinaryNaturalDual.FourActors.PermutationCatalogue.Comparison
public import Theory.ElementaryAbelian.Quotient
public import Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction

/-!
# Three elementary sixteen-subgroups in the eight-point automorphism model

Four independent commuting involutions parametrize each of the three marked
subgroups by the binary four-space. The resulting multiplicative equivalences
prove elementary abelianness and order sixteen. Their point orbits are computed
from these sixteen coordinates: two four-blocks, four pairs, and two pairs plus
a four-block. Orbit cardinality is invariant under conjugation, so the three
representatives are pairwise nonconjugate. The first is identified with the
existing product of the two block Klein groups.

Only small coordinate identities are checked by finite computation; the
multiplication law follows structurally from commuting generators. This module
does not assert exhaustion of the elementary subgroups or a Thompson identity.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.3(3),
printed pp.391–392, PDF pp.402–403.
-/

@[expose] public section

open Equiv Subgroup
namespace BinaryNaturalDual.FourActors.PermutationCatalogue
abbrev Binary := Multiplicative (Fin 4 → ZMod 2)
def generator : Fin 3 → Fin 4 → S := ![
  ![swap 0 1 * swap 2 3, swap 0 2 * swap 1 3,
    swap 4 5 * swap 6 7, swap 4 6 * swap 5 7],
  ![swap 0 1, swap 2 3, swap 4 5, swap 6 7],
  ![swap 0 1, swap 2 3, swap 4 5 * swap 6 7, swap 4 6 * swap 5 7]]
def word (i : Fin 3) (v : Binary) : S :=
  generator i 0 ^ (v.toAdd 0).val * generator i 1 ^ (v.toAdd 1).val *
    generator i 2 ^ (v.toAdd 2).val * generator i 3 ^ (v.toAdd 3).val

private theorem generator_commute : ∀ i j k, Commute (generator i j) (generator i k) := by
  change ∀ i j k, generator i j * generator i k = generator i k * generator i j
  decide +kernel

private theorem generator_pow_add : ∀ (i : Fin 3) (j : Fin 4) (a b : ZMod 2),
    generator i j ^ (a + b).val = generator i j ^ a.val * generator i j ^ b.val := by
  decide +kernel

private theorem word_mul (i : Fin 3) (v w : Binary) :
    word i (v * w) = word i v * word i w := by
  have hc (j k : Fin 4) : Commute
      (generator i j ^ (w.toAdd j).val) (generator i k ^ (v.toAdd k).val) :=
    (generator_commute i j k).pow_pow _ _
  change
    generator i 0 ^ (v.toAdd 0 + w.toAdd 0).val *
      generator i 1 ^ (v.toAdd 1 + w.toAdd 1).val *
      generator i 2 ^ (v.toAdd 2 + w.toAdd 2).val *
      generator i 3 ^ (v.toAdd 3 + w.toAdd 3).val = _
  simp only [generator_pow_add]
  rw [(hc 0 1).mul_mul_mul_comm,
    ((hc 0 2).mul_left (hc 1 2)).mul_mul_mul_comm,
    (((hc 0 3).mul_left (hc 1 3)).mul_left (hc 2 3)).mul_mul_mul_comm]
  rfl

def wordHom (i : Fin 3) : Binary →* S where
  toFun := word i
  map_one' := by simp [word]
  map_mul' := by exact word_mul i

theorem word_injective (i : Fin 3) : Function.Injective (word i) := by
  revert i; decide +kernel

def permutationActor : Fin 3 → Subgroup S := ![permutationA0, permutationA1, permutationA2]
noncomputable def actor (i : Fin 3) : Subgroup M :=
  (permutationActor i).comap permutationEquiv.toMonoidHom

private theorem generator_mem (i : Fin 3) (j : Fin 4) : generator i j ∈ permutationActor i := by
  fin_cases i <;> fin_cases j <;>
    apply Subgroup.subset_closure <;> simp [generator]

private theorem generator_word (i : Fin 3) (j : Fin 4) :
    word i (Multiplicative.ofAdd (Pi.single j 1)) = generator i j := by
  revert i j; decide +kernel

theorem wordHom_range (i : Fin 3) : (wordHom i).range = permutationActor i := by
  apply le_antisymm
  · rintro q ⟨v, rfl⟩
    exact (permutationActor i).mul_mem
      ((permutationActor i).mul_mem
        ((permutationActor i).mul_mem
          ((permutationActor i).pow_mem (generator_mem i 0) _)
          ((permutationActor i).pow_mem (generator_mem i 1) _))
        ((permutationActor i).pow_mem (generator_mem i 2) _))
      ((permutationActor i).pow_mem (generator_mem i 3) _)
  · have hg (j : Fin 4) : generator i j ∈ (wordHom i).range :=
      ⟨Multiplicative.ofAdd (Pi.single j 1), generator_word i j⟩
    fin_cases i <;> apply (Subgroup.closure_le _).mpr <;>
      intro g hg' <;> simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg' <;>
      rcases hg' with rfl | rfl | rfl | rfl
    all_goals first | exact hg 0 | exact hg 1 | exact hg 2 | exact hg 3

/-- Coordinates on the actual permutation subgroups, not merely abstract group tags. -/
noncomputable def binaryPermutationEquiv (i : Fin 3) : Binary ≃* permutationActor i :=
  (MonoidHom.ofInjective (word_injective i)).trans (MulEquiv.subgroupCongr (wordHom_range i))

/-- The eight-point comparison restricted to each actual automorphism subgroup. -/
noncomputable def actorPermutationEquiv (i : Fin 3) : actor i ≃* permutationActor i :=
  MulEquiv.ofBijective (permutationEquiv.toMonoidHom.subgroupComap (permutationActor i))
    ⟨fun _ _ h => Subtype.ext (permutationEquiv.injective (congrArg Subtype.val h)),
      permutationEquiv.toMonoidHom.subgroupComap_surjective_of_surjective _
        permutationEquiv.surjective⟩

instance binary_elementary : IsElementaryAbelian 2 Binary where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by decide +kernel)

instance permutationActor_elementary (i : Fin 3) : IsElementaryAbelian 2 (permutationActor i) :=
  IsElementaryAbelian.of_surjective (binaryPermutationEquiv i).toMonoidHom
    (binaryPermutationEquiv i).surjective

instance actor_elementary (i : Fin 3) : IsElementaryAbelian 2 (actor i) :=
  IsElementaryAbelian.of_surjective (actorPermutationEquiv i).symm.toMonoidHom
    (actorPermutationEquiv i).symm.surjective

theorem permutationActor_card (i : Fin 3) : Nat.card (permutationActor i) = 16 := by
  rw [← Nat.card_congr (binaryPermutationEquiv i).toEquiv, Nat.card_eq_fintype_card]
  decide +kernel

theorem actor_card (i : Fin 3) : Nat.card (actor i) = 16 := by
  rw [Nat.card_congr (actorPermutationEquiv i).toEquiv, permutationActor_card]

instance A0_elementary : IsElementaryAbelian 2 A0 := actor_elementary 0
instance A1_elementary : IsElementaryAbelian 2 A1 := actor_elementary 1
instance A2_elementary : IsElementaryAbelian 2 A2 := actor_elementary 2

theorem A0_card : Nat.card A0 = 16 := actor_card 0
theorem A1_card : Nat.card A1 = 16 := actor_card 1
theorem A2_card : Nat.card A2 = 16 := actor_card 2

/-- Labels of the actual eight-point orbits. For the mixed actor the labels are
`0,1,2` on the blocks `{0,1}`, `{2,3}`, `{4,5,6,7}`. -/
def blockLabel (i : Fin 3) (x : Fin 8) : ℕ :=
  if i = 0 then x.val / 4 else if i = 1 then x.val / 2
  else if x.val < 4 then x.val / 2 else 2

private theorem word_orbit_table : ∀ (i : Fin 3) (x y : Fin 8),
    (∃ v : Binary, word i v x = y) ↔ blockLabel i y = blockLabel i x := by
  decide +kernel

theorem mem_permutationActor_orbit (i : Fin 3) (x y : Fin 8) :
    y ∈ MulAction.orbit (permutationActor i) x ↔ blockLabel i y = blockLabel i x := by
  rw [← word_orbit_table i x y, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨⟨g, hg⟩, h⟩
    rw [← wordHom_range] at hg
    obtain ⟨v, rfl⟩ := hg
    exact ⟨v, h⟩
  · rintro ⟨v, h⟩
    exact ⟨⟨word i v, wordHom_range i ▸ show word i v ∈ (wordHom i).range from ⟨v, rfl⟩⟩, h⟩

theorem permutationActor_orbit (i : Fin 3) (x : Fin 8) :
    MulAction.orbit (permutationActor i) x = {y | blockLabel i y = blockLabel i x} := by
  ext y
  exact mem_permutationActor_orbit i x y

/-- An orbit of an automorphism subgroup in its specified eight-point action. -/
noncomputable def actorOrbit (A : Subgroup M) (x : Fin 8) : Set (Fin 8) :=
  MulAction.orbit (A.map permutationEquiv.toMonoidHom) x

theorem actor_map (i : Fin 3) :
    (actor i).map permutationEquiv.toMonoidHom = permutationActor i :=
  Subgroup.map_comap_eq_self_of_surjective permutationEquiv.surjective _

theorem actor_orbit (i : Fin 3) (x : Fin 8) :
    actorOrbit (actor i) x = {y | blockLabel i y = blockLabel i x} := by
  rw [actorOrbit, actor_map, permutationActor_orbit]

/-- Orbit sizes, with the two pairs distinguished from the four-block for A₂. -/
def orbitSize (i : Fin 3) (x : Fin 8) : ℕ :=
  if i = 0 then 4 else if i = 1 then 2 else if x.val < 4 then 2 else 4

private theorem block_card (i : Fin 3) (x : Fin 8) :
    ({y : Fin 8 | blockLabel i y = blockLabel i x} : Set (Fin 8)).ncard = orbitSize i x := by
  rw [Set.ncard_eq_toFinset_card']
  rw [Set.toFinset_ofPred]
  revert i x
  decide +kernel

theorem permutationActor_orbit_card (i : Fin 3) (x : Fin 8) :
    (MulAction.orbit (permutationActor i) x).ncard = orbitSize i x := by
  rw [permutationActor_orbit, block_card]

theorem actor_orbit_card (i : Fin 3) (x : Fin 8) :
    (actorOrbit (actor i) x).ncard = orbitSize i x := by
  rw [actor_orbit, block_card]

/-- Conjugation carries each actual orbit to its image under the conjugator. -/
theorem orbit_map_conj (H : Subgroup S) (g : S) (x : Fin 8) :
    MulAction.orbit (H.map (MulAut.conj g).toMonoidHom) (g x) =
      g '' MulAction.orbit H x := by
  ext y
  constructor
  · rintro ⟨⟨p, hp⟩, h⟩
    obtain ⟨q, hq, rfl⟩ := hp
    refine ⟨q x, ⟨⟨q, hq⟩, rfl⟩, ?_⟩
    change (g * q * g⁻¹) (g x) = y at h
    simpa using h
  · rintro ⟨z, ⟨⟨q, hq⟩, rfl⟩, rfl⟩
    refine ⟨⟨(MulAut.conj g) q, ⟨q, hq, rfl⟩⟩, ?_⟩
    change (g * q * g⁻¹) (g x) = g (q x)
    simp

theorem orbit_map_conj_card (H : Subgroup S) (g : S) (x : Fin 8) :
    (MulAction.orbit (H.map (MulAut.conj g).toMonoidHom) (g x)).ncard =
      (MulAction.orbit H x).ncard := by
  rw [orbit_map_conj, Set.ncard_image_of_injective _ g.injective]

/-- The three permutation representatives are pairwise nonconjugate. -/
theorem permutationActor_conjugacy_injective (i j : Fin 3) (g : S)
    (h : (permutationActor i).map (MulAut.conj g).toMonoidHom = permutationActor j) :
    i = j := by
  have hc (x : Fin 8) : orbitSize j (g x) = orbitSize i x := by
    have he := orbit_map_conj_card (permutationActor i) g x
    rwa [h, permutationActor_orbit_card, permutationActor_orbit_card] at he
  fin_cases i <;> fin_cases j
  all_goals solve
    | rfl
    | (have he := hc 0; norm_num [orbitSize] at he)
    | (have he := hc 4; norm_num [orbitSize] at he)
    | (have he := hc (g.symm 0); norm_num [orbitSize] at he)
    | (have he := hc (g.symm 4); norm_num [orbitSize] at he)

/-- Distinct marked actors cannot be conjugated in the full automorphism group. -/
theorem actor_conjugacy_injective (i j : Fin 3) (a : M)
    (h : (actor i).map (MulAut.conj a).toMonoidHom = actor j) : i = j := by
  apply permutationActor_conjugacy_injective i j (permutationEquiv a)
  rw [← actor_map i, ← permutation_map_conj, h, actor_map]

theorem actor_conjugate_iff (i j : Fin 3) :
    (∃ a : M, (actor i).map (MulAut.conj a).toMonoidHom = actor j) ↔ i = j := by
  constructor
  · rintro ⟨a, ha⟩
    exact actor_conjugacy_injective i j a ha
  · rintro rfl
    refine ⟨1, ?_⟩
    change (actor i).map (MonoidHom.id M) = actor i
    exact Subgroup.map_id _

/-- The two four-point orbits of A₀, on the specified eight letters. -/
theorem A0_orbit_partition (x : Fin 8) : actorOrbit A0 x =
    if x.val < 4 then {0, 1, 2, 3} else {4, 5, 6, 7} := by
  rw [show A0 = actor 0 from rfl, actor_orbit]
  ext y
  fin_cases x <;> fin_cases y <;> norm_num [blockLabel] <;> decide +kernel

/-- The four two-point orbits of A₁, on the specified eight letters. -/
theorem A1_orbit_partition (x : Fin 8) : actorOrbit A1 x =
    if x.val < 2 then {0, 1} else if x.val < 4 then {2, 3}
    else if x.val < 6 then {4, 5} else {6, 7} := by
  rw [show A1 = actor 1 from rfl, actor_orbit]
  ext y
  fin_cases x <;> fin_cases y <;> norm_num [blockLabel] <;> decide +kernel

/-- The two pairs and four-point orbit of A₂, on the specified eight letters. -/
theorem A2_orbit_partition (x : Fin 8) : actorOrbit A2 x =
    if x.val < 2 then {0, 1} else if x.val < 4 then {2, 3} else {4, 5, 6, 7} := by
  rw [show A2 = actor 2 from rfl, actor_orbit]
  ext y
  fin_cases x <;> fin_cases y <;> norm_num [blockLabel] <;> decide +kernel

open Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction

/-- The A₀ permutation representative is the existing product of block Klein groups. -/
theorem permutationA0_eq_kleinGroup : permutationA0 = kleinGroup := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact ⟨1, 0, rfl⟩
    · exact ⟨2, 0, rfl⟩
    · exact ⟨0, 1, rfl⟩
    · exact ⟨0, 2, rfl⟩
  · rintro g ⟨a, b, rfl⟩
    have ht : ∀ a b : Fin 4, ∃ v : Binary, word 0 v = kleinPerm a b := by
      decide +kernel
    obtain ⟨v, hv⟩ := ht a b
    change kleinPerm a b ∈ permutationActor 0
    rw [← wordHom_range]
    exact ⟨v, hv⟩

end BinaryNaturalDual.FourActors.PermutationCatalogue
