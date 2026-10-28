module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.PermutationOvergroups.Coordinates
import Mathlib.Tactic

/-!
# Sylow normalization and its compatible orbits

Every subgroup B between A₇ and S₇ is one of those two groups. The common
partition stabilizer has index 315 in either one, so it is a Sylow two-subgroup.
The sign map computes the order of its even part without enumerating A₇.
Explicit even permutations connect the four-point orbit and the two-point
orbit. Preservation of both partitions proves that these and the singleton
are the exact orbits. Sylow conjugacy inside B retains this same coordinate
choice for the subsequent solvable-overgroup calculation.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.24, printed pp.958–959 (1 March 2004 manuscript).
-/

@[expose] public section
open Equiv Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry.PermutationOvergroups

/-- The sign kernel in the standard group of order sixteen has order eight. -/
theorem standardEvenTwo_card : Nat.card standardEvenTwo = 8 := by
  let f : standardTwo →* ℤˣ := Perm.sign.comp standardTwo.subtype
  have hf : Function.Surjective f := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one f⟩
    · exact ⟨⟨swap 0 1, by decide +kernel⟩, by decide +kernel⟩
  have hi : f.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf,
      Nat.card_congr (Subgroup.topEquiv (G := ℤˣ)).toEquiv, Nat.card_eq_fintype_card]
    decide
  have hc := f.ker.card_mul_index
  rw [hi, standardTwo_card] at hc
  let e : standardEvenTwo ≃ f.ker := {
    toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
    invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr e]
  omega

/-- The four-plus-three subgroup has the order of its actual product action. -/
theorem fourThreeStabilizer_card : Nat.card fourThreeStabilizer = 144 := by
  rw [← Nat.card_congr fourThreeEquiv.toEquiv, Nat.card_prod]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

/-- Index two leaves only the alternating and full symmetric cases. -/
theorem ambient_cases (B : Subgroup S7) (hB : alternatingGroup (Fin 7) ≤ B) :
    B = ⊤ ∨ B = alternatingGroup (Fin 7) := by
  have h := Subgroup.index_dvd_of_le hB
  rw [alternatingGroup.index_eq_two] at h
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h | h
  · exact Or.inl (Subgroup.index_eq_one.mp h)
  · exact Or.inr (Perm.eq_alternatingGroup_of_index_eq_two h)

/-- The common partition stabilizer has the same odd index in both cases. -/
theorem standardTwoIn_index (B : Subgroup S7) (hB : alternatingGroup (Fin 7) ≤ B) :
    (standardTwoIn B).index = 315 := by
  rcases ambient_cases B hB with rfl | rfl
  · have hc : Nat.card (standardTwoIn (⊤ : Subgroup S7)) = 16 := by
      change Nat.card (standardTwo.subgroupOf ⊤) = _
      rw [Nat.card_congr (subgroupOfEquivOfLe (show standardTwo ≤ ⊤ from le_top)).toEquiv]
      exact standardTwo_card
    have h := (standardTwoIn (⊤ : Subgroup S7)).card_mul_index
    rw [hc, Nat.card_congr (Subgroup.topEquiv (G := S7)).toEquiv] at h
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at h
    omega
  · have h := standardEvenTwo.card_mul_index
    rw [standardEvenTwo_card, Nat.card_eq_fintype_card, card_alternatingGroup] at h
    norm_num [Nat.factorial] at h
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 8) h

/-- The standard Sylow subgroup, as an actual subgroup of the supplied B. -/
noncomputable def standardSylow (B : Subgroup S7) (hB : alternatingGroup (Fin 7) ≤ B) :
    Sylow 2 B :=
  ((IsPGroup.of_card (show Nat.card standardTwo = 2 ^ 4 by
    rw [standardTwo_card]; decide)).comap_of_injective B.subtype B.subtype_injective).toSylow
      (by change ¬ 2 ∣ (standardTwoIn B).index; rw [standardTwoIn_index B hB]; decide)

@[simp] theorem standardSylow_coe (B : Subgroup S7)
    (hB : alternatingGroup (Fin 7) ≤ B) :
    (standardSylow B hB : Subgroup B) = standardTwoIn B := rfl

/-- Labels for the source's four-point, two-point, and singleton orbits. -/
def orbitLabel (i : Fin 7) : Fin 3 :=
  if i.val < 4 then 0 else if i.val < 6 then 1 else 2

private def orbitRepresentative (i : Fin 7) : Fin 7 :=
  (![0, 4, 6] : Fin 3 → Fin 7) (orbitLabel i)

private theorem singleton_pairBlock (x : Fin 7) :
    (∀ y, pairBlock y = pairBlock x → y = x) ↔ x = 6 := by
  fin_cases x <;> decide

/-- Permuting the three pairs still fixes the unique singleton. -/
theorem pairStabilizer_fixes_last (g : S7) (hg : g ∈ pairStabilizer) : g 6 = 6 := by
  apply (singleton_pairBlock (g 6)).mp
  intro y hy
  have hh : pairBlock (g (g⁻¹ y)) = pairBlock (g 6) := by
    simpa using hy
  have he : g⁻¹ y = (6 : Fin 7) :=
    (singleton_pairBlock 6).mpr rfl _ ((hg _ _).mp hh)
  have := congrArg g he
  simpa using this

/-- Both partition conditions together preserve all three proposed orbits. -/
theorem standardTwo_preserves_orbitLabel (g : S7) (hg : g ∈ standardTwo)
    (i : Fin 7) : orbitLabel (g i) = orbitLabel i := by
  have hf : (g i).val < 4 ↔ i.val < 4 := by
    constructor
    · intro h
      have hh := (mem_fourThree_coord g⁻¹).mp (fourThreeStabilizer.inv_mem hg.1) (g i) h
      simpa using hh
    · exact (mem_fourThree_coord g).mp hg.1 i
  have hl : (g i).val = 6 ↔ i.val = 6 := by
    have h6 := pairStabilizer_fixes_last g hg.2
    constructor
    · intro h
      exact congrArg Fin.val (g.injective ((Fin.ext h).trans h6.symm))
    · intro h
      exact congrArg Fin.val ((congrArg g (Fin.ext h)).trans h6)
  unfold orbitLabel
  split_ifs <;> first | rfl | omega

private def orbitWitness (i : Fin 7) : S7 :=
  if i = 1 then swap 0 1 * swap 4 5
  else if i = 2 then swap 0 2 * swap 1 3
  else if i = 3 then (swap 0 2 * swap 1 3) * (swap 0 1 * swap 4 5)
  else if i = 5 then swap 0 1 * swap 4 5
  else 1

private theorem orbitWitness_mem (i : Fin 7) :
    orbitWitness i ∈ standardTwo ∧ orbitWitness i ∈ alternatingGroup (Fin 7) := by
  fin_cases i <;> decide +kernel

private theorem orbitWitness_apply (i : Fin 7) :
    orbitWitness i (orbitRepresentative i) = i := by
  fin_cases i <;> decide +kernel

/-- Even witnesses already connect every point with the same orbit label. -/
theorem standardTwoIn_orbit (B : Subgroup S7) (hB : alternatingGroup (Fin 7) ≤ B)
    (x : Fin 7) : MulAction.orbit (standardTwoIn B) x = {y | orbitLabel y = orbitLabel x} := by
  ext y
  constructor
  · rintro ⟨g, rfl⟩
    exact standardTwo_preserves_orbitLabel g.val.val g.property x
  · intro hy
    let w := orbitWitness y * (orbitWitness x)⁻¹
    have hwT : w ∈ standardTwo :=
      standardTwo.mul_mem (orbitWitness_mem y).1 (standardTwo.inv_mem (orbitWitness_mem x).1)
    have hwB : w ∈ B := hB ((alternatingGroup (Fin 7)).mul_mem
      (orbitWitness_mem y).2 ((alternatingGroup (Fin 7)).inv_mem (orbitWitness_mem x).2))
    refine ⟨⟨⟨w, hwB⟩, hwT⟩, ?_⟩
    change w x = y
    have hi : (orbitWitness x)⁻¹ x = orbitRepresentative x := by
      exact (Equiv.symm_apply_eq (orbitWitness x)).mpr (orbitWitness_apply x).symm
    have he : orbitRepresentative x = orbitRepresentative y := by
      unfold orbitRepresentative
      rw [show orbitLabel y = orbitLabel x from hy]
    change orbitWitness y ((orbitWitness x)⁻¹ x) = y
    rw [hi, he, orbitWitness_apply]

/-- The three exact source orbits in zero-based coordinates. -/
theorem standardTwoIn_orbits (B : Subgroup S7) (hB : alternatingGroup (Fin 7) ≤ B) :
    MulAction.orbit (standardTwoIn B) (0 : Fin 7) = {0, 1, 2, 3} ∧
    MulAction.orbit (standardTwoIn B) (4 : Fin 7) = {4, 5} ∧
    MulAction.orbit (standardTwoIn B) (6 : Fin 7) = {6} := by
  simp only [standardTwoIn_orbit B hB]
  constructor
  · ext i; fin_cases i <;> decide
  constructor
  · ext i; fin_cases i <;> decide
  · ext i; fin_cases i <;> decide

/-- Conjugation inside B puts any Sylow subgroup in these same coordinates. -/
theorem sylow_conjugate_standard (B : Subgroup S7) (hB : alternatingGroup (Fin 7) ≤ B)
    (S : Sylow 2 B) :
    ∃ σ : B, (S : Subgroup B).map (MulAut.conj σ).toMonoidHom = standardTwoIn B := by
  obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq B S (standardSylow B hB)
  refine ⟨σ, ?_⟩
  have h := congrArg Sylow.toSubgroup hσ
  have he : (MulDistribMulAction.toMonoidEnd (MulAut B) B) (MulAut.conj σ) =
      (MulAut.conj σ).toMonoidHom := by
    ext x
    rfl
  simpa only [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, he, standardSylow_coe] using h

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry.PermutationOvergroups

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry.PermutationOvergroups

/-- The chosen conjugation has the required three orbits in the actual
seven-point action, and retains the exact Sylow subgroup equality. -/
theorem sylow_compatible_coordinates (B : Subgroup S7)
    (hB : alternatingGroup (Fin 7) ≤ B) (S : Sylow 2 B) :
    ∃ σ : B,
      (S : Subgroup B).map (MulAut.conj σ).toMonoidHom = standardTwoIn B ∧
      ∀ x y : Fin 7,
        (∃ s : S, ((MulAut.conj (σ : S7)) (s.val : S7)) x = y) ↔
          orbitLabel y = orbitLabel x := by
  obtain ⟨σ, hσ⟩ := sylow_conjugate_standard B hB S
  refine ⟨σ, hσ, ?_⟩
  intro x y
  have ho := Set.ext_iff.mp (standardTwoIn_orbit B hB x) y
  rw [MulAction.mem_orbit_iff] at ho
  change (∃ g : standardTwoIn B, (g.val : S7) x = y) ↔
    orbitLabel y = orbitLabel x at ho
  rw [← ho]
  constructor
  · rintro ⟨s, hs⟩
    have hm : (MulAut.conj σ) s.val ∈ standardTwoIn B := by
      rw [← hσ]
      exact mem_map_of_mem _ s.property
    exact ⟨⟨(MulAut.conj σ) s.val, hm⟩, hs⟩
  · rintro ⟨g, hg⟩
    have hm : g.val ∈ (S : Subgroup B).map (MulAut.conj σ).toMonoidHom := by
      rw [hσ]
      exact g.property
    obtain ⟨s, hs, he⟩ := hm
    refine ⟨⟨s, hs⟩, ?_⟩
    change (((MulAut.conj σ) s : B) : S7) x = y
    exact (congrArg (fun b : B => (b : S7) x) he).trans hg

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry.PermutationOvergroups
