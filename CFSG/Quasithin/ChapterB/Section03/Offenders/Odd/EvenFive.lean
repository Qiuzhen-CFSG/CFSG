module
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd
public import Theory.Representation.BinaryPermutation.FiveGeometry
/-!
# No even elementary offenders on the deleted five-point module

The proved B.3.2 orbit bound is strict for every nontrivial elementary
subgroup of A5: equality would put a transposition in that even subgroup.
The cardinal form compares an actual action image with its opposite
centralizer, as used in the A5 specialization of F.9.1(e).

Source: Aschbacher–Smith B.3.2(4), pp.83–84; 13.5.7, pp.917–918.
-/
@[expose] public section
open Subgroup BinaryPermutation Representation.BinaryOffender
open Representation.BinaryOffender.OddTransport
namespace CFSG.Quasithin.ChapterB.Offenders.Odd
/-- The deleted binary A5 module has no nontrivial elementary even offender. -/
theorem even_five_rank_lt_fixedCodim (A : Subgroup (Equiv.Perm (Fin 5)))
    (hA : IsElementaryTwo A) (heven : A ≤ alternatingGroup (Fin 5)) :
    rank A < fixedCodim (coreRepresentation (Fin 5)) A := by
  rw [fixedCodim_core_eq_full_odd (Fin 5) (by decide)]
  have hle := rank_le_fixedCodim_full_of_elementary (Or.inl rfl) A hA
  apply lt_of_le_of_ne hle
  intro he
  obtain ⟨a, ha⟩ := ne_bot_iff_exists_ne_one.mp hA.1
  have hane : (a : Equiv.Perm (Fin 5)) ≠ 1 := fun h => ha (Subtype.ext h)
  obtain ⟨i,hi⟩ : ∃ i : Fin 5, a.val i ≠ i := by
    by_contra h
    push Not at h
    exact hane (Equiv.ext h)
  have hs := (pair_orbits_of_fixedCodim_full_eq_rank (Or.inl rfl) A hA he.symm).2
    i (a.val i) (MulAction.mem_orbit_iff.mpr ⟨a,rfl⟩)
  have hev := Equiv.Perm.mem_alternatingGroup.mp (heven hs)
  rw [Equiv.Perm.sign_swap hi.symm] at hev
  exact (by decide : (-1 : ℤˣ) ≠ 1) hev

/-- Cardinal form, ready for comparison with an actual opposite action kernel. -/
theorem even_five_card_fixed_lt (A : Subgroup (Equiv.Perm (Fin 5)))
    (hA : IsElementaryTwo A) (heven : A ≤ alternatingGroup (Fin 5)) :
    Nat.card A * Nat.card (fixedSpace (coreRepresentation (Fin 5)) A) < 16 := by
  have hs := even_five_rank_lt_fixedCodim A hA heven
  have hd := fixedCodim_add_finrank (coreRepresentation (Fin 5)) A
  rw [FiveGeometry.finrank_core] at hd
  rw [hA.card_eq_two_pow_rank, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod, ← pow_add]
  change 2 ^ _ < 2 ^ 4
  exact Nat.pow_lt_pow_right (by decide) (by omega)
end CFSG.Quasithin.ChapterB.Offenders.Odd
