module
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimeDegree
public import Theory.GroupTheory.Perm.PrimeDegreeNormalizer

/-!
# No subgroup of order 56 in the symmetric group on seven letters

A Sylow seven-subgroup acts regularly. The normalizer bound and the Sylow
congruence force eight Sylow seven-subgroups. Their 48 nonidentity elements
leave only eight elements for every point stabilizer, forcing all point
stabilizers to agree and contradicting faithfulness.

This is the seven-point obstruction used for the M₂₃ Cartan calculation in
Aschbacher--Smith, 7.3.4, printed p.699. The counting argument uses the
proved Chapman lemma from the attributed ATLAS prime-degree development.
-/

public section
open Subgroup
namespace SymmetricSeven
theorem subgroup_card_ne_fiftysix (H : Subgroup (Equiv.Perm (Fin 7))) : Nat.card H ≠ 56 := by
  intro hH
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hp (P : Sylow 7 H) : Nat.card P = 7 :=
    P.card_eq_prime_of_dvd_of_not_sq_dvd (by rw [hH]; decide) (by rw [hH]; decide)
  let P : Sylow 7 H := Classical.choice inferInstance
  let : MulAction.IsPretransitive P (Fin 7) :=
    Atlas.GroupTheory.prime_subgroup_pretransitive (G := H) 7 (by simp) P (hp P)
  let : MulAction.IsPretransitive H (Fin 7) := ⟨fun x y => by
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq P x y
    exact ⟨g.val,hg⟩⟩
  obtain ⟨m, hm, hn⟩ := Theory.GroupTheory.prime_degree_normalizer_card H.subtype H.subtype_injective P (hp P)
  have hc := (normalizer (P : Set H)).card_mul_index
  rw [hn, ← P.card_eq_index_normalizer, hH] at hc
  have hmod := card_sylow_modEq_one 7 H
  change Nat.card (Sylow 7 H) % 7 = 1 % 7 at hmod
  have hpos : 0 < Nat.card (Sylow 7 H) := Nat.card_pos
  have hmle := Nat.le_of_dvd (by decide : 0 < 6) hm
  have hcount : Nat.card (Sylow 7 H) = 8 := by
    interval_cases m <;> omega
  have hone := Atlas.GroupTheory.sylow_count_one_of_card (G := H) (X := Fin 7) 7
    (by simp) hp (by rw [hH,hcount])
  omega


end SymmetricSeven
