module

public import Mathlib.GroupTheory.Sylow

/-!
# Weak closure inside the normalizer

If a p-subgroup is weakly closed in a Sylow subgroup, its normalizer contains
no other ambient conjugate of it. The subgroup and any such conjugate
generate a p-group, since the latter normalizes the former. Conjugating
that p-group into the chosen Sylow subgroup makes weak closure apply to
both subgroups.

This supplies the last weak-closure step in Aschbacher–Smith, combined
manuscript of 1 March 2004, Lemma 13.9.10, printed p.973 (PDF p.990).
-/

public section

namespace Sylow

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A weakly closed p-subgroup is the only ambient conjugate of itself
contained in its normalizer. -/
theorem conjugate_eq_of_le_normalizer_of_weakly_closed
    (S : Sylow p G) (B : Subgroup G) (hBS : B ≤ (S : Subgroup G))
    (hweak : ∀ g : G, B.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
      B.map (MulAut.conj g).toMonoidHom = B)
    (g : G) (hg : B.map (MulAut.conj g).toMonoidHom ≤ normalizer (B : Set G)) :
    B.map (MulAut.conj g).toMonoidHom = B := by
  let B' := B.map (MulAut.conj g).toMonoidHom
  have hB : IsPGroup p B := S.isPGroup'.to_le hBS
  have hjoin : IsPGroup p (B ⊔ B' : Subgroup G) :=
    hB.to_sup_of_normal_left' (hB.map (MulAut.conj g).toMonoidHom) hg
  obtain ⟨P, hP⟩ := hjoin.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G P S
  have hS : (B ⊔ B').map (MulAut.conj a).toMonoidHom ≤ (S : Subgroup G) := by
    rw [← ha]
    exact map_mono hP
  have hBa : B.map (MulAut.conj a).toMonoidHom = B :=
    hweak a ((map_mono le_sup_left).trans hS)
  have hB'a : B'.map (MulAut.conj a).toMonoidHom = B := by
    have hle := (map_mono (f := (MulAut.conj a).toMonoidHom)
      (show B' ≤ B ⊔ B' from le_sup_right)).trans hS
    have hcomp : (MulAut.conj a).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (a * g)).toMonoidHom := by
      ext x
      simp [mul_assoc]
    change (B.map (MulAut.conj g).toMonoidHom).map _ ≤ _ at hle
    rw [map_map, hcomp] at hle
    change (B.map (MulAut.conj g).toMonoidHom).map _ = _
    rw [map_map, hcomp]
    exact hweak (a * g) hle
  exact map_injective (MulAut.conj a).injective (hB'a.trans hBa.symm)

end Sylow
