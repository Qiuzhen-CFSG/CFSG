module
public import Theory.SpecificGroups.SU3.StronglyClosedPairs.Inner
public import Theory.SpecificGroups.SU3.BinaryRootFrattini

/-!
# Strongly closed subgroups of the binary unitary Sylow

Torus invariance follows from strong closure. The full-torus weight span
then makes a subgroup with a nonzero first coordinate the whole root group;
the remaining subgroups have square one. Sylow conjugacy transports this
dichotomy to the original Sylow subgroup.

Source: Huppert II.10.12 and the unitary model calculation for
Aschbacher (1975), Lemma 3.4, pp.94–96.
-/

open Subgroup Theory.GroupTheory BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.StronglyClosedPairs
open EvenInner
variable {E : Type*} [Field E] [Finite E] [CharP E 2]
variable (J : HermitianForm 3 E)

/-- A strongly closed subgroup of the root Sylow either has square one on all
its elements or is the whole root Sylow. -/
public theorem root_stronglyClosed_dichotomy
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {q : ℕ} (hq : 2 < q) (hcard : Nat.card E = q^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q)
    (D : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hc : IsStronglyClosedSet (D : Set _) (rootImage J hJ) ⊤) :
    (∀ d ∈ D, d^2 = 1) ∨ D = rootImage J hJ := by
  let f := hermitianUnipotentPSU J hJ
  have ht (k : Eˣ) (z : hermitianUnipotentCoord J) (hz : z ∈ D.comap f) :
      hermitianTorusAction J k z ∈ D.comap f := by
    have hh := hc.2 (f z) hz (hermitianTorusPSU J hJ k)⁻¹ (mem_top _) ?_
    · simpa only [inv_inv, projective_torus_action, mem_comap, SetLike.mem_coe, f] using hh
    · simp only [inv_inv, projective_torus_action, f]
      exact ⟨hermitianTorusAction J k z, rfl⟩
  obtain hsmall | hfull := BinaryRootFrattini.invariant_subgroup J hcard hfixed hq
    (D.comap f) ht
  · left
    intro d hd
    obtain ⟨z, rfl⟩ := hc.1 hd
    have hs := (BinaryRootFrattini.mem_frattini_iff_square_one J hcard hfixed z).mp (hsmall hd)
    rw [← map_pow, hs, map_one]
  · right
    apply le_antisymm (show D ≤ rootImage J hJ from hc.1)
    rintro x ⟨z, rfl⟩
    have hh : z ∈ D.comap f := hfull ▸ mem_top z
    exact hh

omit [CharP E 2] in
/-- The same strongly closed subgroup dichotomy in any actual Sylow subgroup. -/
public theorem sylow_stronglyClosed_dichotomy
    {n : ℕ} (hn : 2 ≤ n) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (D : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hc : IsStronglyClosedSet (D : Set _) (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ⊤) :
    (∀ d ∈ D, d^2 = 1) ∨ D = (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let U := EvenTwoRank.rootSylow J hJ (show 0 < n by omega) hcard hfixed
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) P U
  let e := MulAut.conj g
  have hP : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map e.toMonoidHom = rootImage J hJ := congrArg Sylow.toSubgroup hg
  have hc' := hc.image P e.toMonoidHom e.surjective
  rw [← Subgroup.coe_map, hP] at hc'
  have hq : 2 < 2^n := lt_of_lt_of_le (by decide : 2 < 2^2)
    (Nat.pow_le_pow_right (by decide) hn)
  obtain hs | he := root_stronglyClosed_dichotomy J hJ hq hcard hfixed _ hc'
  · left
    intro d hd
    apply e.injective
    rw [map_pow, map_one]
    exact hs (e d) (mem_map_of_mem e.toMonoidHom hd)
  · right
    exact Subgroup.map_injective e.injective (he.trans hP.symm)

end BenderSuzuki.MatrixGroups.HermitianForm.StronglyClosedPairs
