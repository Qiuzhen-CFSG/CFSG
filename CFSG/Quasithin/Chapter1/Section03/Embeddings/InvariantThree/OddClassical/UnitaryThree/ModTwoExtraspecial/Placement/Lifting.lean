module

public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Mathlib.GroupTheory.Sylow

/-!
# The full special-unitary preimage of the local product

The natural projective map has central three-group kernel. Its full preimage
therefore preserves solvability and lifts a nonabelian three-subgroup to a
nonabelian three-subgroup. Surjectivity on Sylow subgroups supplies a full
ambient Sylow two-subgroup in the preimage. No order or exponent of the
projective complement is ascribed to its lift.

These are the central-cover steps preceding the solvable representation
argument in GLS3, proof of Theorem 6.5.3(a)–(d).
-/

public section
open Subgroup BenderSuzuki.MatrixGroups
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement

variable {E : Type*} [Field E] (J : HermitianForm 3 E)

/-- Centrality of the scalar kernel preserves solvability on taking preimages. -/
theorem projective_preimage_solvable (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hH : Group.IsSolvable H) : Group.IsSolvable (H.comap J.specialToProjective) := by
  let _ := hH
  let _ : Group.IsSolvable J.specialToProjective.ker := Group.isSolvable_of_comm (by
    intro a b
    apply Subtype.ext
    exact (mem_center_iff.mp (J.specialToProjective_ker_le_center a.property) b.val).symm)
  exact isSolvable_comap_of_solvable_ker J.specialToProjective H

/-- A nonabelian three-subgroup has a nonabelian three-group preimage. -/
theorem projective_preimage_nonabelian_three_subgroup
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hU : ∃ U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
      U ≤ H ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U) :
    ∃ U : Subgroup J.specialSubgroup,
      U ≤ H.comap J.specialToProjective ∧ IsPGroup 3 U ∧ ¬ IsMulCommutative U := by
  obtain ⟨U, hUH, hUp, hUa⟩ := hU
  have hker : IsPGroup 3 J.specialToProjective.ker :=
    fun x => ⟨1, by simpa using J.specialToProjective_ker_cube x⟩
  refine ⟨U.comap J.specialToProjective, comap_mono hUH,
    hUp.comap_of_ker_isPGroup _ hker, ?_⟩
  intro ha
  let _ := ha
  apply hUa
  refine ⟨⟨fun a b => ?_⟩⟩
  obtain ⟨x, hx⟩ := J.specialToProjective_surjective a.val
  obtain ⟨y, hy⟩ := J.specialToProjective_surjective b.val
  have hxU : x ∈ U.comap J.specialToProjective := by
    change J.specialToProjective x ∈ U
    rw [hx]
    exact a.property
  have hyU : y ∈ U.comap J.specialToProjective := by
    change J.specialToProjective y ∈ U
    rw [hy]
    exact b.property
  have hc := congrArg (fun z : U.comap J.specialToProjective =>
    J.specialToProjective z.val) (mul_comm (⟨x, hxU⟩ : U.comap J.specialToProjective) ⟨y, hyU⟩)
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, map_mul, hx, hy] using hc

variable [Finite E]

/-- A full projective Sylow subgroup lifts to a full special-unitary Sylow subgroup. -/
theorem projective_preimage_contains_sylow (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hTH : (T : Subgroup _) ≤ H) :
    ∃ S : Sylow 2 J.specialSubgroup, (S : Subgroup _) ≤ H.comap J.specialToProjective := by
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective J.specialToProjective_surjective 2 T
  refine ⟨S, map_le_iff_le_comap.mp ?_⟩
  change (S.mapSurjective J.specialToProjective_surjective : Subgroup _) ≤ H
  rw [hS]
  exact hTH
/-- The central three-kernel introduces no prime divisors other than three. -/
theorem projective_preimage_prime_divisors (H : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hH : ∀ r : ℕ, r.Prime → r ∣ Nat.card H → r = 2 ∨ r = 3) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card (H.comap J.specialToProjective) → r = 2 ∨ r = 3 := by
  let f := J.specialToProjective.comp (H.comap J.specialToProjective).subtype
  have hk : IsPGroup 3 f.ker :=
    (show IsPGroup 3 J.specialToProjective.ker from
      fun x => ⟨1, by simpa using J.specialToProjective_ker_cube x⟩).comap_subtype
  have hf : f.range = H := by
    rw [MonoidHom.range_comp, range_subtype]
    exact map_comap_eq_self_of_surjective J.specialToProjective_surjective H
  have hcard : Nat.card f.ker * Nat.card H = Nat.card (H.comap J.specialToProjective) := by
    simpa only [index_ker, hf] using f.ker.card_mul_index
  intro r hr hd
  rw [← hcard] at hd
  rcases hr.dvd_mul.mp hd with hd | hd
  · obtain ⟨n, hn⟩ := hk.exists_card_eq
    rw [hn] at hd
    exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp (hr.dvd_of_dvd_pow hd))
  · exact hH r hr hd

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoExtraspecial.Placement
