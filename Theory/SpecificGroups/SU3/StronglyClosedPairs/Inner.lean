module

public import Theory.SpecificGroups.SU3.StronglyClosedPairs.Coordinates
public import Theory.SpecificGroups.SU3.EvenTwoRank
public import Theory.GroupTheory.SetStrongClosureImage

/-!
# Elementary smaller factors inside binary PSU₃

Conjugate the given Sylow subgroup to the actual Hermitian root image.
Its injective coordinate map and torus action turn strong closure into the
coordinate fusion hypothesis. The smaller factor supplied by that calculation
has first coordinate zero, so its elements square to one. Both containment
and the square identities transport back through the conjugation.

This is the inner-group case of the automorphism-overgroup contract. It does
not assert that factors in an automorphism overgroup are inner.
The coefficient field has order q² and its fixed field has order q = 2ⁿ.

Source: Huppert II.10.12; the terminal model analysis for Aschbacher,
*On finite groups of component type* (1975), Lemma 3.4, pp.94–96.
-/

open Subgroup Theory.GroupTheory BenderSuzuki.External BenderSuzuki.MatrixGroups
open BenderSuzuki.MatrixGroups.HermitianForm.EvenInner
namespace BenderSuzuki.MatrixGroups.HermitianForm.StronglyClosedPairs

private theorem root_factors_nested_elementary {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {q : ℕ} (hcard : Nat.card E = q^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) (hq : 2 < q)
    (B C : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hB : B ≤ rootImage J hJ) (hC : C ≤ rootImage J hJ)
    (hcomm : ⁅B, C⁆ = ⊥)
    (hclosed : IsStronglyClosedSet ((B : Set _) ∪ C) (rootImage J hJ) ⊤) :
    (B ≤ C ∧ ∀ b ∈ B, b ^ 2 = 1) ∨
      (C ≤ B ∧ ∀ c ∈ C, c ^ 2 = 1) := by
  let f := hermitianUnipotentPSU J hJ
  have hc : ∀ z ∈ B.comap f, ∀ w ∈ C.comap f, Commute z w := by
    intro z hz w hw
    apply (root_injective J hJ)
    change f (z*w) = f (w*z)
    rw [map_mul, map_mul]
    exact (mem_centralizer_iff.mp
      ((commutator_eq_bot_iff_le_centralizer.mp hcomm) hz) (f w) hw).symm
  have ht : ∀ (k : Eˣ) z, z ∈ B.comap f ∨ z ∈ C.comap f →
      hermitianTorusAction J k z ∈ B.comap f ∨ hermitianTorusAction J k z ∈ C.comap f := by
    intro k z hz
    have hh := hclosed.2 (f z) hz (hermitianTorusPSU J hJ k)⁻¹ (mem_top _) ?_
    · simpa only [f, inv_inv, projective_torus_action, Subgroup.mem_comap,
        Set.mem_union, SetLike.mem_coe] using hh
    · simp only [f, inv_inv, projective_torus_action]
      exact ⟨hermitianTorusAction J k z, rfl⟩
  rcases Coordinates.factors_nested_elementary J hJ hcard hfixed hq
      (B.comap f) (C.comap f) hc ht with ⟨h, hs⟩ | ⟨h, hs⟩
  · left
    constructor
    · intro x hx
      obtain ⟨z, rfl⟩ := hB hx
      exact h hx
    · intro x hx
      obtain ⟨z, rfl⟩ := hB hx
      rw [← map_pow, hs z hx, map_one]
  · right
    constructor
    · intro x hx
      obtain ⟨z, rfl⟩ := hC hx
      exact h hx
    · intro x hx
      obtain ⟨z, rfl⟩ := hC hx
      rw [← map_pow, hs z hx, map_one]

/-- The smaller commuting strongly closed factor in PSU₃(2ⁿ) is elementary.
Neither a rank premise nor a simplicity premise is needed for this inner case. -/
public theorem inner_factors_nested_elementary {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (B C : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hBP : B ≤ P) (hCP : C ≤ P) (hBC : ⁅B, C⁆ = ⊥)
    (hclosed : IsStronglyClosedSet ((B : Set _) ∪ C) (↑P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) ⊤) :
    (B ≤ C ∧ ∀ b ∈ B, b ^ 2 = 1) ∨
      (C ≤ B ∧ ∀ c ∈ C, c ^ 2 = 1) := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa [Nat.card_eq_fintype_card, pow_mul] using hcard)
  let : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let U := EvenTwoRank.rootSylow J hJ (show 0 < n by omega) hcard hfixed
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) P U
  let e := MulAut.conj g
  have hP : (P : Subgroup _).map e.toMonoidHom = rootImage J hJ :=
    congrArg Sylow.toSubgroup hg
  have hBr : B.map e.toMonoidHom ≤ rootImage J hJ := hP ▸ map_mono hBP
  have hCr : C.map e.toMonoidHom ≤ rootImage J hJ := hP ▸ map_mono hCP
  have hcomm : ⁅B.map e.toMonoidHom, C.map e.toMonoidHom⁆ = ⊥ := by
    rw [← map_commutator, hBC, Subgroup.map_bot]
  have hc : IsStronglyClosedSet
      ((B.map e.toMonoidHom : Set _) ∪ C.map e.toMonoidHom) (rootImage J hJ) ⊤ := by
    have hh := hclosed.image P e.toMonoidHom e.surjective
    rwa [Set.image_union, ← Subgroup.coe_map, ← Subgroup.coe_map, hP] at hh
  have hq : 2 < 2^n := by
    have h4 : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by decide) hn
    omega
  rcases root_factors_nested_elementary J hJ hcard hfixed hq _ _ hBr hCr hcomm hc
      with ⟨h, hs⟩ | ⟨h, hs⟩
  · left
    refine ⟨(Subgroup.map_le_map_iff_of_injective e.injective).mp h, ?_⟩
    intro b hb
    apply e.injective
    rw [map_pow, map_one]
    exact hs (e b) (mem_map_of_mem e.toMonoidHom hb)
  · right
    refine ⟨(Subgroup.map_le_map_iff_of_injective e.injective).mp h, ?_⟩
    intro c hc
    apply e.injective
    rw [map_pow, map_one]
    exact hs (e c) (mem_map_of_mem e.toMonoidHom hc)

end BenderSuzuki.MatrixGroups.HermitianForm.StronglyClosedPairs
