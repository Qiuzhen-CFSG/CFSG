module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.RootGeneration.RootIdentities
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.RootGeneration.Bruhat
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FieldParameters

/-!
# SU₃ and PSU₃ root generation from Bruhat coverage

This module proves the unitary generation step in Aschbacher–Smith F.1.3(1)
(printed pp.259–260) using a precise matrix factorization: every SU matrix has
form `u * t` or `u * w * t * v`, where `u,v` are standard roots, `t` is in the
standard torus, and `w` is the standard Weyl matrix.

The opposite roots contain the Weyl matrix and torus by explicit words.
Coverage therefore gives opposite-root generation. For `g` outside the root
normalizer, the large cell expresses its conjugate root as a root conjugate
of the opposite root, proving generation. Surjectivity of the actual map
SU → PSU transfers this conclusion to the existing projective root range.

The theorems named `of_bruhat` retain the conditional assembly interfaces.
The final theorems `su_root_generation` and `psu_root_generation` discharge
their matrix-factorization premise using `su_bruhat_coverage`.
The field hypotheses include q = 2; simplicity and perfectness are not used.
-/

open BenderSuzuki BenderSuzuki.MatrixGroups BenderSuzuki.External
open scoped Matrix
namespace CFSG.Quasithin.ChapterF.Source.Unitary

private theorem map_conj_mul {G : Type*} [Group G] (R : Subgroup G) (a b : G) :
    R.map (MulAut.conj (a * b) : G →* G) = (R.map (MulAut.conj b : G →* G)).map (MulAut.conj a : G →* G) := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem generation_of_big_cell {G : Type*} [Group G]
    (R : Subgroup G) (w : G)
    (hop : R ⊔ R.map (MulAut.conj w : G →* G) = ⊤)
    (hcell : ∀ g : G, g ∈ Subgroup.normalizer R ∨
      ∃ u ∈ R, ∃ b ∈ Subgroup.normalizer R, g = u * w * b)
    (g : G) (hg : g ∉ Subgroup.normalizer R) : R ⊔ R.map (MulAut.conj g : G →* G) = ⊤ := by
  obtain h | ⟨u, hu, b, hb, rfl⟩ := hcell g
  · exact (hg h).elim
  have hb' := Subgroup.mem_normalizer_iff_map_conj_eq.mp hb
  have hu' := Subgroup.mem_normalizer_iff_map_conj_eq.mp (R.le_normalizer hu)
  rw [map_conj_mul, hb', map_conj_mul]
  have heq : R ⊔ (R.map (MulAut.conj w : G →* G)).map (MulAut.conj u : G →* G) =
      (R ⊔ R.map (MulAut.conj w : G →* G)).map (MulAut.conj u : G →* G) := by
    rw [Subgroup.map_sup, hu']
  rw [heq, hop]
  exact Subgroup.map_top_of_surjective _ (MulAut.conj u).surjective

private theorem generation_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Surjective f) (R : Subgroup G)
    (hgen : ∀ g : G, g ∉ Subgroup.normalizer R → R ⊔ R.map (MulAut.conj g : G →* G) = ⊤)
    (g : H) (hg : g ∉ Subgroup.normalizer (R.map f)) :
    R.map f ⊔ (R.map f).map (MulAut.conj g : H →* H) = ⊤ := by
  obtain ⟨x, rfl⟩ := hf g
  have hx : x ∉ Subgroup.normalizer R := by
    intro hx
    exact hg (R.le_normalizer_map f (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩))
  have hconj : (R.map (MulAut.conj x : G →* G)).map f =
      (R.map f).map (MulAut.conj (f x) : H →* H) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext y
    simp [MulAut.conj_apply]
  rw [← hconj, ← Subgroup.map_sup, hgen x hx]
  exact Subgroup.map_top_of_surjective _ hf

variable {K : Type*} [Field K] (J : HermitianForm 3 K)
variable (hs : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

/-- The genuine map from SU to its image in PGL. -/
@[expose] public def specialProjective : J.specialSubgroup →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (Matrix.ProjGenLinGroup.mk.comp J.specialSubgroup.subtype).codRestrict _
    (fun g => ⟨g, g.property, rfl⟩)

/-- The actual projective special unitary group is the image of SU. -/
public theorem specialProjective_surjective : Function.Surjective (specialProjective J) := by
  rintro ⟨g, M, hM, rfl⟩
  exact ⟨⟨M, hM⟩, rfl⟩

/-- The genuine projective map agrees with the existing root homomorphism. -/
public theorem specialProjective_root :
    (specialProjective J).comp (hermitianUnipotentSU J hs) =
      hermitianUnipotentPSU J hs := rfl

/-- The explicit PSU root range is the image of the explicit SU root range. -/
public theorem specialProjective_root_range :
    (hermitianUnipotentSU J hs).range.map (specialProjective J) =
      (hermitianUnipotentPSU J hs).range := by
  rw [← MonoidHom.range_comp, specialProjective_root]


/-- Bruhat coverage and the explicit opposite-root words generate all SU. -/
public theorem su_opposite_generation_of_bruhat [Finite K] [CharP K 2] (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hbruhat : ∀ g : J.specialSubgroup,
      (∃ u k, g = hermitianUnipotentSU J hs u * hermitianTorusSU J hs k) ∨
      (∃ u k v, g = hermitianUnipotentSU J hs u * hermitianWeylSU J hs *
        hermitianTorusSU J hs k * hermitianUnipotentSU J hs v)) :
    (hermitianUnipotentSU J hs).range ⊔
      (hermitianUnipotentSU J hs).range.map (MulAut.conj (hermitianWeylSU J hs)) = ⊤ := by
  let H := (hermitianUnipotentSU J hs).range ⊔
    (hermitianUnipotentSU J hs).range.map (MulAut.conj (hermitianWeylSU J hs))
  have hu (u : hermitianUnipotentCoord J) : hermitianUnipotentSU J hs u ∈ H :=
    Subgroup.mem_sup_left ⟨u, rfl⟩
  have ht (k : Kˣ) : hermitianTorusSU J hs k ∈ H :=
    su_torus_mem_opposite_join J hs q hcard hfixed k
  have hw : hermitianWeylSU J hs ∈ H := su_weyl_mem_opposite_join J hs
  apply top_unique
  intro g _
  obtain ⟨u, k, rfl⟩ | ⟨u, k, v, rfl⟩ := hbruhat g
  · exact H.mul_mem (hu u) (ht k)
  · exact H.mul_mem (H.mul_mem (H.mul_mem (hu u) hw) (ht k)) (hu v)

/-- Conditional on Bruhat coverage, any two distinct conjugate SU root groups generate SU. -/
public theorem su_root_generation_of_bruhat [Finite K] (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hbruhat : ∀ g : J.specialSubgroup,
      (∃ u k, g = hermitianUnipotentSU J hs u * hermitianTorusSU J hs k) ∨
      (∃ u k v, g = hermitianUnipotentSU J hs u * hermitianWeylSU J hs *
        hermitianTorusSU J hs k * hermitianUnipotentSU J hs v))
    (g : J.specialSubgroup)
    (hg : g ∉ Subgroup.normalizer (hermitianUnipotentSU J hs).range) :
    (hermitianUnipotentSU J hs).range ⊔
      (hermitianUnipotentSU J hs).range.map (MulAut.conj g) = ⊤ := by
  let : CharP K 2 := charP_two n hn hcard
  have hop := su_opposite_generation_of_bruhat J hs (2 ^ n) hcard
    (fixed_card J n hn hcard hconj) hbruhat
  apply generation_of_big_cell _ (hermitianWeylSU J hs) hop _ g hg
  intro x
  let R := (hermitianUnipotentSU J hs).range
  have hu (u : hermitianUnipotentCoord J) :
      hermitianUnipotentSU J hs u ∈ Subgroup.normalizer R := R.le_normalizer ⟨u, rfl⟩
  obtain ⟨u, k, rfl⟩ | ⟨u, k, v, rfl⟩ := hbruhat x
  · left
    apply Subgroup.mul_mem
    · exact hu u
    · exact su_torus_mem_root_normalizer J hs k
  · refine Or.inr ⟨hermitianUnipotentSU J hs u, ⟨u, rfl⟩,
      hermitianTorusSU J hs k * hermitianUnipotentSU J hs v, ?_, mul_assoc _ _ _⟩
    apply Subgroup.mul_mem
    · exact su_torus_mem_root_normalizer J hs k
    · exact hu v

/-- The SU generation argument descends through the genuine projective map. -/
public theorem psu_root_generation_of_bruhat [Finite K] (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (hbruhat : ∀ g : J.specialSubgroup,
      (∃ u k, g = hermitianUnipotentSU J hs u * hermitianTorusSU J hs k) ∨
      (∃ u k v, g = hermitianUnipotentSU J hs u * hermitianWeylSU J hs *
        hermitianTorusSU J hs k * hermitianUnipotentSU J hs v))
    (g : ProjectiveSpecialUnitaryMatrixGroup J)
    (hg : g ∉ Subgroup.normalizer (hermitianUnipotentPSU J hs).range) :
    (hermitianUnipotentPSU J hs).range ⊔
      (hermitianUnipotentPSU J hs).range.map (MulAut.conj g) = ⊤ := by
  rw [← specialProjective_root_range J hs] at hg ⊢
  exact generation_map (specialProjective J) (specialProjective_surjective J)
    (hermitianUnipotentSU J hs).range
    (su_root_generation_of_bruhat J hs n hn hcard hconj hbruhat) g hg

/-- Any two distinct conjugate standard root groups generate the actual SU₃.
The fixed-field parameter is `2 ^ n`, including `n = 1`. -/
public theorem su_root_generation [Finite K] (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (g : J.specialSubgroup)
    (hg : g ∉ Subgroup.normalizer (hermitianUnipotentSU J hs).range) :
    (hermitianUnipotentSU J hs).range ⊔
      (hermitianUnipotentSU J hs).range.map (MulAut.conj g) = ⊤ :=
  su_root_generation_of_bruhat J hs n hn hcard hconj (su_bruhat_coverage J hs) g hg

/-- Any two distinct conjugate standard root groups generate the actual PSU₃,
via the genuine projective map from SU₃. This includes fixed-field order two. -/
public theorem psu_root_generation [Finite K] (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card K = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (g : ProjectiveSpecialUnitaryMatrixGroup J)
    (hg : g ∉ Subgroup.normalizer (hermitianUnipotentPSU J hs).range) :
    (hermitianUnipotentPSU J hs).range ⊔
      (hermitianUnipotentPSU J hs).range.map (MulAut.conj g) = ⊤ :=
  psu_root_generation_of_bruhat J hs n hn hcard hconj (su_bruhat_coverage J hs) g hg

end CFSG.Quasithin.ChapterF.Source.Unitary
