module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Assembly

/-!
# The original pure-point Sylow marking

The action quotient detects normalization of the literal natural summand.
Consequently H.9's marked fixed line identifies C_T(w) with the original
T₁ = T ∩ N_G(V₁). This identification does not assert ambient Sylow control.
Source: Aschbacher--Smith H.9.1(3) and 12.1.4--5, pp.390,790--791.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

namespace SourceModel
variable (S : B.SourceModel)

/-- The normalizer preimage retains the given natural coordinate summand. -/
theorem naturalNormalizer_comap :
    S.setup.naturalNormalizer.comap B.actionProjection =
      (normalizer (B.naturalSummand : Set G)).subgroupOf (normalizer (L : Set G)) := by
  ext m
  have hact (u : Additive (componentOrbit V (T : Subgroup G))) :
      ((S.setup.representation (B.actionProjection m) u).toMul : G) =
        (m : G) * (u.toMul : G) * (m : G)⁻¹ := by
    rw [S.representation_eq]
    exact B.quotientAction_projection_apply m u.toMul
  have hmem (u : Additive (componentOrbit V (T : Subgroup G))) :
      u ∈ S.setup.natural ↔ (u.toMul : G) ∈ B.naturalSummand :=
    (S.natural_marking u.toMul).trans (B.mem_naturalSummand u.toMul).symm
  change (∀ u, S.setup.representation (B.actionProjection m) u ∈ S.setup.natural ↔
    u ∈ S.setup.natural) ↔ (m : G) ∈ normalizer (B.naturalSummand : Set G)
  constructor
  · intro hm
    apply mem_normalizer_fintype
    intro x hx
    let u : componentOrbit V (T : Subgroup G) := ⟨x, B.naturalSummand_le hx⟩
    have hu := (hmem (S.setup.representation (B.actionProjection m) (Additive.ofMul u))).mp
      ((hm _).mpr ((hmem (Additive.ofMul u)).mpr hx))
    rwa [hact] at hu
  · intro hm u
    rw [hmem, hmem, hact]
    exact ((mem_normalizer_iff.mp hm) (u.toMul : G)).symm

/-- H.9 identifies the actual C_T(w), without changing the Sylow marking. -/
theorem marked_centralizer_eq
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (w : componentOrbit V (T : Subgroup G)) (hw : w ≠ 1)
    (hp : (B.coordinates w).toAdd.2 = 0)
    (hfix : (⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
      S.setup.naturalFixed (S.setup.naturalSylowNormalizer
        ((T.subtype hTM).mapSurjective B.actionProjection_surjective))) :
    (T : Subgroup G) ⊓ centralizer ({(w : G)} : Set G) =
      (T : Subgroup G) ⊓ normalizer (B.naturalSummand : Set G) := by
  let P := (T.subtype hTM).mapSurjective B.actionProjection_surjective
  have he := (S.setup.pure_sylow P
    ⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ hw hfix).1
  apply le_antisymm
  · intro t ht
    let m : normalizer (L : Set G) := ⟨t, hTM ht.1⟩
    have hm : B.actionProjection m ∈ (P : Subgroup _) := mem_map_of_mem _ ht.1
    have hc : B.actionProjection m ∈ S.setup.stabilizer (Additive.ofMul w) := by
      change m ∈ (S.setup.stabilizer (Additive.ofMul w)).comap B.actionProjection
      rw [S.stabilizer_comap]
      exact ht.2
    have hn := (show B.actionProjection m ∈ S.setup.naturalSylowNormalizer P from he ▸ ⟨hm, hc⟩).2
    have hn' : m ∈ S.setup.naturalNormalizer.comap B.actionProjection := hn
    rw [S.naturalNormalizer_comap] at hn'
    exact ⟨ht.1, hn'⟩
  · intro t ht
    let m : normalizer (L : Set G) := ⟨t, hTM ht.1⟩
    have hm : B.actionProjection m ∈ (P : Subgroup _) := mem_map_of_mem _ ht.1
    have hn : B.actionProjection m ∈ S.setup.naturalNormalizer := by
      change m ∈ S.setup.naturalNormalizer.comap B.actionProjection
      rw [S.naturalNormalizer_comap]
      exact ht.2
    have hc := (show B.actionProjection m ∈ (P : Subgroup _) ⊓
      S.setup.stabilizer (Additive.ofMul w) from he.symm ▸ ⟨hm, hn⟩).2
    have hc' : m ∈ (S.setup.stabilizer (Additive.ofMul w)).comap B.actionProjection := hc
    rw [S.stabilizer_comap] at hc'
    exact ⟨ht.1, hc'⟩

end SourceModel
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The chosen-module form of the original T₁ marking and relative Sylow theorem. -/
theorem doubleNatural_marked_pure_relative_sylow_of_many
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G),
      w ≠ 1 → ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w, (S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      (T : Subgroup G) ⊓ centralizer ({(w : G)} : Set G) =
        (T : Subgroup G) ⊓ normalizer (B.naturalSummand : Set G) ∧
      Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (B.naturalSummand : Set G))
        (normalizer (L : Set G) ⊓ centralizer ({(w : G)} : Set G)) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix
  have he := S.marked_centralizer_eq D.sylow_normalizes_component w hw hp hfix
  exact ⟨he, he ▸ D.doubleNatural_relative_pure_sylow_of_many h hmany B S w hw hp hfix⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
