module

public import Theory.SpecificGroups.SL2.RootNormalizedNine.Triangular
public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Borel marking independent of rank-one coordinates

A subgroup whose quotient by its two-core has exponent three is triangular
when it is normalized by the full upper root group. Its two-core lies in that
root group by Sylow maximality, and the lower matrix entry of commutator cubes
then vanishes. Sylow conjugacy makes this conclusion valid for every chosen
SL₂ equivalence. A cubic element in the resulting Borel forces even field
degree. No compatibility with later natural-module coordinates is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49 after (k), printed p.1144.
-/

public section

open Subgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne
variable {D E : Type*} [Group D] [Group E]

theorem cubes_mem_core_of_card (hc : Nat.card (D ⧸ pCore 2 D) = 3) (x : D) :
    x ^ 3 ∈ pCore 2 D := by
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' (pCore 2 D)) (x ^ 3) = 1
  rw [map_pow, ← hc]
  exact pow_card_eq_one'

theorem cubes_mem_core_of_surjective (f : D →* E) (hf : Function.Surjective f)
    (hc : ∀ x : D, x ^ 3 ∈ pCore 2 D) (y : E) : y ^ 3 ∈ pCore 2 E := by
  obtain ⟨x, rfl⟩ := hf y
  have hle : (pCore 2 D).map f ≤ pCore 2 E :=
    le_sSup ⟨(inferInstance : (pCore 2 D).Normal).map f hf, pCore_isPGroup.map f⟩
  rw [← map_pow]
  exact hle (mem_map_of_mem f (hc x))

theorem core_le_sylow_of_normalized (C : Subgroup D) (S : Sylow 2 D)
    (hn : (S : Subgroup D) ≤ normalizer (C : Set D)) : C.pCoreIn 2 ≤ S := by
  have hN : (S : Subgroup D) ≤ normalizer (C.pCoreIn 2 : Set D) :=
    hn.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  exact sup_eq_left.mp (S.is_maximal'
    (S.isPGroup'.to_sup_of_normal_right' (isPGroup_pCoreIn 2 C) hN) le_sup_left)

variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem root_normalized_le_borel (C : Subgroup (SL(2,F))) (hq : 2 < Nat.card F)
    (hn : upperUnipotent F ≤ normalizer (C : Set _))
    (hc : ∀ c : C, c ^ 3 ∈ pCore 2 C) : C ≤ rankOneBorel F := by
  apply RootNormalizedNine.le_borel_of_cubes C hq hn
  intro c hc'
  exact core_le_sylow_of_normalized C (upperUnipotentSylow F 2) hn
    (mem_map_of_mem C.subtype (hc ⟨c,hc'⟩))

theorem exists_borel_conjugator (C : Subgroup (SL(2,F))) (hq : 2 < Nat.card F)
    (S : Sylow 2 (SL(2,F))) (hn : (S : Subgroup (SL(2,F))) ≤ normalizer (C : Set (SL(2,F))))
    (hc : ∀ c : C, c ^ 3 ∈ pCore 2 C) :
    ∃ g : SL(2,F), ∀ c ∈ C, g * c * g⁻¹ ∈ rankOneBorel F := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SL(2,F)) S (upperUnipotentSylow F 2)
  let a := MulAut.conj g
  have hs : (S : Subgroup (SL(2,F))).map a.toMonoidHom = upperUnipotent F :=
    congrArg Sylow.toSubgroup hg
  have hN : upperUnipotent F ≤ normalizer (C.map a.toMonoidHom : Set _) := by
    rw [← hs]
    exact (map_mono hn).trans (C.le_normalizer_map a.toMonoidHom)
  have hB := root_normalized_le_borel (C.map a.toMonoidHom) hq hN
    (cubes_mem_core_of_surjective (a.subgroupMap C).toMonoidHom (a.subgroupMap C).surjective hc)
  exact ⟨g, fun c hc' => hB (mem_map_of_mem a.toMonoidHom hc')⟩

theorem exists_borel_conjugator_of_equiv [Finite D] (C : Subgroup D)
    (S : Sylow 2 D) (hn : (S : Subgroup D) ≤ normalizer (C : Set D))
    (hc : ∀ c : C, c ^ 3 ∈ pCore 2 C) (hq : 2 < Nat.card F)
    (e : D ≃* SL(2,F)) :
    ∃ g : SL(2,F), ∀ c : C, g * e c * g⁻¹ ∈ rankOneBorel F := by
  have hn' : (S.mapSurjective (f := e.toMonoidHom) e.surjective : Subgroup (SL(2,F))) ≤
      normalizer (C.map e.toMonoidHom : Set (SL(2,F))) :=
    (map_mono hn).trans (C.le_normalizer_map e.toMonoidHom)
  obtain ⟨g,hg⟩ := exists_borel_conjugator (C.map e.toMonoidHom) hq
    (S.mapSurjective (f := e.toMonoidHom) e.surjective) hn'
    (cubes_mem_core_of_surjective (e.subgroupMap C).toMonoidHom (e.subgroupMap C).surjective hc)
  exact ⟨g, fun c => hg _ (mem_map_of_mem e.toMonoidHom c.property)⟩

theorem even_of_borel_cubic {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (x : rankOneBorel F) (hx : orderOf x = 3) : Even n := by
  have hd : 3 ∣ Nat.card (rankOneBorel F) := hx ▸ orderOf_dvd_natCard x
  rw [Nat.card_congr (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.rankOneBorelEquiv F).toEquiv,
    Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.card_borel, hF] at hd
  exact (Nat.BinaryTorusParity.three_dvd_sub_one_iff n).mp
    (((by decide : Nat.Coprime 3 2).pow_right n).dvd_of_dvd_mul_left hd)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne
