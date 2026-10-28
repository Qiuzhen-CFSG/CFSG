module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Contracts

/-!
# Faithfulness of each original coordinate summand

An element fixing the natural summand belongs to its normalizer, which
H.9 identifies with the inner layer. The given natural action detects it
there. Conjugation by the source outer interchange proves the dual case.
Lifting these facts through the actual normalizer action quotient shows
that fixing either summand fixes the whole doubled orbit.

This discharges the two action-kernel equalities used in 12.1.6; it
requires no ambient point-centralizer or weak-closure conclusion.
Source: Aschbacher--Smith H.9.1 and 12.1.6, printed pp.389--390,791.
-/

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup
variable {n : ℕ} {M E : Type*} [Group M] [AddCommGroup E] [Module (ZMod 2) E]
  (S : SourceSetup n M E)

private theorem eq_one_of_fixes_natural (a : M)
    (hf : ∀ u ∈ S.natural, S.representation a u = u) : a = 1 := by
  have hn : a ∈ S.naturalNormalizer := by
    change ∀ u, S.representation a u ∈ S.natural ↔ u ∈ S.natural
    intro u
    constructor
    · intro hu
      have he : S.representation a u = u := (S.linearAction a).injective (hf _ hu)
      rwa [he] at hu
    · intro hu
      rwa [hf u hu]
  rw [S.naturalNormalizer_eq_layer] at hn
  have he : S.layer ⟨a, hn⟩ = 1 := by
    apply LinearEquiv.ext
    intro x
    have hh := S.natural_action ⟨a, hn⟩ x
    rw [hf _ (S.naturalCoordinates.symm x).property] at hh
    have heq : S.naturalCoordinates.symm x =
        S.naturalCoordinates.symm (S.layer ⟨a, hn⟩ x) := Subtype.ext hh
    have hh' := congrArg S.naturalCoordinates heq
    simpa only [LinearEquiv.apply_symm_apply, LinearEquiv.coe_one, id_eq] using hh'.symm
  exact congrArg Subtype.val (S.layer.injective (he.trans (map_one S.layer).symm))

private theorem eq_one_of_fixes_dual (a : M)
    (hf : ∀ u ∈ S.dual, S.representation a u = u) : a = 1 := by
  obtain ⟨t, _, ht⟩ := S.outer
  have hb : t⁻¹ * a * t = 1 := S.eq_one_of_fixes_natural _ (by
    intro u hu
    have htu : S.representation t u ∈ S.dual := ht ▸ Submodule.mem_map_of_mem hu
    change (S.representation (t⁻¹ * a * t)) u = u
    rw [map_mul, map_mul]
    change S.representation t⁻¹ (S.representation a (S.representation t u)) = u
    rw [hf _ htu]
    change (S.representation t⁻¹ * S.representation t) u = u
    rw [← map_mul, inv_mul_cancel, map_one]
    rfl)
  calc
    a = t * (t⁻¹ * a * t) * t⁻¹ := by group
    _ = 1 := by rw [hb]; group

end CFSG.Quasithin.ChapterH.NaturalDual.SourceSetup

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

private theorem SourceModel.fixes_of_projection_eq_one (_S : B.SourceModel)
    (m : normalizer (L : Set G)) (he : B.actionProjection m = 1) :
    (m : G) ∈ centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
  intro w hw
  have hh := B.quotientAction_projection_apply m ⟨w, hw⟩
  rw [he, map_one, MulAut.one_apply] at hh
  change w = (m : G) * w * (m : G)⁻¹ at hh
  have hh' := congrArg (fun z => z * (m : G)) hh
  simpa only [inv_mul_cancel_right] using hh'

private theorem SourceModel.natural_centralizer (S : B.SourceModel) :
    normalizer (L : Set G) ⊓ centralizer (B.naturalSummand : Set G) ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
  intro m hm
  apply S.fixes_of_projection_eq_one ⟨m, hm.1⟩
  apply S.setup.eq_one_of_fixes_natural
  intro u hu
  have huw : (u.toMul : G) ∈ B.naturalSummand :=
    (B.mem_naturalSummand u.toMul).mpr ((S.natural_marking u.toMul).mp hu)
  rw [S.representation_eq]
  apply congrArg Additive.ofMul
  apply Subtype.ext
  change m * (u.toMul : G) * m⁻¹ = (u.toMul : G)
  rw [← hm.2 _ huw, mul_inv_cancel_right]

private theorem SourceModel.dual_centralizer (S : B.SourceModel) :
    normalizer (L : Set G) ⊓ centralizer (B.dualSummand : Set G) ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G) := by
  intro m hm
  apply S.fixes_of_projection_eq_one ⟨m, hm.1⟩
  apply S.setup.eq_one_of_fixes_dual
  intro u hu
  have huw : (u.toMul : G) ∈ B.dualSummand :=
    (B.mem_dualSummand u.toMul).mpr ((S.dual_marking u.toMul).mp hu)
  rw [S.representation_eq]
  apply congrArg Additive.ofMul
  apply Subtype.ext
  change m * (u.toMul : G) * m⁻¹ = (u.toMul : G)
  rw [← hm.2 _ huw, mul_inv_cancel_right]

/-- Both literal summands detect the full normalizer action on W. -/
public theorem SourceModel.summandCentralizers (S : B.SourceModel)
    (hNM : normalizer (componentOrbit V (T : Subgroup G) : Set G) = normalizer (L : Set G)) :
    B.SummandCentralizers := by
  constructor
  · rw [hNM]
    exact S.natural_centralizer
  · rw [hNM]
    exact S.dual_centralizer

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
