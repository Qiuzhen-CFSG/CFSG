module
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.UniqueMaximalNormalExtension
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.MinimalParabolicGeneration
public import Theory.PGroupCore

/-!
# Minimal parabolics with a central rank-one core quotient

Suppose a normal perfect subgroup A and a Sylow two-subgroup S generate H.
If A/O₂(A) maps onto SL₂(F) with central kernel, then H has a unique maximal
subgroup over S, and S is not normal. The central kernel is allowed to have
odd order: perfection rules out proper supplements to it. Unique maximality
first lifts through this cover and O₂(A), then through the normal extension.
Nonnormality follows from the literal SL₂ Sylow image.

This is the rank-one local argument used in Aschbacher–Smith 13.6.19,
printed p.931, with the minimal-parabolic convention of B.6.1, p.112.
-/

public section
namespace Matrix.SpecialLinearGroup

open Subgroup Theory.GroupTheory
open scoped MatrixGroups

private theorem unique_over_central_cover {A B : Type*} [Group A] [Group B]
    [Finite A] [Group.IsPerfect A] (f : A →* B) (hf : Function.Surjective f)
    (hk : f.ker ≤ center A) (U : Subgroup A)
    (hu : Order.HasUniqueMaximalOver (U.map f) ⊤) :
    Order.HasUniqueMaximalOver U ⊤ := by
  let : Finite B := Finite.of_surjective f hf
  obtain ⟨M, hM, _⟩ := hu.2
  have hco := isCoatom_comap_of_surjective hf hM.2.isCoatom
  have hUM : U ≤ M.comap f := map_le_iff_le_comap.mp hM.1
  refine ⟨lt_of_le_of_lt hUM hco.lt_top, M.comap f, ⟨hUM, hco.covBy_top⟩, ?_⟩
  intro N hN
  have hproper : N.map f < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro he
    have hs : Function.Surjective (f.comp N.subtype) := by
      rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, range_subtype, he]
    have hsN := PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      f N.subtype hs hk
    exact hN.2.ne (by simpa only [range_subtype] using MonoidHom.range_eq_top.mpr hsN)
  have hNM := map_le_iff_le_comap.mp (hu.le_maximal hM (map_mono hN.1) hproper)
  exact ((hN.2.eq_or_eq hNM le_top).resolve_right hco.1).symm

private theorem rankOne_core_unique {A : Type*} [Group A] [Finite A] [Group.IsPerfect A]
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (f : A ⧸ pCore 2 A →* SL(2, F)) (hf : Function.Surjective f)
    (hk : f.ker ≤ center (A ⧸ pCore 2 A)) (U : Sylow 2 A) :
    Order.HasUniqueMaximalOver (U : Subgroup A) ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 A)
  let Uq := U.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 A))
  let Uf := Uq.mapSurjective hf
  have hu := Matrix.SpecialLinearGroup.sylow_hasUniqueMaximalOver (F := F) 2 Uf
  have huq := unique_over_central_cover f hf hk (Uq : Subgroup (A ⧸ pCore 2 A)) hu
  apply hasUniqueMaximalOver_of_surjective q (QuotientGroup.mk'_surjective _) ?_ huq
  rw [QuotientGroup.ker_mk']
  exact pCore_isPGroup.le_sylow_of_normal U

theorem minimal_over_normal_rankOne_core {H : Type*} [Group H] [Finite H]
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    (A : Subgroup H) [A.Normal] [Group.IsPerfect A] (S : Sylow 2 H)
    (hgen : A ⊔ (S : Subgroup H) = ⊤)
    (f : A ⧸ pCore 2 A →* SL(2, F)) (hf : Function.Surjective f)
    (hk : f.ker ≤ center (A ⧸ pCore 2 A)) :
    (⊤ : Subgroup H) ∈ nonNormalUniqueMaximalOvergroups (S : Subgroup H) := by
  obtain ⟨U, hU⟩ := S.exists_subgroupOf_eq_of_normal A
  have hu := rankOne_core_unique F f hf hk U
  have huA := hasUniqueMaximalOver_map_subtype hu
  rw [hU, subgroupOf_map_subtype, inf_comm] at huA
  have huH := hasUniqueMaximalOver_sup_of_normalizes
    (show (S : Subgroup H) ≤ normalizer (A : Set H) from le_normalizer_of_normal) huA
  rw [hgen] at huH
  refine ⟨huH, ?_⟩
  intro hn
  let : (S : Subgroup H).Normal := normalizer_eq_top_iff.mp (top_unique hn)
  have hnU : (U : Subgroup A).Normal := by rw [hU]; infer_instance
  let q := QuotientGroup.mk' (pCore 2 A)
  let Uq := U.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 A))
  let Uf := Uq.mapSurjective hf
  have hnUq : (Uq : Subgroup (A ⧸ pCore 2 A)).Normal :=
    Subgroup.Normal.map hnU q (QuotientGroup.mk'_surjective _)
  have hnUf : (Uf : Subgroup SL(2, F)).Normal := Subgroup.Normal.map hnUq f hf
  exact Matrix.SpecialLinearGroup.no_normal_sylow F 2 Uf hnUf

end Matrix.SpecialLinearGroup
end
