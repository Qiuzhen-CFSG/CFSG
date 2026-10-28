module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction.LocalFamily.CComponent
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCoreCentralLift

/-!
# The star quotient of the lifted parabolic residual

The actual comparison K*/O₂(K*) → K⁺ has central kernel, since its source
is quasisimple and its image is nontrivial. Restrict it to the perfect
residual. Its star-to-plus kernel is central modulo the intersection with
O₂(K*), a normal two-subgroup. Prime-core central-cover calculus therefore
lifts the geometric quasisimplicity to D*/O₂(D*).

No subnormality of D in Gᵥ or intrinsic model for K/O₂(K) is used.
Source: Aschbacher–Smith, proof of 13.6.23, p.933/PDF p.950.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]

/-- Restricting the original component comparison lifts quasisimplicity
modulo the two-core for every perfect subgroup of K. -/
theorem star_core_quasisimple_of_plus_core
    (K D L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v) (hDK : D ≤ K) [Group.IsPerfect D]
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hq : IsQuasisimple (plusImage K L T z v hL hz D ⧸
      pCore 2 (plusImage K L T z v hL hz D))) :
    IsQuasisimple (starImage z v D ⧸ pCore 2 (starImage z v D)) := by
  let S := starImage z v K
  let E := starImage z v D
  let B := plusImage K L T z v hL hz D
  have hDG : D ≤ Gv v := hDK.trans hY.1.1
  have hDA : D ≤ plusActor K L T v := hDK.trans (K_le_plusActor K L T v)
  let i : E →* S := inclusion (map_mono (comap_mono hDK))
  let c := componentStarToPlus K L T z v hY.1.1 hL hz
  let cq := componentCoreQuotientToPlus K L T z v hL hz hY hR
  let q := QuotientGroup.mk' (pCore 2 S)
  let : IsQuasisimple (S ⧸ pCore 2 S) := hY.2.1
  let : Nontrivial (plusImage K L T z v hL hz K) :=
    (nontrivial_iff_ne_bot _).mpr (plusImage_ne_bot_of_mem_Yz K L T z v hL hz hY)
  have hck : cq.ker ≤ center (S ⧸ pCore 2 S) := by
    rcases IsQuasisimple.normal_le_center_or_eq_top cq.ker with hc | ht
    · exact hc
    · obtain ⟨b, hb⟩ := exists_ne (1 : plusImage K L T z v hL hz K)
      obtain ⟨a, rfl⟩ := componentCoreQuotientToPlus_surjective K L T z v hL hz hY hR b
      exact (hb (MonoidHom.mem_ker.mp (ht.symm ▸ mem_top a))).elim
  have hrep (d : D) :
      (c (i (starImageMap z v D hDG d)) : Gplus K L T z v hL hz) =
        plusMk K L T z v hL hz (inclusion hDA d) := by
    exact componentStarToPlus_mk K L T z v hY.1.1 hL hz (inclusion hDK d)
  let f : E →* B :=
    ((plusImage K L T z v hL hz K).subtype.comp (c.comp i)).codRestrict B (by
      intro x
      obtain ⟨d, rfl⟩ := starImageMap_surjective z v D hDG x
      change (c (i (starImageMap z v D hDG d)) : Gplus K L T z v hL hz) ∈ B
      rw [hrep]
      exact mem_map.mpr ⟨inclusion hDA d, d.property, rfl⟩)
  have hf : Function.Surjective f := by
    intro b
    obtain ⟨x, hx, he⟩ := b.property
    refine ⟨starImageMap z v D hDG ⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact (hrep ⟨x, hx⟩).trans he
  let N := (pCore 2 S).comap i
  have hp : IsPGroup 2 N := pCore_isPGroup.comap_of_injective i (inclusion_injective _)
  have hN : N ≤ f.ker := by
    intro x hx
    apply Subtype.ext
    change (c (i x) : Gplus K L T z v hL hz) = 1
    exact congrArg (fun a : plusImage K L T z v hL hz K =>
      (a : Gplus K L T z v hL hz))
      (MonoidHom.mem_ker.mp (componentStarToPlus_twoCore_le_ker K L T z v hL hz hY hR hx))
  have hk : f.ker.map (QuotientGroup.mk' N) ≤ center (E ⧸ N) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxq : q (i x) ∈ cq.ker := by
      change c (i x) = 1
      apply Subtype.ext
      change (f x : Gplus K L T z v hL hz) = 1
      exact congrArg (fun a : B => (a : Gplus K L T z v hL hz))
        (MonoidHom.mem_ker.mp hx)
    have hc := hck hxq
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N y
    rw [← map_mul, ← map_mul]
    apply QuotientGroup.eq_iff_div_mem.mpr
    change i (y * x / (x * y)) ∈ pCore 2 S
    apply (QuotientGroup.eq_one_iff _).mp
    change q (i (y * x / (x * y))) = 1
    rw [map_div, map_mul, map_mul, map_div, map_mul, map_mul,
      mem_center_iff.mp hc (q (i y)), div_eq_mul_inv, mul_inv_cancel]
  let : Group.IsPerfect E := Group.IsPerfect.ofSurjective
    (starImageMap_surjective z v D hDG)
  let : IsQuasisimple (B ⧸ pCore 2 B) := hq
  exact quasisimple_core_quotient_of_kernel_central_mod_pGroup f hf N hp hN hk

/-- The literal geometric model supplies star-quasisimplicity of the actual lifted residual. -/
theorem liftedResidual_star_quasisimple
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hY : K ∈ Yz L T z v)
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (P : Subgroup (Gplus K L T z v hL hz))
    (eP : ((solvableResidual P).map P.subtype ⧸
      pCore 2 ((solvableResidual P).map P.subtype)) ≃* SL(3, ZMod 2)) :
    IsQuasisimple (starImage z v (liftedResidual K L T z v hL hz P) ⧸
      pCore 2 (starImage z v (liftedResidual K L T z v hL hz P))) := by
  let D := liftedResidual K L T z v hL hz P
  let : Group.IsPerfect D := liftedResidual_perfect K L T z v hL hz P
  let a : plusImage K L T z v hL hz D ≃* (solvableResidual P).map P.subtype :=
    MulEquiv.subgroupCongr (liftedResidual_plusImage K L T z v hL hz P)
  let e := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eP
  let : IsQuasisimple SL(3, ZMod 2) :=
    { toIsPerfect := Atlas.sl_perfect 3 (by decide)
      simple := Atlas.psl_simple_high_rank 3 (by decide) }
  exact star_core_quasisimple_of_plus_core K D L T z v hL hz hY
    (liftedResidual_le_component K L T z v hL hz P hY.1 hLK hK) hR
    (IsQuasisimple.of_mulEquiv e.symm)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction
