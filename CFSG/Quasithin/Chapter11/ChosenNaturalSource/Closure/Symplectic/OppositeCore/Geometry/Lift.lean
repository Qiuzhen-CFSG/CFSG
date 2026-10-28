module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.Geometry.Kernel

/-!
# Lifting marked three-pair generation

The kernel of the full LT action on V is O₂(LT). Thus an inclusion between
actual action images lifts to an inclusion modulo that two-core. Conjugation
and joins use this same action. Three conjugators in the marked L₁ image
therefore lift to three actual elements of L₁, and model generation supplies
the literal inclusion needed by the opposite-core assembly.

This module does not assert the missing matrix generation theorem or the
existence of the Cartan-compatible opposite pair.
Source: Aschbacher--Smith 11.5.7, printed p.783.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeGeometry
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)
include E

/-- Image inclusion lifts through the actual kernel, with no abstract
quotient replacement. -/
theorem le_join_large_core_of_image_le (A B : Subgroup G)
    (hA : A ≤ L ⊔ (T : Subgroup G)) (hB : B ≤ L ⊔ (T : Subgroup G))
    (himage : actionImage (V := V) A ≤ actionImage (V := V) B) :
    A ≤ B ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  rw [← largeAction_image E A hA, ← largeAction_image E B hB] at himage
  intro a ha
  obtain ⟨b, hb, he⟩ := himage (mem_map_of_mem (largeAction E)
    (show (⟨a, hA ha⟩ : (L ⊔ (T : Subgroup G) : Subgroup G)) ∈ A.subgroupOf _ from ha))
  have hc : (b : G)⁻¹ * a ∈ centralizer (V : Set G) := by
    have hk : b⁻¹ * ⟨a, hA ha⟩ ∈ (largeAction E).ker := by
      change (largeAction E) (b⁻¹ * ⟨a, hA ha⟩) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]
    exact (largeAction_ker E).le hk
  have hk : (b : G)⁻¹ * a ∈ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    (large_centralizer_eq_core E).le
      ⟨(L ⊔ (T : Subgroup G)).mul_mem
        ((L ⊔ (T : Subgroup G)).inv_mem b.property) (hA ha), hc⟩
  have hm : (b : G) * ((b : G)⁻¹ * a) ∈ B ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    (B ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2).mul_mem (mem_sup_left hb) (mem_sup_right hk)
  simpa only [mul_inv_cancel_left] using hm

omit [Finite G] E in
private theorem conjugate_le {A J : Subgroup G} (hA : A ≤ J) {l : G} (hl : l ∈ J) :
    A.map (MulAut.conj l).toMonoidHom ≤ J :=
  (map_mono hA).trans_eq (mem_normalizer_iff_map_conj_eq.mp (J.le_normalizer hl))

omit [Finite G] E in
private theorem restrict_conjugate {A J : Subgroup G} (hA : A ≤ J) {l : G} (hl : l ∈ J) :
    (A.map (MulAut.conj l).toMonoidHom).subgroupOf J =
      (A.subgroupOf J).map (MulAut.conj (⟨l,hl⟩ : J)).toMonoidHom := by
  apply map_injective J.subtype_injective
  rw [map_subgroupOf_eq_of_le (conjugate_le hA hl), map_map]
  have he : J.subtype.comp (MulAut.conj (⟨l,hl⟩ : J)).toMonoidHom =
      (MulAut.conj l).toMonoidHom.comp J.subtype := rfl
  rw [he, ← map_map, map_subgroupOf_eq_of_le hA]

/-- Conjugation is transported by the same marked full-module action. -/
theorem actionImage_conjugate (m : MarkedFlag E) (A : Subgroup G)
    (hA : A ≤ L ⊔ (T : Subgroup G)) {l : G} (hl : l ∈ L) :
    actionImage (V := V) (A.map (MulAut.conj l).toMonoidHom) =
      (actionImage (V := V) A).map
        (MulAut.conj (FullAction.modelHom m (PointModel.quotientMap m ⟨l,hl⟩))).toMonoidHom := by
  have hlJ : l ∈ L ⊔ (T : Subgroup G) := mem_sup_left hl
  rw [← largeAction_image E _ (conjugate_le hA hlJ), restrict_conjugate hA hlJ,
    ← largeAction_image E A hA, map_map, map_map]
  congr 1
  apply MonoidHom.ext
  intro a
  change (largeAction E) ((⟨l,hlJ⟩ : (L ⊔ (T : Subgroup G) : Subgroup G)) * a * ⟨l,hlJ⟩⁻¹) = _
  rw [map_mul, map_mul, map_inv, FullAction.modelHom_quotientMap]
  rfl

/-- Joins of subgroups inside LT have the expected full action image. -/
theorem actionImage_iSup {ι : Type*} (A : ι → Subgroup G)
    (hA : ∀ i, A i ≤ L ⊔ (T : Subgroup G)) :
    actionImage (V := V) (⨆ i, A i) = ⨆ i, actionImage (V := V) (A i) := by
  have he : (⨆ i, A i).subgroupOf (L ⊔ (T : Subgroup G)) =
      ⨆ i, (A i).subgroupOf (L ⊔ (T : Subgroup G)) := by
    apply map_injective (L ⊔ (T : Subgroup G)).subtype_injective
    rw [map_subgroupOf_eq_of_le (iSup_le hA), Subgroup.map_iSup]
    simp only [map_subgroupOf_eq_of_le (hA _)]
  rw [← largeAction_image E _ (iSup_le hA), he, Subgroup.map_iSup]
  simp only [largeAction_image E _ (hA _)]

/-- The exact premise of core_le_point_core_of_three_opposites follows
from generation in the full original action image. -/
theorem three_pairs_lift (m : MarkedFlag E) (hW : E.W ≤ E.G₁.pCoreIn 2)
    {y : G} (hy : y ∈ L) (l : Fin 3 → G) (hl : ∀ i, l i ∈ E.L₁)
    (hgen : actionImage (V := V) L ≤
      ⨆ i, actionImage (V := V)
        ((oppositeJoin (auxiliaryW E) y).map (MulAut.conj (l i)).toMonoidHom)) :
    L ≤ (⨆ i, (oppositeJoin (auxiliaryW E) y).map (MulAut.conj (l i)).toMonoidHom) ⊔
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hA (i : Fin 3) :
      (oppositeJoin (auxiliaryW E) y).map (MulAut.conj (l i)).toMonoidHom ≤
        L ⊔ (T : Subgroup G) :=
    conjugate_le (oppositeJoin_le_large E m hW hy) (mem_sup_left (E.L₁_le (hl i)))
  apply le_join_large_core_of_image_le E L _ le_sup_left (iSup_le hA)
  rwa [actionImage_iSup E _ hA]

/-- Lift three model conjugators from the actual L₁ image, then lift
model generation to the literal source inclusion. The geometric producer
must supply generation by these three point-local conjugate pairs. -/
theorem three_model_pairs_lift (m : MarkedFlag E) (hW : E.W ≤ E.G₁.pCoreIn 2)
    {y : G} (hy : y ∈ L)
    (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp E.input.field.Carrier))
    (hS : actionImage (V := V) (oppositeJoin (auxiliaryW E) y) = S.map (FullAction.modelHom m))
    (k : Fin 3 → Theory.SpecificGroups.SymplecticFour.Sp E.input.field.Carrier)
    (hk : ∀ i, k i ∈ PointModel.image m E.L₁)
    (hgen : (⨆ i, S.map (MulAut.conj (k i)).toMonoidHom) = ⊤) :
    ∃ l : Fin 3 → G, (∀ i, l i ∈ E.L₁) ∧
      L ≤ (⨆ i, (oppositeJoin (auxiliaryW E) y).map (MulAut.conj (l i)).toMonoidHom) ⊔
        (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  classical
  have hx : ∀ i, ∃ a : L, (a : G) ∈ E.L₁ ∧ PointModel.quotientMap m a = k i :=
    fun i => hk i
  choose a ha he using hx
  let l : Fin 3 → G := fun i => a i
  refine ⟨l, ha, three_pairs_lift E m hW hy l ha ?_⟩
  have hmap (i : Fin 3) :
      actionImage (V := V)
        ((oppositeJoin (auxiliaryW E) y).map (MulAut.conj (l i)).toMonoidHom) =
          (S.map (MulAut.conj (k i)).toMonoidHom).map (FullAction.modelHom m) := by
    rw [actionImage_conjugate E m _ (oppositeJoin_le_large E m hW hy) (a i).property,
      hS, he, map_map, map_map]
    congr 1
    apply MonoidHom.ext
    intro s
    change _ = (FullAction.modelHom m) (k i * s * (k i)⁻¹)
    rw [map_mul, map_mul, map_inv]
    rfl
  simp_rw [hmap]
  rw [← Subgroup.map_iSup, hgen]
  rw [← FullAction.image_eq m L le_rfl]
  exact map_mono le_top

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeGeometry
