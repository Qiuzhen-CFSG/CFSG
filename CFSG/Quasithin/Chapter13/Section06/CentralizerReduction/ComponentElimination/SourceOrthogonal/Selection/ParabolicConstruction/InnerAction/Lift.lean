module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.Marking
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.Replacement
public import Theory.GroupTheory.SolvableResidual.TwoSupplement

/-!
# Lifting the inner-action parabolic and its solvable residual

Under the inner-action hypothesis Tᵥ⁺ equals the actual component Sylow image.
The full preimage of a geometric parabolic in K Lᵥ Tᵥ contains its prescribed
actors. Its terminal derived subgroup is therefore normalized by both Tᵥ and
Lᵥ, lies inside K, and has exactly the geometric residual as its original
plus image. Two-perfectness puts the image of Lᵥ in that residual whenever
the geometric solvable quotient is a two-group, transferring movement of z.

The geometric enlargement, local C-component membership and star-quasisimplicity
are separate obligations. In particular no ambient containment Lᵥ≤D is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
13.6.23 on printed p.933/PDF p.950 and the minimal-parabolic argument on p.932.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction
open ComponentSelection
variable {G : Type*} [Group G]

/-- Under the inner-action assumption the actor has exactly the component Sylow image. -/
theorem plusTv_eq_intersection [Finite G]
    (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hlocal : K ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hinner : plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K) :
    plusImage K L T z v hL hz (Tv T v) =
      plusImage K L T z v hL hz (Tv T v ⊓ K) := by
  have ht := (Chapter1.isSylowIn_iff.mp hlocal.2.2.1).1
  exact (Chapter1.isSylowIn_iff.mp
    (plusSylowIntersection K L T z v hL hz hlocal)).2.2 _
      (ht.comap_subtype.map _) (map_mono (comap_mono inf_le_left)) hinner

variable (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))

/-- The full preimage of the geometric parabolic in the literal plus actor. -/
def liftedParabolic (P : Subgroup (Gplus K L T z v hL hz)) : Subgroup G :=
  (P.comap (plusMk K L T z v hL hz)).map (plusActor K L T v).subtype

/-- The source's terminal derived subgroup, embedded in the original group. -/
def liftedResidual (P : Subgroup (Gplus K L T z v hL hz)) : Subgroup G :=
  (solvableResidual (liftedParabolic K L T z v hL hz P)).map
    (liftedParabolic K L T z v hL hz P).subtype

theorem liftedParabolic_le_actor (P : Subgroup (Gplus K L T z v hL hz)) :
    liftedParabolic K L T z v hL hz P ≤ plusActor K L T v := map_subtype_le _

theorem le_liftedParabolic (P : Subgroup (Gplus K L T z v hL hz))
    (A : Subgroup G) (hA : A ≤ plusActor K L T v)
    (hi : plusImage K L T z v hL hz A ≤ P) :
    A ≤ liftedParabolic K L T z v hL hz P := by
  intro x hx
  exact mem_map.mpr ⟨⟨x, hA hx⟩, hi (mem_map.mpr ⟨⟨x, hA hx⟩, hx, rfl⟩), rfl⟩

theorem liftedParabolic_plusImage (P : Subgroup (Gplus K L T z v hL hz)) :
    plusImage K L T z v hL hz (liftedParabolic K L T z v hL hz P) = P := by
  rw [plusImage, liftedParabolic, subgroupOf,
    comap_map_eq_self_of_injective (plusActor K L T v).subtype_injective,
    map_comap_eq_self_of_surjective (plusMk_surjective K L T z v hL hz)]

private theorem residual_map {X Y : Type*} [Group X] [Group Y] [Finite X]
    (P : Subgroup X) (f : X →* Y) :
    ((solvableResidual P).map P.subtype).map f =
      (solvableResidual (P.map f)).map (P.map f).subtype := by
  have h := congrArg (fun S => S.map (P.map f).subtype)
    (map_solvableResidual_eq (f.subgroupMap P) (f.subgroupMap_surjective P))
  have he : (P.map f).subtype.comp (f.subgroupMap P) = f.comp P.subtype := rfl
  simpa only [map_map, he] using h

/-- The original plus image of the lifted residual is exactly the geometric residual. -/
theorem liftedResidual_plusImage [Finite G]
    (P : Subgroup (Gplus K L T z v hL hz)) :
    plusImage K L T z v hL hz (liftedResidual K L T z v hL hz P) =
      (solvableResidual P).map P.subtype := by
  rw [plusImage, liftedResidual, liftedParabolic, ← residual_map,
    subgroupOf, comap_map_eq_self_of_injective (plusActor K L T v).subtype_injective]
  exact map_solvableResidual_comap _ (plusMk_surjective K L T z v hL hz) P

/-- Any subgroup whose image lies in the parabolic normalizes its actual residual. -/
theorem normalizes_liftedResidual (P : Subgroup (Gplus K L T z v hL hz))
    (A : Subgroup G) (hA : A ≤ plusActor K L T v)
    (hi : plusImage K L T z v hL hz A ≤ P) :
    A ≤ normalizer (liftedResidual K L T z v hL hz P : Set G) := by
  apply (le_liftedParabolic K L T z v hL hz P A hA hi).trans
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
  let a := MulAut.conj (⟨g, hg⟩ : liftedParabolic K L T z v hL hz P)
  exact mem_map.mpr ⟨a y, map_solvableResidual_le a.toMonoidHom
    (mem_map_of_mem a.toMonoidHom hy), rfl⟩

/-- Perfectness belongs to the terminal derived subgroup, before any quotient. -/
theorem liftedResidual_perfect [Finite G]
    (P : Subgroup (Gplus K L T z v hL hz)) :
    Group.IsPerfect (liftedResidual K L T z v hL hz P) := by
  unfold liftedResidual
  exact Group.IsPerfect.map _

/-- The lifted residual lies in K, although the full preimage also contains Tᵥ. -/
theorem liftedResidual_le_component [Finite G]
    (P : Subgroup (Gplus K L T z v hL hz))
    (hlocal : K ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G)) :
    liftedResidual K L T z v hL hz P ≤ K := by
  let A := K ⊔ Tv T v
  let N := K.subgroupOf A
  let S := (Tv T v).subgroupOf A
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hlocal.2
  let : Group.IsPerfect N := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show K ≤ A from le_sup_left)).symm.toMonoidHom)
    (subgroupOfEquivOfLe (show K ≤ A from le_sup_left)).symm.surjective
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hK)
  have ht := (Chapter1.isSylowIn_iff.mp hlocal.2.2.1).1
  have hs : N ⊔ S = ⊤ := (codisjoint_subgroupOf_sup K (Tv T v)).eq_top
  have hr := (residuals_of_perfect_normal_sup_twoGroup N S ht.comap_subtype hs).2
  have hm := map_solvableResidual_mono
    ((liftedParabolic_le_actor K L T z v hL hz P).trans_eq
      (plusActor_eq_sup K L T v hLK hK))
  change liftedResidual K L T z v hL hz P ≤ (solvableResidual A).map A.subtype at hm
  rw [hr, map_subgroupOf_eq_of_le (show K ≤ A from le_sup_left)] at hm
  exact hm

/-- Lᵥ's two-perfect image lies in the geometric residual when its remaining quotient is a two-group. -/
theorem plusLv_le_geometricResidual [Finite G]
    (P : Subgroup (Gplus K L T z v hL hz))
    (hLP : plusImage K L T z v hL hz (Lv L v) ≤ P)
    (hquot : IsPGroup 2 (P ⧸ solvableResidual P)) :
    plusImage K L T z v hL hz (Lv L v) ≤ (solvableResidual P).map P.subtype := by
  let A := plusImage K L T z v hL hz (Lv L v)
  have hp : IsPPerfect 2 A :=
    (isPPerfect_embedded_pResidual 2 (L ⊓ Gv v)).of_surjective
      (plusImageMap K L T z v hL hz _ (le_sup_right.trans le_sup_left))
      (plusImageMap_surjective K L T z v hL hz _ _)
  have hp' : IsPPerfect 2 (A.subgroupOf P) := hp.of_surjective
    (subgroupOfEquivOfLe hLP).symm.toMonoidHom (subgroupOfEquivOfLe hLP).symm.surjective
  have hh := (le_pResidual_of_isPPerfect (A.subgroupOf P) hp').trans
    (sInf_le ⟨inferInstance, hquot⟩ : pResidual 2 P ≤ solvableResidual P)
  intro x hx
  exact mem_map.mpr ⟨⟨x, hLP hx⟩, hh hx, rfl⟩

/-- Movement is transported through the original quotient, without asserting Lᵥ≤D. -/
theorem liftedResidual_moves [Finite G]
    (P : Subgroup (Gplus K L T z v hL hz))
    (hLP : plusImage K L T z v hL hz (Lv L v) ≤ P)
    (hquot : IsPGroup 2 (P ⧸ solvableResidual P))
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G)) :
    ¬ liftedResidual K L T z v hL hz P ≤ centralizer ({z} : Set G) := by
  apply replacement_moves_z K _ L T z v hL hz _ hmove
  rw [liftedResidual_plusImage]
  exact plusLv_le_geometricResidual K L T z v hL hz P hLP hquot

/-- The source Sylow remains Sylow in the join of the actual residual and Tᵥ. -/
theorem liftedResidual_sylow [Finite G]
    (P : Subgroup (Gplus K L T z v hL hz))
    (hlocal : K ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G)) :
    Chapter1.IsSylowIn 2 (Tv T v) (liftedResidual K L T z v hL hz P ⊔ Tv T v) :=
  hlocal.2.2.1.restrict le_sup_right
    (sup_le_sup (liftedResidual_le_component K L T z v hL hz P hlocal hLK hK) le_rfl)

/-- The actual source application constructs the residual, both normalizers,
movement and the Sylow witness from the geometric overgroup. Local-component
membership and star-quasisimplicity are not included as premises here. -/
theorem liftedResidual_source_data [Finite G]
    (hlocal : K ∈ Chapter1.LIn (Gv v) (Tv T v))
    (hLK : Lv L v ≤ K) (hK : Tv T v ≤ normalizer (K : Set G))
    (hinner : plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K)
    (hmove : ¬ Lv L v ≤ centralizer ({z} : Set G))
    (P : Subgroup (Gplus K L T z v hL hz))
    (hP : plusImage K L T z v hL hz (sourceParabolic K L T v) ≤ P)
    (hquot : IsPGroup 2 (P ⧸ solvableResidual P)) :
    let D := liftedResidual K L T z v hL hz P
    D ≤ K ∧ Tv T v ≤ normalizer (D : Set G) ∧
      Lv L v ≤ normalizer (D : Set G) ∧ ¬ D ≤ centralizer ({z} : Set G) ∧
      Chapter1.IsSylowIn 2 (Tv T v) (D ⊔ Tv T v) := by
  have hLP : plusImage K L T z v hL hz (Lv L v) ≤ P :=
    (map_mono (comap_mono (show Lv L v ≤ sourceParabolic K L T v from le_sup_left))).trans hP
  have hTP : plusImage K L T z v hL hz (Tv T v) ≤ P := by
    rw [plusTv_eq_intersection K L T z v hL hz hlocal hinner]
    exact (map_mono (comap_mono
      (show Tv T v ⊓ K ≤ sourceParabolic K L T v from le_sup_right))).trans hP
  exact ⟨liftedResidual_le_component K L T z v hL hz P hlocal hLK hK,
    normalizes_liftedResidual K L T z v hL hz P _ le_sup_right hTP,
    normalizes_liftedResidual K L T z v hL hz P _ (le_sup_right.trans le_sup_left) hLP,
    liftedResidual_moves K L T z v hL hz P hLP hquot hmove,
    liftedResidual_sylow K L T z v hL hz P hlocal hLK hK⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection.ParabolicConstruction.InnerAction
