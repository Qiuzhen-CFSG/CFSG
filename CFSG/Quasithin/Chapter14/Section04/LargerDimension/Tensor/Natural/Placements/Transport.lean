module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Quotients
public import Theory.GroupTheory.SylowNormalizerCommutingFamily
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.SylowImageIntersection

/-!
# Quotient marks for the literal tensor subgroups

The component, its specified Sylow intersection, and its Borel are transported
through the original core quotient and any prescribed actor equivalence.
Sylow restriction to the normal solvable residual and the relative Frattini
argument prove the normalizer image equality, even for an arbitrary kernel.
The residual and join formulas retain both actual source factors.

Source: Aschbacher–Smith, Lemma 14.4.10, printed pp.1010–1011.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Placements
variable {G D : Type*} [Group G] [Group D]

private theorem normalizer_map_subtype (K : Subgroup G) (A : Subgroup K) :
    (normalizer (A : Set K)).map K.subtype =
      K ⊓ normalizer (A.map K.subtype : Set G) := by
  have h : (A.map K.subtype).subgroupOf K = A := by
    exact comap_map_eq_self_of_injective K.subtype_injective A
  nth_rw 1 [← h]
  rw [← subgroupOf_normalizer_eq (map_subtype_le _), subgroupOf_map_subtype,
    inf_comm]

private theorem sylowNormalizer_map [Finite G] {p : ℕ} [Fact p.Prime]
    (K : Subgroup G) (P : Sylow p K) (f : G →* D) :
    ((normalizer (P : Set K)).map K.subtype).map f =
      K.map f ⊓ normalizer (((P : Subgroup K).map K.subtype).map f : Set D) := by
  let g := f.subgroupMap K
  have hg : (K.map f).subtype.comp g = f.comp K.subtype := rfl
  rw [map_map, ← hg, ← map_map,
    P.normalizer_map_surjective g (f.subgroupMap_surjective K), normalizer_map_subtype,
    map_map, hg, ← map_map]

variable (H : Subgroup G)

theorem star_map_subtype (A : Subgroup H) :
    star H (A.map H.subtype) = A.map (QuotientGroup.mk' (pCore 2 H)) := by
  rw [star, ← comap_subtype, comap_map_eq_self_of_injective H.subtype_injective]

theorem star_sup {X Y : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    star H (X ⊔ Y) = star H X ⊔ star H Y := by
  rw [star, subgroupOf_sup hX hY, Subgroup.map_sup]
  rfl

variable [Finite G]

theorem star_component : star H (component H) = solvableResidual (coreQuotient H) := by
  rw [component, star_map_subtype, map_solvableResidual_eq _ (QuotientGroup.mk'_surjective _)]

theorem map_star_component (e : coreQuotient H ≃* D) :
    (star H (component H)).map e.toMonoidHom = solvableResidual D := by
  rw [star_component, map_solvableResidual_eq _ e.surjective]

variable {H} {T : Subgroup G}

/-- A Sylow witness for the original T gives all three quotient marks together. -/
theorem star_sylow_marks
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T) :
    (∃ P : Sylow 2 (coreQuotient H), (P : Subgroup (coreQuotient H)) = star H T) ∧
    star H (T ⊓ component H) = star H T ⊓ star H (component H) ∧
    star H (borel H T) = star H (component H) ⊓
      normalizer (star H (T ⊓ component H) : Set (coreQuotient H)) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let K := solvableResidual H
  obtain ⟨P, hP⟩ := S.exists_sylow_map_eq_inf_of_normal K
  have hTP : ((P : Subgroup K).map K.subtype).map H.subtype = T ⊓ component H := by
    rw [hP, map_inf _ _ _ H.subtype_injective, hS]
    rfl
  have hB : ((normalizer (P : Set K)).map K.subtype).map H.subtype = borel H T := by
    rw [sylowNormalizer_map, hTP]
    rfl
  have hTI : star H (T ⊓ component H) = star H T ⊓ star H (component H) := by
    rw [← hTP, star_map_subtype, ← hS, star_map_subtype, component, star_map_subtype]
    exact S.map_image_eq_inf K ((P : Subgroup K).map K.subtype) P rfl
      (hP.le.trans inf_le_left) q
  refine ⟨⟨S.mapSurjective (QuotientGroup.mk'_surjective _), ?_⟩, hTI, ?_⟩
  · rw [← hS, star_map_subtype]
    rfl
  · rw [← hB, star_map_subtype, sylowNormalizer_map, ← hTP, star_map_subtype,
      component, star_map_subtype]

/-- The same marks in any prescribed genuine actor coordinates. -/
theorem actor_sylow_marks
    (S : Sylow 2 H) (hS : (S : Subgroup H).map H.subtype = T)
    (e : coreQuotient H ≃* D) :
    (∃ P : Sylow 2 D, (P : Subgroup D) = (star H T).map e.toMonoidHom) ∧
    (star H (T ⊓ component H)).map e.toMonoidHom =
      (star H T).map e.toMonoidHom ⊓ solvableResidual D ∧
    (star H (borel H T)).map e.toMonoidHom = solvableResidual D ⊓
      normalizer (((star H T).map e.toMonoidHom ⊓ solvableResidual D) : Set D) := by
  obtain ⟨⟨P, hP⟩, hI, hB⟩ := star_sylow_marks S hS
  refine ⟨⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩, ?_, ?_⟩
  · change (P : Subgroup (coreQuotient H)).map e.toMonoidHom = _
    rw [hP]
  · rw [hI, map_inf _ _ _ e.injective, map_star_component]
  · rw [hB, map_inf _ _ _ e.injective, map_star_component,
      map_equiv_normalizer_eq, hI, map_inf _ _ _ e.injective, map_star_component]
    rfl

/-- The first residual is the three-core in the original actor coordinates. -/
theorem actor_first (e : coreQuotient H ≃* D) :
    (star H (first H)).map e.toMonoidHom = pCore 3 D := by
  rw [star_first, pCore_map_iso]

/-- The second residual is transported using the actual Borel image. -/
theorem actor_second (e : coreQuotient H ≃* D) :
    (star H (second H T)).map e.toMonoidHom =
      twoResidual ((star H (borel H T)).map e.toMonoidHom) := by
  rw [second, star_twoResidual (show borel H T ≤ H from
    inf_le_left.trans (map_subtype_le _))]
  exact map_embedded_pResidual 2 _ _

/-- The literal local join maps to the residual Borel joined with the image Sylow. -/
theorem actor_second_join (hT : T ≤ H) (e : coreQuotient H ≃* D) :
    (star H (second H T ⊔ T)).map e.toMonoidHom =
      twoResidual ((star H (borel H T)).map e.toMonoidHom) ⊔
        (star H T).map e.toMonoidHom := by
  rw [star_sup H (second_le H T) hT, Subgroup.map_sup, actor_second]

/-- The complete overlap retains both residual factors and the image Sylow. -/
theorem actor_overlap (hT : T ≤ H) (e : coreQuotient H ≃* D) :
    (star H (overlap H T)).map e.toMonoidHom =
      pCore 3 D ⊔ twoResidual ((star H (borel H T)).map e.toMonoidHom) ⊔
        (star H T).map e.toMonoidHom := by
  rw [overlap, star_sup H (sup_le (first_le H) (second_le H T)) hT,
    star_sup H (first_le H) (second_le H T), Subgroup.map_sup, Subgroup.map_sup,
    actor_first, actor_second]

omit [Finite G] in
/-- The given Sylow image normalizes the given Borel image. -/
theorem actor_borel_normalized (hT : T ≤ H) (e : coreQuotient H ≃* D) :
    (star H T).map e.toMonoidHom ≤
      normalizer ((star H (borel H T)).map e.toMonoidHom : Set D) := by
  have hBH : borel H T ≤ H := inf_le_left.trans (map_subtype_le _)
  have hN : T.subgroupOf H ≤ normalizer ((borel H T).subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hBH]
    exact fun x hx => borel_T_normalized hT hx
  have hq : star H T ≤ normalizer (star H (borel H T) : Set (coreQuotient H)) :=
    (map_mono hN).trans (le_normalizer_map (QuotientGroup.mk' (pCore 2 H)))
  exact (map_mono hq).trans (le_normalizer_map e.toMonoidHom)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Tensor.Placements
