module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.Action
public import Theory.GroupTheory.PRadical.NormalComponentImages
public import Theory.GroupTheory.RadicalNormalizerControl

/-!
# The actual radical intersection in the point-component image

R₁ is the two-core of L₁T, which contains the original Sylow subgroup.
Restriction of normal two-cores makes R₁ the two-core of its full
normalizer and of its normalizer in KzT. Intersecting with the relatively
normal Kz and passing first through O₂(Kz), then through the odd central
action kernel, preserves this core identity. The resulting subgroup is
exactly R₁* intersect Kz*, through the original VK-action projection.
No assertion that all of R₁* is inner is made here.

Source: Aschbacher--Smith 11.4.2, printed p.777; the radical-intersection
and central-cover transport is the argument of Asc81b 8.2(4).
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
open Classification
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (E : Closure.Geometry D)

/-- The original R₁ is the full two-core of its ambient normalizer. -/
theorem radical_normalizer_core :
    (normalizer (E.R₁ : Set G)).pCoreIn 2 = E.R₁ := by
  have hn : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (E.R₁ : Set G) :=
    (E.L₁ ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  apply le_antisymm (pCoreIn_le_pCoreIn_of_sylow T le_sup_right hn)
  exact le_map_pCore_normalizer (isPGroup_pCoreIn 2 _)

/-- The same core identity holds on the literal KzT carrier. -/
theorem intrinsic_radical_normalizer_core :
    (normalizer (radical E : Set (localGroup E))).pCoreIn 2 = radical E := by
  have hRL : E.R₁ ≤ localGroup E := (radical_le_sylow E).trans le_sup_right
  let N := normalizer (E.R₁ : Set G) ⊓ localGroup E
  have he : (normalizer (radical E : Set (localGroup E))).map (localGroup E).subtype = N := by
    rw [radical, ← subgroupOf_normalizer_eq hRL, subgroupOf_map_subtype]
  apply map_injective (localGroup E).subtype_injective
  rw [map_pCoreIn_of_injective 2 _ _ (localGroup E).subtype_injective, he,
    radical, map_subgroupOf_eq_of_le hRL]
  apply le_antisymm
  · exact pCoreIn_le_pCoreIn_of_sylow T le_sup_right
      (le_inf ((E.L₁ ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
        (sup_le_sup_right (le_conjugateSpanBy _ _) _))
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 _)
      (le_inf E.R₁.le_normalizer hRL) inf_le_left

/-- Strict comparison is not needed for nontriviality of the radical:
the specified nonidentity point lies in V₁ ≤ VK ≤ R₁. -/
theorem intrinsic_radical_isRadical (h : EarlierGeometry E)
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) : (radical E).IsPRadical 2 := by
  refine ⟨?_,intrinsic_radical_normalizer_core E⟩
  intro hb
  obtain ⟨v,hv,he⟩ := line_le_module E hstar hcent h.point_mem
  have hr := module_le_radical E hv
  rw [hb,mem_bot] at hr
  exact h.point_ne_one (he.symm.trans (congrArg Subtype.val hr))

/-- The point-component intersection is a radical core before any quotient. -/
theorem component_intersection_normalizer_core (h : EarlierGeometry E)
    (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) :
    (normalizer (E.R₁.subgroupOf E.Kz : Set E.Kz)).pCoreIn 2 = E.R₁.subgroupOf E.Kz := by
  let := component_normal E h
  let U := (radical E).subgroupOf (component E)
  let e := subgroupOfEquivOfLe (show E.Kz ≤ localGroup E from le_sup_left)
  have hu : U.map e.toMonoidHom = E.R₁.subgroupOf E.Kz := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩; exact ha
    · intro hx
      exact ⟨⟨⟨x,(show E.Kz ≤ localGroup E from le_sup_left) x.property⟩,x.property⟩,hx,rfl⟩
  have hh := congrArg (map e.toMonoidHom)
    (normal_intersection_relative_core (component E) (radical E)
      (intrinsic_radical_isRadical E h hstar hcent))
  change ((normalizer (U : Set (component E))).pCoreIn 2).map e.toMonoidHom = U.map e.toMonoidHom at hh
  rwa [map_pCoreIn_of_injective 2 _ _ e.injective,map_equiv_normalizer_eq,hu] at hh

/-- The literal component projection preserves the radical-core identity,
including its possible odd central kernel. -/
theorem component_image_intersection_normalizer_core
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) :
    (normalizer ((E.R₁.subgroupOf E.Kz).map (componentProjection E) : Set (componentImage E))).pCoreIn 2 =
      (E.R₁.subgroupOf E.Kz).map (componentProjection E) := by
  let : IsQuasisimple (componentImage E) := (action_structure E h hf hne hstar hcent).2.2
  let : IsSimpleGroup (componentImage E ⧸ center (componentImage E)) := IsQuasisimple.simple
  let : Nontrivial (componentImage E) :=
    (QuotientGroup.mk'_surjective (center (componentImage E))).nontrivial
  let U := E.R₁.subgroupOf E.Kz
  let q := QuotientGroup.mk' (pCore 2 E.Kz)
  let f := componentQuotientProjection E h
  have hU : IsPGroup 2 U := (isPGroup_pCoreIn 2 (E.L₁ ⊔ (T : Subgroup G))).comap_subtype
  have hc := component_intersection_normalizer_core E h hstar hcent
  have hQU : q.ker ≤ U := by
    rw [QuotientGroup.ker_mk']
    exact pCore_le_of_pCore_normalizer_le U hU hc.le
  have hquot := map_normalizer_core_of_p_kernel U hU hc q (QuotientGroup.mk'_surjective _) hQU
  have hk : f.ker ≤ center (E.Kz ⧸ pCore 2 E.Kz) := by
    rw [← IsQuasisimple.comap_center_of_surjective f (componentQuotientProjection_surjective E h)]
    intro x hx
    change f x ∈ center (componentImage E)
    rw [show f x = 1 from hx]
    exact one_mem _
  have hp : Nat.Coprime 2 (Nat.card f.ker) := Nat.prime_two.coprime_iff_not_dvd.mpr
    (PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) f.ker hk)
  have hs := map_normalizer_core_of_central_coprime_kernel (U.map q) (hU.map q) hquot f
    (componentQuotientProjection_surjective E h) hk hp
  have he : f.comp q = componentProjection E := by ext; rfl
  simpa only [map_map,he] using hs

/-- The VK-action kernel lies in O₂(KzT)Kz; the covering-center part is retained. -/
theorem action_kernel_le_core_sup_component
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) :
    (projection E).ker ≤ pCore 2 (localGroup E) ⊔ component E := by
  let := component_normal E h
  let := component_quasisimple E
  have hc : pCore 2 (localGroup E) ≤ centralizer (moduleSubgroup E : Set (localGroup E)) := by
    intro q hq w hw
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hw).2.2 q hq |>.symm
  have hn : ¬ component E ≤ centralizer (moduleSubgroup E : Set (localGroup E)) := by
    intro hh
    exact module_moved E h hf hne hstar hcent
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hh))
  rw [projection, ChapterB.InternalThompsonAction.actionMk, QuotientGroup.ker_mk']
  exact (QuasisimpleKernel.normal_kernel_structure (component E)
    (sylow E : Subgroup (localGroup E)) (centralizer (moduleSubgroup E : Set (localGroup E)))
    hstar.1.1 (sylow E).isPGroup' (component_sup_sylow E) hc hn).1.trans
      (sup_le_sup_left (map_subtype_le _) _)

/-- Images commute with this intersection because the entire action kernel
lies in O₂(KzT)Kz and the two-core lies in R₁. -/
theorem radical_image_inf_component
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) :
    ((radical E) ⊓ component E).map (projection E) =
      (radical E).map (projection E) ⊓ componentImage E := by
  apply map_inf_of_kernel_le_sup (radical E) (component E) (pCore 2 (localGroup E))
    (projection E) _ (intrinsic_core_le_radical E)
    (action_kernel_le_core_sup_component E h hf hne hstar hcent)
  intro q hq
  apply (QuotientGroup.eq_one_iff _).mpr
  intro w hw
  exact ((mem_omegaOneCenterAmbient_iff _ _).mp hw).2.2 q hq |>.symm

/-- The intrinsic projected intersection is literally R₁* restricted to Kz*. -/
theorem component_image_intersection_eq
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) :
    (E.R₁.subgroupOf E.Kz).map (componentProjection E) =
      ((radical E).map (projection E)).subgroupOf (componentImage E) := by
  apply map_injective (componentImage E).subtype_injective
  rw [subgroupOf_map_subtype, ← radical_image_inf_component E h hf hne hstar hcent]
  ext x
  constructor
  · rintro ⟨y,⟨k,hk,rfl⟩,rfl⟩
    exact ⟨⟨k,(show E.Kz ≤ localGroup E from le_sup_left) k.property⟩,⟨hk,k.property⟩,rfl⟩
  · rintro ⟨k,hk,rfl⟩
    exact ⟨componentProjection E ⟨k,hk.2⟩,⟨⟨k,hk.2⟩,hk.1,rfl⟩,rfl⟩

/-- The normalizer-core identity on the actual intersection in Kz*. -/
theorem radical_image_intersection_normalizer_core
    (h : EarlierGeometry E) (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : E.Kz ≠ E.K) (hstar : E.Kz ∈ Chapter1.LStar G (T : Subgroup G))
    [IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)]
    (hcent : E.V₁ ≤ centralizer (E.R₁ : Set G)) :
    (normalizer (((radical E).map (projection E)).subgroupOf (componentImage E) :
      Set (componentImage E))).pCoreIn 2 =
      ((radical E).map (projection E)).subgroupOf (componentImage E) := by
  rw [← component_image_intersection_eq E h hf hne hstar hcent]
  exact component_image_intersection_normalizer_core E h hf hne hstar hcent

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Hall
