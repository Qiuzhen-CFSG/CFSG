module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Projections from the layer to a component's central quotient

The layer lies in the product of a chosen component and its centralizer,
since distinct components commute. Quotienting the layer by the relative
centralizer therefore gives the chosen component modulo its center. This
constructs an actual homomorphism whose restriction to that component is
the original central quotient map, allowing nontrivial central intersections.

If the normal closure of a subgroup contains the chosen component, its
projection is nonzero: otherwise the projection's normal kernel contains
the whole closure and kills the surjective component restriction.

Source: the central-product projection argument in GLS II, Chapter B,
Proposition 5.22(i)-(ii). Its application to the odd-core images of
two-components is in ChapterI/Section03/RankTwoSource/OrbitProjection.
-/

public section
open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A component factor of the layer has a projection to its central quotient.
On the original component inclusion this is exactly the quotient map. -/
theorem IsComponent.exists_layer_centralQuotient_projection
    {J : Subgroup G} (hJ : IsComponent G J) :
    ∃ π : componentLayer G →* (J ⧸ center J),
      ∀ j : J, π (inclusion (le_sSup hJ) j) = QuotientGroup.mk' (center J) j := by
  classical
  let E := componentLayer G
  have hJE : J ≤ E := le_sSup hJ
  have hEC : E ≤ J ⊔ centralizer (J : Set G) := by
    apply sSup_le
    intro K hK
    by_cases h : K = J
    · exact h ▸ le_sup_left
    · exact (commutator_eq_bot_iff_le_centralizer.mp
        (hK.commutator_eq_bot_of_ne hJ h)).trans le_sup_right
  have hEN : E ≤ normalizer (J : Set G) := hEC.trans
    (sup_le J.le_normalizer (Subgroup.centralizer_le_normalizer _))
  let R := J.subgroupOf E
  let : R.Normal := normal_subgroupOf_of_le_normalizer hEN
  let C := centralizer (R : Set E)
  let q := QuotientGroup.mk' C
  let i : J →* E := inclusion hJE
  let f := q.comp i
  have hsup : R ⊔ C = ⊤ := by
    apply top_unique
    intro x _
    have hx := hEC x.property
    have hmem : (x : G) ∈ (J : Set G) * (centralizer (J : Set G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left J _ (Subgroup.centralizer_le_normalizer _)]
      exact hx
    obtain ⟨j, hj, c, hc, he⟩ := hmem
    have hcE : c ∈ E := by
      have : c = j⁻¹ * (x : G) := by rw [← he]; simp
      rw [this]
      exact E.mul_mem (E.inv_mem (hJE hj)) x.property
    have hcC : (⟨c, hcE⟩ : E) ∈ C := by
      intro y hy
      exact Subtype.ext (hc y hy)
    have hxE : x = (⟨j, hJE hj⟩ : E) * ⟨c, hcE⟩ := Subtype.ext he.symm
    rw [hxE]
    exact mul_mem (mem_sup_left hj) (mem_sup_right hcC)
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    have hi : i.range = R := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        exact j.property
      · intro hx
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [MonoidHom.range_comp, hi]
    have hm := congrArg (map q) hsup
    have hcq : C.map q = ⊥ := (map_eq_bot_iff C).mpr (QuotientGroup.ker_mk' C).ge
    simpa only [Subgroup.map_sup, hcq, sup_bot_eq,
      map_top_of_surjective q (QuotientGroup.mk'_surjective C)] using hm
  have hk : f.ker = center J := by
    ext j
    change q (i j) = 1 ↔ j ∈ center J
    change QuotientGroup.mk (i j) = 1 ↔ j ∈ center J
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro h
      apply mem_center_iff.mpr
      intro k
      exact Subtype.ext (congrArg (fun x : E => (x : G)) (h (i k) k.property))
    · intro h k hk
      exact Subtype.ext (congrArg (fun x : J => (x : G)) (mem_center_iff.mp h ⟨k, hk⟩))
  let e := QuotientGroup.liftEquiv (center J) hf hk.symm
  refine ⟨e.symm.toMonoidHom.comp q, ?_⟩
  intro j
  exact e.symm_apply_apply (QuotientGroup.mk' (center J) j)

/-- If the normal closure of an image in the layer contains a component,
its projection to that component's central quotient is nontrivial. -/
theorem IsComponent.exists_nontrivial_centralQuotient_projection
    {J : Subgroup G} (hJ : IsComponent G J)
    {T : Type*} [Group T] (f : T →* G)
    (hf : f.range ≤ componentLayer G)
    (hgen : J ≤ componentOrbit f.range (componentLayer G)) :
    ∃ π : T →* (J ⧸ center J), π.range ≠ ⊥ := by
  obtain ⟨π, hπ⟩ := hJ.exists_layer_centralQuotient_projection
  let E := componentLayer G
  let fE : T →* E := f.codRestrict E (fun x => hf ⟨x, rfl⟩)
  let ρ := π.comp fE
  refine ⟨ρ, ?_⟩
  intro hz
  let K := π.ker.map E.subtype
  have hDK : f.range ≤ K := by
    rintro _ ⟨t, rfl⟩
    have ht : ρ t = 1 := mem_bot.mp (hz ▸ (show ρ t ∈ ρ.range from ⟨t, rfl⟩))
    exact mem_map_of_mem E.subtype (show fE t ∈ π.ker from ht)
  have hEK : E ≤ normalizer (K : Set G) := by
    have hn := π.ker.le_normalizer_map E.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hn
  have hJK : J ≤ K := hgen.trans (iSup_conjugates_le_of_le_normalizer _ _ _ hDK hEK)
  have hzero (j : J) : QuotientGroup.mk' (center J) j = 1 := by
    obtain ⟨x, hx, he⟩ := hJK j.property
    have hxj : x = inclusion (le_sSup hJ) j := Subtype.ext he
    rw [← hπ j, ← hxj]
    exact hx
  let := hJ.2
  let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
  have hq : (QuotientGroup.mk' (center J)).range = ⊥ := by
    apply le_bot_iff.mp
    rintro _ ⟨j, rfl⟩
    exact hzero j
  exact top_ne_bot ((MonoidHom.range_eq_top.mpr
    (QuotientGroup.mk'_surjective (center J))).symm.trans hq)

end Theory.GroupTheory
