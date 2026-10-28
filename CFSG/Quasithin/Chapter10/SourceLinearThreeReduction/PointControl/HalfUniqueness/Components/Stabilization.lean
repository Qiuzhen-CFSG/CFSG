module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.Components.Ranks
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.QuotientStructure
public import Theory.GroupTheory.CComponent.NonsolvableNormalIntersection

/-!
# The intersection with M fixes each original factor

M permutes the two original factors. An element of H also preserves each
normal containing component. If it exchanged the factors, the nonsolvable
second factor would lie in both containing components; normality and the
minimal nonsolvable property of C-components would identify them.
Thus distinctness makes H ∩ M stabilize both factors separately.

This supplies the normalizer premise for the C.2.6 Fitting-preimage argument
in the constrained branch of 10.2.6, printed pp.748--749.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {H : Subgroup G} {t : G} {K₁ K₂ : Subgroup H}

/-- Distinctness and relative normality prohibit exchange inside H ∩ M. -/
theorem ContainingPair.intersection_normalizes_left (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) (hne : K₁ ≠ K₂) :
    H ⊓ D.maximalLocal ≤ normalizer (L : Set G) := by
  let B := (L.map (MulAut.conj t).toMonoidHom).subgroupOf H
  let : K₁.Normal := C.first_normal
  have hmap : (K₁.map H.subtype).subgroupOf H = K₁ :=
    comap_map_eq_self_of_injective H.subtype_injective K₁
  have hNK : H ≤ normalizer (K₁.map H.subtype : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (map_subtype_le K₁)).mp
      (hmap.symm ▸ C.first_normal)
  have hLK : L ≤ K₁.map H.subtype := by
    have hh := map_mono (f := H.subtype) C.first_le
    rwa [map_subgroupOf_eq_of_le C.left_le] at hh
  have hB : ¬ Group.IsSolvable B := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable D.maximal.1
      (Group.isSolvable_of_isSolvable_injective
        (f := C.rightEquiv.toMonoidHom) C.rightEquiv.injective)
  intro m hm
  apply mem_normalizer_iff_map_conj_eq.mpr
  rcases source_nonnormal_maximal_pair D hn C.t_mem C.t_not_normalizes m hm.2 with he | he
  · exact he
  · have hBK : L.map (MulAut.conj t).toMonoidHom ≤ K₁.map H.subtype := by
      rw [←he,←mem_normalizer_iff_map_conj_eq.mp (hNK hm.1)]
      exact map_mono hLK
    have hB₁ : B ≤ K₁ := by
      have hh := subgroupOf_mono H hBK
      rwa [hmap] at hh
    have hK₂K₁ := C.second_component.le_normal_of_nonsolvable_subgroup hB C.second_le hB₁
    exact (hne (C.second_component.eq_of_le C.first_component hK₂K₁).symm).elim

/-- The same intersection fixes the literal exchanged factor. -/
theorem ContainingPair.intersection_normalizes_right (C : ContainingPair D H t K₁ K₂)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) (hne : K₁ ≠ K₂) :
    H ⊓ D.maximalLocal ≤ normalizer (L.map (MulAut.conj t).toMonoidHom : Set G) :=
  (le_inf (C.intersection_normalizes_left hn hne) inf_le_right).trans
    (source_nonnormal_component_normalizer_fixes_opposite D hn C.t_mem C.t_not_normalizes)

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness
