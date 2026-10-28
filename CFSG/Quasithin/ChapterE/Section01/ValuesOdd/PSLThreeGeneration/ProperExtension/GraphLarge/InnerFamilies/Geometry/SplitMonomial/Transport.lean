module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Geometry.SplitMonomial.Model

/-!
# Sylow placement and literal matrix transport

An odd relative index places the full ambient Sylow subgroup in a conjugate
of the split monomial overgroup, with the conjugator inside the involution
centralizer. Every ambient element factors into an inner element and a graph
power. Graph fixes both the marked involution and the orthogonal signed swap,
so the same SL₃ conjugator witnesses both required conjugation identities.

The final theorem reduces `SolvableMixing` to the single numerical relative
index. It uses no inner-only replacement of the supplied ambient Sylow.
Source: Aschbacher--Smith E.1.2, E.1.5 and E.1.14(7), printed pp.209--210,
214; Aschbacher (1982), Lemma 4.11.
-/

public section
open Subgroup
open scoped MatrixGroups Pointwise
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry

private theorem sylow_le_conjugate_of_odd_relIndex
    {G : Type*} [Group G] [Finite G] (H C : Subgroup G)
    (hi : ¬ 2 ∣ H.relIndex C) (T : Sylow 2 G) (hTC : (T : Subgroup G) ≤ C) :
    ∃ g ∈ C, (T : Subgroup G) ≤ H.map (MulAut.conj g).toMonoidHom := by
  classical
  let N := H.subgroupOf C
  let R : Sylow 2 N := Classical.choice inferInstance
  have hRi : ¬ 2 ∣ ((R : Subgroup N).map N.subtype).index := by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul R.not_dvd_index hi
  let Q : Sylow 2 C := (R.isPGroup'.map N.subtype).toSylow hRi
  let S := T.subtype hTC
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C Q S
  have hSC : (S : Subgroup C) ≤ N.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact map_mono (show (Q : Subgroup C) ≤ N from map_subtype_le _)
  refine ⟨g.val, g.property, ?_⟩
  intro t ht
  obtain ⟨n, hn, he⟩ := hSC (show (⟨t, hTC ht⟩ : C) ∈ (S : Subgroup C) from ht)
  exact ⟨n.val, hn, congrArg Subtype.val he⟩

variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

omit [Finite F] [IsSimpleGroup PSL(3,F)] in
private theorem split_inner_range : (innerSL F).range = innerPart F := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨Matrix.PSL3.projection F g, rfl⟩
  · intro hx
    obtain ⟨y, hy⟩ := hx
    obtain ⟨g, rfl⟩ := Matrix.PSL3.projection_surjective F y
    exact ⟨g, Subtype.ext hy⟩

omit [Finite F] [IsSimpleGroup PSL(3,F)] in
private theorem split_inner_sup_graph : innerPart F ⊔ zpowers (graphElement F) = ⊤ := by
  apply Subgroup.map_injective (graphExtension F).subtype_injective
  rw [Subgroup.map_sup, MonoidHom.map_zpowers]
  change ((MulAut.innerSubgroup PSL(3,F)).subgroupOf (graphExtension F)).map _ ⊔
    zpowers (Matrix.PSL3.OuterSolvable.graph F) = _
  rw [map_subgroupOf_eq_of_le (show MulAut.innerSubgroup PSL(3,F) ≤ graphExtension F from le_sup_left)]
  rw [← MonoidHom.range_eq_map, range_subtype]
  rfl

omit [Finite F] [IsSimpleGroup PSL(3,F)] in
private theorem split_conjugation_pair (g : graphExtension F) :
    ∃ s : SL(3,F),
      innerSL F s * standardInner F * (innerSL F s)⁻¹ =
        g * standardInner F * g⁻¹ ∧
      innerSL F s * innerSL F (splitMixingMatrix F) * (innerSL F s)⁻¹ =
        g * innerSL F (splitMixingMatrix F) * g⁻¹ := by
  have hg : g ∈ innerPart F ⊔ zpowers (graphElement F) :=
    split_inner_sup_graph F ▸ mem_top g
  obtain ⟨u, hu, v, hv, rfl⟩ := mem_sup_of_normal_left.mp hg
  obtain ⟨s, rfl⟩ := (split_inner_range F).symm ▸ hu
  have hc₁ : v ∈ centralizer ({standardInner F} : Set (graphExtension F)) :=
    zpowers_le.mpr (split_graph_centralizes_standard F) hv
  have hc₂ : v ∈ centralizer ({innerSL F (splitMixingMatrix F)} : Set (graphExtension F)) :=
    zpowers_le.mpr (split_graph_centralizes_mixing F) hv
  have hc (w : graphExtension F) (h : v ∈ centralizer ({w} : Set (graphExtension F))) :
      (innerSL F s * v) * w * (innerSL F s * v)⁻¹ = innerSL F s * w * (innerSL F s)⁻¹ := by
    rw [mul_inv_rev]
    calc
      _ = innerSL F s * (v * w * v⁻¹) * (innerSL F s)⁻¹ := by simp only [mul_assoc]
      _ = _ := by rw [mem_centralizer_singleton_iff.mp h, mul_inv_cancel_right]
  exact ⟨s, (hc _ hc₁).symm, (hc _ hc₂).symm⟩

omit [IsSimpleGroup PSL(3,F)] in
/-- Ambient conjugation preserves a witness with an actual SL₃ coordinate conjugator. -/
theorem splitMonomial_conjugate_hasMixing (g : graphExtension F) :
    HasMixingElement F (g * standardInner F * g⁻¹)
      ((splitMonomialOvergroup F).map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨s, hs, hx⟩ := split_conjugation_pair F g
  exact ⟨s, hs, splitMixingMatrix F, splitMixingMatrix_mixes F,
    ⟨innerSL F (splitMixingMatrix F), splitMixingMatrix_mem F, hx.symm⟩⟩

/-- Odd relative index supplies solvable mixing for every full ambient Sylow. -/
theorem solvableMixing_of_splitMonomial_odd_relIndex (hodd : Odd (Nat.card F))
    (hi : ¬ 2 ∣ (splitMonomialOvergroup F).relIndex
      (centralizer ({standardInner F} : Set (graphExtension F)))) : SolvableMixing F := by
  intro T z hz hzI hTC
  have h2 := Field.two_ne_zero_of_odd_card F hodd
  obtain ⟨s, hs⟩ := exists_standard_coordinates F h2 z hz hzI
  let a := innerSL F s
  let e := MulAut.conj a
  let T₀ := T.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hT₀ : (T₀ : Subgroup (graphExtension F)) ≤
      centralizer ({standardInner F} : Set (graphExtension F)) := by
    rintro _ ⟨t, ht, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    rw [map_mul, map_mul]
    change e (e.symm t) * e (standardInner F) = e (standardInner F) * e (e.symm t)
    rw [MulEquiv.apply_symm_apply]
    change t * (a * standardInner F * a⁻¹) = (a * standardInner F * a⁻¹) * t
    rw [hs]
    exact mem_centralizer_singleton_iff.mp (hTC ht)
  obtain ⟨c, hc, hT₀c⟩ := sylow_le_conjugate_of_odd_relIndex _ _ hi T₀ hT₀
  let g := a * c
  let H := (splitMonomialOvergroup F).map (MulAut.conj g).toMonoidHom
  have hTH : (T : Subgroup (graphExtension F)) ≤ H := by
    intro t ht
    have ht₀ : e.symm t ∈ (T₀ : Subgroup (graphExtension F)) := ⟨t, ht, rfl⟩
    obtain ⟨k, hk, he⟩ := hT₀c ht₀
    refine ⟨k, hk, ?_⟩
    have he' := congrArg e he
    simpa [g, e, MulAut.conj_apply, mul_assoc] using he'
  have hgz : g * standardInner F * g⁻¹ = z := by
    have hc' : c * standardInner F * c⁻¹ = standardInner F := by
      rw [mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]
    calc
      _ = a * (c * standardInner F * c⁻¹) * a⁻¹ := by simp [g, mul_assoc]
      _ = z := by rw [hc']; exact hs
  refine ⟨H, hTH, ?_, ?_⟩
  · let : Group.IsSolvable (splitMonomialOvergroup F) := splitMonomialOvergroup_solvable F hodd
    exact Group.isSolvable_of_surjective ((MulAut.conj g).toMonoidHom.subgroupMap_surjective _)
  · rw [← hgz]
    exact splitMonomial_conjugate_hasMixing F g

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerGenerationGeometry
