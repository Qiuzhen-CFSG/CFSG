module

public import Theory.SpecificGroups.SL2.SubgroupTwoCore
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.SpecificGroups.PSL2.SylowIntersections

/-!
# Internal conjugate pairs in binary SL₂

For a nonzero upper-root parameter a, the Weyl matrix w(a) is a word in u(a)
and its w(a)-conjugate. Hence it belongs to the join of any root subgroup
containing u(a) and that conjugate. The join is not a two-group because these
two matrices do not commute, and its two-core is trivial by root-normalizer
control. The original upper-root intersection is Sylow in every subgroup
containing u(a), and its normalizer is exactly the original Borel intersection.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.2.7,
printed p.218, the characteristic-two linear model branch.
-/

@[expose] public section

open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup.TwoConjugateWitness
variable {F : Type*} [Field F] [CharP F 2]
local notation "u" => transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one

noncomputable def rootWeyl (a : F) (ha : a ≠ 0) : SL(2,F) :=
  ⟨!![0,a;a⁻¹,0], by simp [det_fin_two, ha, CharTwo.neg_eq]⟩

lemma rootWeyl_word (a : F) (ha : a ≠ 0) :
    rootWeyl a ha = u a * (rootWeyl a ha * u a * (rootWeyl a ha)⁻¹) * u a := by
  have hm : (rootWeyl a ha * u a).val = (rootWeyl a ha).val * (u a).val := rfl
  have hi : ((rootWeyl a ha)⁻¹).val = adjugate (rootWeyl a ha).val := rfl
  apply Subtype.ext
  change (rootWeyl a ha).val =
    (u a).val * ((rootWeyl a ha * u a).val * ((rootWeyl a ha)⁻¹).val) * (u a).val
  rw [hm, hi]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootWeyl, transvection_coe, mul_apply, Fin.sum_univ_two,
      adjugate_fin_two, CharTwo.neg_eq, CharTwo.add_self_eq_zero, Matrix.vecMul, dotProduct, ha]

lemma rootWeyl_not_mem_borel (a : F) (ha : a ≠ 0) :
    rootWeyl a ha ∉ rankOneBorel F := by
  rw [mem_rankOneBorel_iff]
  simpa [rootWeyl] using inv_ne_zero ha

lemma rootWeyl_mem_join {V : Subgroup SL(2,F)} {a : F} (ha : a ≠ 0)
    (hu : u a ∈ V) :
    rootWeyl a ha ∈ V ⊔ V.map (MulAut.conj (rootWeyl a ha)).toMonoidHom := by
  let I : Subgroup SL(2,F) := V ⊔ V.map (MulAut.conj (rootWeyl a ha)).toMonoidHom
  have hv : u a ∈ I := (show V ≤ I from le_sup_left) hu
  have hw : rootWeyl a ha * u a * (rootWeyl a ha)⁻¹ ∈ I :=
    (show V.map (MulAut.conj (rootWeyl a ha)).toMonoidHom ≤ I from le_sup_right)
      (mem_map.mpr ⟨_,hu,rfl⟩)
  change rootWeyl a ha ∈ I
  rw [rootWeyl_word a ha]
  exact I.mul_mem (I.mul_mem hv hw) hv

lemma pGroup_commute [Finite F] (I : Subgroup SL(2,F)) (hI : IsPGroup 2 I)
    (x y : SL(2,F)) (hx : x ∈ I) (hy : y ∈ I) : x * y = y * x := by
  obtain ⟨S,hS⟩ := hI.exists_le_sylow
  let e := sylowEquivAdditive F 2 S
  have hh : (⟨x,hS hx⟩ : S) * ⟨y,hS hy⟩ = ⟨y,hS hy⟩ * ⟨x,hS hx⟩ := by
    apply e.symm.injective
    simp only [map_mul]
    exact mul_comm _ _
  exact congrArg Subtype.val hh

lemma rootWeyl_join_not_pGroup [Finite F] {V : Subgroup SL(2,F)} {a : F}
    (ha : a ≠ 0) (hu : u a ∈ V) :
    ¬ IsPGroup 2 (V ⊔ V.map (MulAut.conj (rootWeyl a ha)).toMonoidHom : Subgroup SL(2,F)) := by
  intro h
  have he := pGroup_commute _ h (u a) (rootWeyl a ha)
    (show u a ∈ (V ⊔ V.map (MulAut.conj (rootWeyl a ha)).toMonoidHom : Subgroup SL(2,F)) from
      (show V ≤ V ⊔ V.map (MulAut.conj (rootWeyl a ha)).toMonoidHom from le_sup_left) hu)
    (rootWeyl_mem_join ha hu)
  have hh := congrArg (fun g : SL(2,F) => g.val 0 0) he
  change ((u a).val * (rootWeyl a ha).val) 0 0 =
    ((rootWeyl a ha).val * (u a).val) 0 0 at hh
  simp [rootWeyl, transvection_coe, mul_apply, Fin.sum_univ_two, ha] at hh

lemma rootWeyl_join_twoCore [Finite F] {V : Subgroup SL(2,F)}
    (hV : V ≤ upperUnipotent F) {a : F} (ha : a ≠ 0) (hu : u a ∈ V) :
    pCore 2 (V ⊔ V.map (MulAut.conj (rootWeyl a ha)).toMonoidHom : Subgroup SL(2,F)) = ⊥ := by
  classical
  let W := V.map (MulAut.conj (rootWeyl a ha)).toMonoidHom
  let I := V ⊔ W
  have hVp : IsPGroup 2 V := (upperUnipotentSylow F 2).isPGroup'.to_le hV
  have hWp : IsPGroup 2 W := hVp.map _
  by_contra hn
  have hv := isPGroup_le_twoCore_of_ne_bot I hn (V.subgroupOf I) hVp.comap_subtype
  have hw := isPGroup_le_twoCore_of_ne_bot I hn (W.subgroupOf I) hWp.comap_subtype
  have ht : pCore 2 I = ⊤ := by
    apply top_unique
    have he : V.subgroupOf I ⊔ W.subgroupOf I = ⊤ := by
      apply Subgroup.map_injective I.subtype_injective
      rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show V ≤ I from le_sup_left),
        map_subgroupOf_eq_of_le (show W ≤ I from le_sup_right), ← MonoidHom.range_eq_map, range_subtype]
    rw [← he]
    exact sup_le hv hw
  have hp : IsPGroup 2 I := by
    have hc := pCore_isPGroup (p := 2) (G := I)
    rw [ht] at hc
    exact hc.of_equiv topEquiv
  exact rootWeyl_join_not_pGroup ha hu hp

lemma pGroup_le_upper_of_nonzero [Finite F] (P : Subgroup SL(2,F))
    (hP : IsPGroup 2 P) {a : F} (ha : a ≠ 0) (hu : u a ∈ P) :
    P ≤ upperUnipotent F := by
  have hPB : P ≤ rankOneBorel F := by
    intro g hg
    rw [mem_rankOneBorel_iff]
    have he := congrArg (fun g : SL(2,F) => g.val 0 0) (pGroup_commute P hP (u a) g hu hg)
    change ((u a).val * g.val) 0 0 = (g.val * (u a).val) 0 0 at he
    have hh : a * g.val 1 0 = 0 := by
      simpa [transvection_coe, mul_apply, Fin.sum_univ_two] using he
    exact (mul_eq_zero.mp hh).resolve_left ha
  calc
    P = P ⊓ normalizer (upperUnipotent F : Set SL(2,F)) := (inf_eq_left.mpr hPB).symm
    _ = P ⊓ (upperUnipotentSylow F 2 : Subgroup SL(2,F)) :=
      hP.inf_normalizer_sylow (upperUnipotentSylow F 2)
    _ ≤ upperUnipotent F := inf_le_right

noncomputable def intersectionSylow [Finite F] (I : Subgroup SL(2,F))
    {a : F} (ha : a ≠ 0) (hu : u a ∈ I) : Sylow 2 I where
  toSubgroup := (upperUnipotent F).subgroupOf I
  isPGroup' := (upperUnipotentSylow F 2).isPGroup'.comap_subtype
  is_maximal' := by
    intro P hP hUP
    apply le_antisymm _ hUP
    have hPu : u a ∈ P.map I.subtype := mem_map.mpr
      ⟨⟨u a,hu⟩,hUP ((mem_upperUnipotent F _).mpr ⟨a,rfl⟩),rfl⟩
    have hh := pGroup_le_upper_of_nonzero (P.map I.subtype) (hP.map _) ha hPu
    exact map_le_iff_le_comap.mp hh

omit [CharP F 2] in
lemma intersection_normalizer [Finite F] (I : Subgroup SL(2,F))
    {a : F} (ha : a ≠ 0) (hu : u a ∈ I) :
    normalizer ((upperUnipotent F).subgroupOf I : Set I) =
      (rankOneBorel F).subgroupOf I := by
  apply le_antisymm
  · intro g hg
    let W := ((upperUnipotent F).subgroupOf I).map I.subtype
    have hWU : W ≤ upperUnipotent F := by
      rintro x ⟨y,hy,rfl⟩
      exact hy
    have hW : W ≠ ⊥ := by
      intro hb
      have hm : u a ∈ W := mem_map.mpr
        ⟨⟨u a,hu⟩,(mem_upperUnipotent F _).mpr ⟨a,rfl⟩,rfl⟩
      rw [hb,mem_bot] at hm
      have he := congrArg (fun x : SL(2,F) => x.val 0 1) hm
      exact ha (by simpa [transvection_coe] using he)
    apply normalizer_le_rankOneBorel_of_le_upperUnipotent W hWU hW
    exact ((upperUnipotent F).subgroupOf I).le_normalizer_map I.subtype
      (mem_map.mpr ⟨g,hg,rfl⟩)
  · intro g hg
    apply mem_normalizer_iff.mpr
    intro x
    exact mem_normalizer_iff.mp hg (x : SL(2,F))

end Matrix.SpecialLinearGroup.TwoConjugateWitness
