module

public import Theory.GroupTheory.ExtraspecialSquareSubgroups
public import Theory.SpecificGroups.ClassicalOrthogonal.BinaryD3Comparison
public import Theory.GroupAction.Defs
public import Theory.ElementaryAbelian.Injective

/-! A normalized subgroup of the original extraspecial group supplies an
invariant subspace in the marked eight-point square action. -/
public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.ExtraspecialSquare
variable {G : Type*} [Group G]

/-- Transport the literal subgroup image, preserving invariance, cardinality,
and the square criterion. No abstract representation is substituted. -/
theorem exists_invariant_image
    (P R Y : Subgroup G) [IsExtraspecial 2 P]
    (hRP : R≤P) (hYP : Y≤normalizer (P : Set G))
    (hYR : Y≤normalizer (R : Set G))
    (hZR : centerIn P<R) (hproper : R≠P)
    (e : (form P).IsometryEquiv (ClassicalOrthogonal.formD 3 (ZMod 2)))
    (f : Y→*Equiv.Perm (Fin 8))
    (he : ∀ (y : Y) (v : P⧸center P),
      (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv (f y)).val (e (Additive.ofMul v))=
        e (Additive.ofMul (quotientAut (center P)
          (P.normalizerMonoidHom (inclusion hYP y)) v))) :
    ∃ V : Submodule (ZMod 2) (ClassicalOrthogonal.VectorD 3 (ZMod 2)),
      V≠⊥ ∧ V≠⊤ ∧ 2*Nat.card V=Nat.card R ∧
      (∀ (g : Equiv.Perm (Fin 8)), g∈f.range → ∀ v∈V,
        (ClassicalOrthogonal.BinaryD3Comparison.symmetricEquiv g).val v∈V) ∧
      ((∀ v∈V, ClassicalOrthogonal.formD 3 (ZMod 2) v=0) → IsElementaryAbelian 2 R) := by
  let A := R.subgroupOf P
  let S := imageSpace P A
  let V := S.map e.toLinearEquiv.toLinearMap
  have hZA : center P≤A := by
    intro x hx
    exact hZR.le (show (x:G)∈centerIn P by
      rw [centerIn_eq_map_center]
      exact mem_map_of_mem P.subtype hx)
  have hS0 : S≠⊥ := by
    intro hh
    have hAZ := (imageSpace_eq_bot_iff A).mp hh
    apply hZR.not_ge
    intro x hx
    have hz : (⟨x,hRP hx⟩:P)∈center P := hAZ hx
    rw [centerIn_eq_map_center]
    exact ⟨⟨x,hRP hx⟩,hz,rfl⟩
  have hS1 : S≠⊤ := by
    intro hh
    have ha := (imageSpace_eq_top_iff A hZA).mp hh
    apply hproper
    apply le_antisymm hRP
    intro x hx
    have hh : (⟨x,hx⟩:P)∈A := ha ▸ mem_top _
    exact hh
  have hVc : Nat.card V=Nat.card S := (Nat.card_congr (e.toLinearEquiv.submoduleMap S).toEquiv).symm
  refine ⟨V,?_,?_,?_,?_,?_⟩
  · exact fun hh => hS0 (Submodule.map_eq_bot_iff.mp hh)
  · exact fun hh => hS1 (Submodule.map_eq_top_iff.mp hh)
  · rw [hVc]
    exact (imageSpace_card P A hZA).trans (Nat.card_congr (subgroupOfEquivOfLe hRP).toEquiv)
  · rintro g ⟨y,rfl⟩ v ⟨w,hw,rfl⟩
    have hpres (x : P) (hx : x∈A) : P.normalizerMonoidHom (inclusion hYP y) x∈A :=
      (mem_normalizer_iff.mp (hYR y.property) x.val).mp hx
    have hm := linearAction_mem_imageSpace A (P.normalizerMonoidHom (inclusion hYP y)) hpres w hw
    refine ⟨_,hm,?_⟩
    exact (he y w.toMul).symm
  · intro hsing
    let : IsElementaryAbelian 2 A := elementary_of_imageSpace_singular A (by
      intro w hw
      have hh := hsing (e w) (Submodule.mem_map_of_mem hw)
      exact (e.map_app w).symm.trans hh)
    exact IsElementaryAbelian.of_injective (subgroupOfEquivOfLe hRP).symm.toMonoidHom
      (subgroupOfEquivOfLe hRP).symm.injective

end Theory.GroupTheory.ExtraspecialSquare
