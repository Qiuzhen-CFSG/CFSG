module

public import Theory.SpecificGroups.BinaryLinear.PerfectRadicalRows
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models

/-!
# Comparing the geometric three-block with an original simple marking

For a finite perfect cover of SL3(2) with two-group kernel, a nontrivial
three-dimensional binary action differs from the original marking by an
actual automorphism. The automorphism is retained in the conjugation formula.
-/

public noncomputable section
open Subgroup
namespace BinaryLinear
open SmallParabolicLevi OuterCyclic BinaryLinearThree
variable {E V : Type*} [Group E] [Finite E] [Group.IsPerfect E]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem sl_three_core : pCore 2 BinaryLinearThree.Group=⊥ := by
  apply Subgroup.map_injective (f := (slEquivLinear 3).toMonoidHom) (slEquivLinear 3).injective
  rw [pCore_map_iso,Subgroup.map_bot]
  exact linearGroup_twoCore_eq_bot

/-- A nontrivial binary three-space action of a perfect two-cover has the
original simple marking, up to one explicit automorphism. -/
theorem perfect_three_action_comparison
    (π : E →* BinaryLinearThree.Group) (hπ : Function.Surjective π)
    (hk : IsPGroup 2 π.ker) (f : E →* LinearGroup 3) (hf : f≠1) :
    ∃ α : MulAut BinaryLinearThree.Group,
      ∀ g : E, f g=slEquivLinear 3 (α (π g)) := by
  let : IsSimpleGroup BinaryLinearThree.Group := Atlas.Comparisons.Exceptional.sl3Two_simple
  let f' := (slEquivLinear 3).symm.toMonoidHom.comp f
  have hf' : f'≠1 := by
    intro he
    apply hf
    ext g : 1
    have hh := congrArg (slEquivLinear 3) (DFunLike.congr_fun he g)
    simpa only [f',MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply,MonoidHom.one_apply,map_one] using hh
  let : Group.IsNilpotent π.ker := hk.isNilpotent
  have hsurj : Function.Surjective f' :=
    (Theory.GroupTheory.hom_eq_one_or_surjective_of_simple_quotient π hπ f').resolve_left hf'
  have hm : π.ker.map f' ≤ pCore 2 BinaryLinearThree.Group :=
    le_sSup ⟨Subgroup.Normal.map inferInstance f' hsurj,hk.map f'⟩
  rw [sl_three_core] at hm
  have hker : π.ker ≤ f'.ker := by
    intro g hg
    exact hm (mem_map.mpr ⟨g,hg,rfl⟩)
  let a := π.liftOfSurjective hπ ⟨f',hker⟩
  have ha (g : E) : a (π g)=f' g := π.liftOfRightInverse_comp_apply _ _ _ g
  have has : Function.Surjective a := by
    intro g
    obtain ⟨x,hx⟩ := hsurj g
    exact ⟨π x,(ha x).trans hx⟩
  let α : MulAut BinaryLinearThree.Group :=
    MulEquiv.ofBijective a ⟨Finite.injective_iff_surjective.mpr has,has⟩
  refine ⟨α,?_⟩
  intro g
  change f g=slEquivLinear 3 (a (π g))
  rw [ha]
  exact ((slEquivLinear 3).apply_symm_apply (f g)).symm

omit [Finite E] [FiniteDimensional (ZMod 2) V] in
private theorem perfect_parabolic_nontrivial_block (W : Submodule (ZMod 2) V)
    (f : E →* parabolic W) (hf : f≠1) : (blockAction W).comp f≠1 := by
  intro hb
  have hmem (g : E) : (f g).val ∈ radical W := by
    have hh : f g ∈ (blockAction W).ker := DFunLike.congr_fun hb g
    rwa [ker_blockAction] at hh
  let r : E →* radical W := ((parabolic W).subtype.comp f).codRestrict _ hmem
  let : Group.IsSolvable (radical W) := Group.isSolvable_of_comm (by
    intro x y
    exact Subtype.ext (OuterCyclic.radical_commute W x.property y.property))
  let : Group.IsPerfect r.range := Group.IsPerfect.range r
  have hr : r.range=⊥ := by
    by_contra hr
    let : Nontrivial r.range := (nontrivial_iff_ne_bot _).mpr hr
    exact Group.IsPerfect.not_isSolvable r.range inferInstance
  have hz : r=1 := MonoidHom.range_eq_bot_iff.mp hr
  apply hf
  ext g : 1
  apply Subtype.ext
  exact congrArg (fun x : radical W => x.val) (DFunLike.congr_fun hz g)

/-- The actual 3+2 radical has two natural columns, with the single
comparison automorphism displayed against the original actor. -/
theorem perfect_radical_natural_marked
    (π : E →* BinaryLinearThree.Group) (hπ : Function.Surjective π)
    (hk : IsPGroup 2 π.ker) (W : Submodule (ZMod 2) V)
    (f : E →* parabolic W) (hf : f≠1)
    (a : W ≃ₗ[ZMod 2] Space 3) (b : (V ⧸ W) ≃ₗ[ZMod 2] Space 2) :
    ∃ (α : MulAut BinaryLinearThree.Group)
      (e : radical W ≃* Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector)),
      ∀ (g : E) (x y : radical W), y.val=(f g).val*x.val*(f g).val⁻¹ →
        (e y).toAdd=(BinaryLinearThree.W.prod BinaryLinearThree.W) (α (π g)) (e x).toAdd := by
  let A := (linearGroupCongr a).toMonoidHom.comp ((subspaceAction W).comp f)
  have hq := perfect_quotientAction_eq_one W f (by simpa using b.finrank_eq)
  have hA : A≠1 := by
    intro hA
    apply perfect_parabolic_nontrivial_block W f hf
    ext g : 1
    apply Prod.ext
    · apply (linearGroupCongr a).injective
      change linearGroupCongr a (subspaceAction W (f g))=linearGroupCongr a 1
      have h := DFunLike.congr_fun hA g
      simpa only [A,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MonoidHom.one_apply,map_one] using h
    · exact DFunLike.congr_fun hq g
  obtain ⟨α,hα⟩ := perfect_three_action_comparison π hπ hk A hA
  obtain ⟨e,he⟩ := perfect_radical_natural_rows W f a b
  refine ⟨α,e,?_⟩
  intro g x y hy
  rw [he g x y hy]
  change (A g ((e x).toAdd.1),A g ((e x).toAdd.2))=_
  rw [hα]
  rfl

/-- The actual 2+3 radical has two dual rows, with the single comparison
automorphism displayed against the original actor. -/
theorem perfect_radical_dual_marked
    (π : E →* BinaryLinearThree.Group) (hπ : Function.Surjective π)
    (hk : IsPGroup 2 π.ker) (W : Submodule (ZMod 2) V)
    (f : E →* parabolic W) (hf : f≠1)
    (a : W ≃ₗ[ZMod 2] Space 2) (b : (V ⧸ W) ≃ₗ[ZMod 2] Space 3) :
    ∃ (α : MulAut BinaryLinearThree.Group)
      (e : radical W ≃* Multiplicative
        (Module.Dual (ZMod 2) BinaryLinearThree.Vector × Module.Dual (ZMod 2) BinaryLinearThree.Vector)),
      ∀ (g : E) (x y : radical W), y.val=(f g).val*x.val*(f g).val⁻¹ →
        (e y).toAdd=(BinaryLinearThree.W.dual.prod BinaryLinearThree.W.dual)
          (α (π g)) (e x).toAdd := by
  let A := (linearGroupCongr b).toMonoidHom.comp ((quotientAction W).comp f)
  have hs := perfect_subspaceAction_eq_one W f (by simpa using a.finrank_eq)
  have hA : A≠1 := by
    intro hA
    apply perfect_parabolic_nontrivial_block W f hf
    ext g : 1
    apply Prod.ext
    · exact DFunLike.congr_fun hs g
    · apply (linearGroupCongr b).injective
      change linearGroupCongr b (quotientAction W (f g))=linearGroupCongr b 1
      have h := DFunLike.congr_fun hA g
      simpa only [A,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MonoidHom.one_apply,map_one] using h
  obtain ⟨α,hα⟩ := perfect_three_action_comparison π hπ hk A hA
  obtain ⟨e,he⟩ := perfect_radical_dual_rows W f a b
  refine ⟨α,e,?_⟩
  intro g x y hy
  rw [he g x y hy]
  change (((e x).toAdd.1).comp ((A g)⁻¹).toLinearMap,
    ((e x).toAdd.2).comp ((A g)⁻¹).toLinearMap)=_
  rw [hα,←map_inv]
  rfl

end BinaryLinear
