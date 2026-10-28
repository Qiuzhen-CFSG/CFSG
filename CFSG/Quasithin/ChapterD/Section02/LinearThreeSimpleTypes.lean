module
public import CFSG.Quasithin.ChapterD.Section02.LinearThreeCentralTypes
public import Theory.Representation.PSL3Two.SmallModules

/-!
# Natural recognition for prescribed simple component maps

A nonzero map from a simple nontrivial component type identifies that type
with its image. Perfectness makes this image an Irr⁺ support, so the existing
natural-type classification gives actual binary SL₃ coordinates. Conjugating
an embedding by an original ambient actor preserves the same conclusion.

The terminal component-support consumer applies this to the two restrictions
of an irreducible constituent of the normal component orbit. This transfers
the earlier natural-type classification; it assumes no tensor decomposition.
Source: Aschbacher--Smith D.3.7 and F.9.18(5), pp.197--199,325--326,
in the natural-support argument of14.6.22, printed p.1038.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.ChapterD
open ChapterB.QuasisimpleSource
universe u v
variable {D V : Type u} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
variable {E : Type v} [AddCommGroup E] [Module (ZMod 2) E]

/-- Every nontrivial simple type occurring through a nonzero map is natural. -/
theorem natural_linear_three_of_simple_map
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [Group.IsPerfect K]
    (htypes : NaturalLinearThreeTypes ρ K)
    (τ : Representation (ZMod 2) K E) [τ.IsIrreducible] (hm : τ ≠ 1)
    (f : τ.IntertwiningMap (ρ.comp K.subtype)) (hf : f ≠ 0) :
    ∃ e : K ≃* BinaryLinearThree.Group,
      Nonempty (τ.Equiv (BinaryLinearThree.W.comp e.toMonoidHom)) := by
  have hfi := (IsIrreducible.injective_or_eq_zero f).resolve_right hf
  let c : τ.Equiv f.range.toRepresentation := Representation.Equiv.mk
    (LinearEquiv.ofInjective f.toLinearMap hfi) (by
      intro k
      apply LinearMap.ext
      intro v
      exact Subtype.ext (f.isIntertwining τ (ρ.comp K.subtype) k v))
  have hi : f.range.toRepresentation.IsIrreducible :=
    (RepEquiv.ofRepresentationEquiv c.symm).irreducible_of_euqiv inferInstance
  have hn : ¬ f.range.toSubmodule ≤ fixedSpace ρ K := by
    intro hh
    apply hm
    ext k v
    apply hfi
    exact (f.isIntertwining τ (ρ.comp K.subtype) k v).trans (hh ⟨v,rfl⟩ k)
  have hI := isIrrPlus_of_simple_noncentral ρ K f.range hi hn
  obtain ⟨F,hF,⟨a⟩⟩ := htypes f.range.toSubmodule hI
  let d := ExtensionConsequences.degreeOneNaturalEquiv F hF 3
  let e := a.groupEquiv.trans d.groupEquiv
  refine ⟨e,⟨Representation.Equiv.mk
    ((c.toLinearEquiv.trans a.linearEquiv).trans d.linearEquiv) ?_⟩⟩
  intro k
  apply LinearMap.ext
  intro v
  have hc := LinearMap.congr_fun (c.isIntertwining' k) v
  exact (congrArg (fun w => d.linearEquiv (a.linearEquiv w)) hc).trans
    ((congrArg d.linearEquiv (a.intertwines k (c v))).trans
      (d.intertwines (a.groupEquiv k) (a.linearEquiv (c v))))

/-- The same recognition applies to the literal conjugate component embedding. -/
theorem natural_linear_three_of_simple_conjugate_map
    (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [Group.IsPerfect K]
    (htypes : NaturalLinearThreeTypes ρ K)
    (i : K →* D) (t : D) (hi : ∀ k, i k = t*k.val*t⁻¹)
    (τ : Representation (ZMod 2) K E) [τ.IsIrreducible] (hm : τ ≠ 1)
    (f : τ.IntertwiningMap (ρ.comp i)) (hf : f ≠ 0) :
    ∃ e : K ≃* BinaryLinearThree.Group,
      Nonempty (τ.Equiv (BinaryLinearThree.W.comp e.toMonoidHom)) := by
  let g : τ.IntertwiningMap (ρ.comp K.subtype) := {
    toLinearMap := (ρ t⁻¹).comp f.toLinearMap
    isIntertwining' k := by
      apply LinearMap.ext
      intro v
      change ρ t⁻¹ (f (τ k v)) = ρ k.val (ρ t⁻¹ (f v))
      rw [f.isIntertwining]
      change ρ t⁻¹ (ρ (i k) (f v)) = ρ k.val (ρ t⁻¹ (f v))
      simp only [←Module.End.mul_apply,←map_mul,hi,mul_assoc,inv_mul_cancel_left] }
  have hg : g ≠ 0 := by
    intro hg
    apply hf
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change f v = 0
    apply (Representation.apply_bijective ρ t⁻¹).1
    rw [map_zero]
    exact congrArg (fun q : τ.IntertwiningMap (ρ.comp K.subtype) => q v) hg
  exact natural_linear_three_of_simple_map ρ K htypes τ hm g hg

/-- Recognition on a nested subrepresentation retains its literal conjugate
component embedding in the original module. -/
theorem natural_linear_three_of_nested_conjugate
    (ρ : Representation (ZMod 2) D V) (K N : Subgroup D) [Group.IsPerfect K]
    (htypes : NaturalLinearThreeTypes ρ K)
    (U : Subrepresentation (ρ.comp N.subtype))
    (j : K →* N) (s : D) (hj : ∀ k, (j k).val = s*k.val*s⁻¹)
    (W : Subrepresentation (U.toRepresentation.comp j))
    (hW : IsIrreducible W.toRepresentation) (hm : W.toRepresentation ≠ 1) :
    ∃ b : K ≃* BinaryLinearThree.Group,
      Nonempty (W.toRepresentation.Equiv (BinaryLinearThree.W.comp b.toMonoidHom)) := by
  let := hW
  let f : W.toRepresentation.IntertwiningMap (ρ.comp (N.subtype.comp j)) := {
    toLinearMap := U.toSubmodule.subtype.comp W.toSubmodule.subtype
    isIntertwining' _ := rfl }
  have hf : f ≠ 0 := by
    let : Nontrivial W.toSubmodule := Subrepresentation.irreducible_module_nontrivial W.toRepresentation
    obtain ⟨v,hv⟩ := exists_ne (0 : W.toSubmodule)
    intro hz
    apply hv
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun q : W.toRepresentation.IntertwiningMap (ρ.comp (N.subtype.comp j)) => q v) hz
  exact natural_linear_three_of_simple_conjugate_map ρ K htypes
    (N.subtype.comp j) s hj W.toRepresentation hm f hf

end CFSG.Quasithin.ChapterD
