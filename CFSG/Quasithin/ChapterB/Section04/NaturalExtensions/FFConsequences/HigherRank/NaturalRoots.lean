module
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.HigherRank.Blocks
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.HigherRank.RootRelations
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.HigherRank.Transport
public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FFConsequences.HigherRank.NaturalRoots.Matrix

/-!
# Common-axis quadratic roots in actual natural extensions

An ordinary section of the literal quotient gives matrix derivations. The
uniform natural root calculation forces common-column double displacements
to vanish on the original extension. The final applications retain the
original DoubleNatural group marking and transport every degree-one field
carrier through `binaryForm`, without changing the submodule or quotient.

This supplies the natural-orientation root identities needed by the
higher-dimensional branch of Aschbacher–Smith B.4.9(2)(i), printed pp.92–95.
No FF or splitting conclusion is assumed. Construction of the axis four-group
and final splitting assembly belong to `HigherRank`.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Representation Matrix
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.HigherRank
variable {n : ℕ}

private lemma natural_matrix (g : SpecialLinearGroup (Fin n) (ZMod 2)) :
    LinearMap.toMatrix' (specialLinearNatural (k := ZMod 2) n g) = g.val :=
  LinearMap.toMatrix'_toLin' g.val

private lemma natural_root_matrix {i j : Fin n} (hij : i ≠ j) :
    LinearMap.toMatrix' (specialLinearNatural (k := ZMod 2) n
      (SpecialLinearGroup.transvection hij 1) - 1) = Matrix.single i j 1 := by
  rw [map_sub, natural_matrix, LinearMap.toMatrix'_one, SpecialLinearGroup.transvection_coe]
  exact add_sub_cancel_left _ _

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- Common-axis root pairs act quadratically on the original extension with
both literal factors identified with the same natural representation. -/
theorem natural_extension_root_product (hn : 6 ≤ n)
    (ρ : Representation (ZMod 2) (SpecialLinearGroup (Fin n) (ZMod 2)) V)
    (N : Subrepresentation ρ)
    (en : N.toRepresentation.Equiv (specialLinearNatural (k := ZMod 2) n))
    (eq : N.quotientRepresentation.Equiv (specialLinearNatural (k := ZMod 2) n))
    {i j k : Fin n} (hij : i ≠ j) (hkj : k ≠ j) :
    (ρ (SpecialLinearGroup.transvection hij 1) - 1) *
      (ρ (SpecialLinearGroup.transvection hkj 1) - 1) = 0 := by
  obtain ⟨b⟩ := exists_extensionBlocks N en eq
  let c (g : SpecialLinearGroup (Fin n) (ZMod 2)) := LinearMap.toMatrix' (b.block g)
  have hc : IsNaturalDerivation c := by
    intro g h
    dsimp only [c]
    rw [b.derivation, map_add, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
      natural_matrix, natural_matrix]
  apply b.displacement_product
  · apply LinearMap.toMatrix'.injective
    rw [LinearMap.toMatrix'_mul, natural_root_matrix, natural_root_matrix, map_zero]
    exact Matrix.single_mul_single_of_ne _ _ _ _ hkj.symm _
  · apply LinearMap.toMatrix'.injective
    rw [LinearMap.toMatrix'_mul, natural_root_matrix, natural_root_matrix, map_zero]
    exact Matrix.single_mul_single_of_ne _ _ _ _ hkj.symm _
  · apply LinearMap.toMatrix'.injective
    rw [map_add, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
      natural_root_matrix, natural_root_matrix, map_zero]
    exact naturalDerivation_root_product hn hc hij hkj

open QuasisimpleSource
variable {G : Type*} [Group G] {ρ : Representation (ZMod 2) G V}

/-- Pull the common-column roots back through the original natural marking.
The conclusion concerns the given representation, submodule and quotient. -/
theorem binary_natural_root_product (d : DoubleNatural BinaryField.two n ρ)
    (hn : 6 ≤ n)
    (eQ : d.space.quotientRepresentation.Equiv d.space.toRepresentation)
    {i j k : Fin n} (hij : i ≠ j) (hkj : k ≠ j) :
    (ρ (d.natural.groupEquiv.symm (SpecialLinearGroup.transvection hij 1)) - 1) *
      (ρ (d.natural.groupEquiv.symm (SpecialLinearGroup.transvection hkj 1)) - 1) = 0 := by
  let f := d.natural.groupEquiv
  let τ := ρ.comp f.symm.toMonoidHom
  let N : Subrepresentation τ :=
    ⟨d.space.toSubmodule, fun g _ hv => d.space.apply_mem_toSubmodule (f.symm g) hv⟩
  let en : N.toRepresentation.Equiv (linearNatural BinaryField.two n) :=
    .mk d.natural.linearEquiv (by
      intro g
      apply LinearMap.ext
      intro v
      exact (d.natural.intertwines (f.symm g) v).trans (by rw [f.apply_symm_apply]; rfl))
  let eq : N.quotientRepresentation.Equiv N.toRepresentation :=
    .mk eQ.toLinearEquiv (by
      intro g
      apply LinearMap.ext
      intro v
      exact LinearMap.congr_fun (eQ.isIntertwining' (f.symm g)) v)
  exact natural_extension_root_product hn τ N en (eq.trans en) hij hkj

variable {F : BinaryField}

/-- The actual same-orientation `DoubleNatural` application for every carrier
of the field of two elements, with the original actors and module retained. -/
theorem degree_one_natural_root_product (d : DoubleNatural F n ρ)
    (hF : F.degree = 1) (hn : 6 ≤ n)
    (eQ : d.space.quotientRepresentation.Equiv d.space.toRepresentation)
    {i j k : Fin n} (hij : i ≠ j) (hkj : k ≠ j) :
    (ρ ((binaryForm d hF).natural.groupEquiv.symm
      (SpecialLinearGroup.transvection hij 1)) - 1) *
      (ρ ((binaryForm d hF).natural.groupEquiv.symm
        (SpecialLinearGroup.transvection hkj 1)) - 1) = 0 :=
  binary_natural_root_product (binaryForm d hF) hn eQ hij hkj

end CFSG.Quasithin.ChapterB.NaturalExtensions.HigherRank
