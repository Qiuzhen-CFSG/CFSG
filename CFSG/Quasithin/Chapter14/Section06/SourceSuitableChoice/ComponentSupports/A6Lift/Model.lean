module

public import CFSG.Quasithin.ChapterI.Section02.ModuleCovers.SymplecticFour.SylowFlag
public import CFSG.Quasithin.ChapterI.Section02.ModuleCovers.SymplecticFour.SylowFlag.Stabilizers
public import CFSG.Quasithin.ChapterI.Section02.ModuleCovers.OriginalAction
public import Theory.Representation.SymplecticConjugatePair.Ambient.Normalizer.Commutant
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# The marked binary A₆ orthogonal cover

The component image is the genuine derived matrix group Sp₄(2)′. Restricting
its six-letter polar isomorphism to commutators identifies it with A₆.
Transport of the natural representation and the five-space along a specified
group isomorphism preserves the covering map, its one-dimensional central
kernel, and the dual H¹ dimension. The additive commutant and the quadratic
geometry are supplied by the concrete matrix proofs, including over F₂.

The fixed radical of the cover is retained: only the natural quotient is
fixed-point-free. These are the model inputs to I.2.3 used in the choice
before 14.6.24, Aschbacher--Smith, printed pp.413 and 1038.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.A6Lift
open Representation Representation.OneCohomology
open Representation.OneCohomology.CentralCoverOriginalAction
open Representation.SymplecticFourOrthogonalCover
open ClassicalOrthogonal Module

abbrev Core := Representation.SymplecticFourOrthogonalCover.L (K := ZMod 2)
abbrev Natural := Representation.SymplecticFourOrthogonalCover.Natural (K := ZMod 2)
abbrev Cover := Space (K := ZMod 2)

/-- The actual Sp₄(2)′ carrier, not a family tag, is A₆. -/
def alternatingEquiv : Core ≃* alternatingGroup (Fin 6) := by
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

variable {H : Type*} [Group H] (e : H ≃* Core)

abbrev natural : Representation (ZMod 2) H Natural :=
  (binaryNatural (K := ZMod 2)).comp e.toMonoidHom
abbrev cover : Representation (ZMod 2) H Cover :=
  (binaryAction (K := ZMod 2)).comp e.toMonoidHom

/-- The original coordinate projection, after marking the component image. -/
def markedProjection : (cover e).IntertwiningMap (natural e) :=
  (projection (K := ZMod 2)).toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
    (fun h v => LinearMap.congr_fun ((projection (K := ZMod 2)).isIntertwining' (e h)) v)

@[simp] theorem markedProjection_apply (v : Cover) : markedProjection e v = v.1 := rfl

/-- The marked cover remains a genuine commutator-generated central cover. -/
theorem markedProjection_isCover : IsCover (restrictCoverMap (k := ZMod 2) (markedProjection e)) := by
  refine ⟨projection_surjective, ?_, ?_⟩
  · intro v hv h
    exact (projection_isCover (K := ZMod 2)).2.1 hv (e h)
  · change Coinvariants.ker ((binaryAction (K := ZMod 2)).comp e.toMonoidHom) = ⊤
    rw [commutator_comp_equiv]
    exact (binaryProjection_isCover (K := ZMod 2)).2.2

/-- The maximal central-kernel dimension is computed for the actual image H. -/
theorem marked_kernel_cohomology :
    finrank (ZMod 2) ((markedProjection e).toLinearMap.restrictScalars (ZMod 2)).ker =
      finrank (ZMod 2) (H1 (restrictScalars (k := ZMod 2) (natural e)).dual) := by
  let E := H1Congr (restrictScalars (k := ZMod 2) (natural e)).dual
    (binaryNatural (K := ZMod 2)).dual e
    (LinearEquiv.refl (ZMod 2) (Module.Dual (ZMod 2) Natural)) (by
      intro h v
      apply LinearMap.ext
      intro w
      change v (binaryNatural (e h⁻¹) w) = v (binaryNatural (e h)⁻¹ w)
      rw [map_inv])
  rw [E.finrank_eq]
  exact (binary_kernel_finrank (K := ZMod 2)).trans binary_dual_H1_finrank.symm

/-- Scalar commutant on the marked natural module, including additive maps. -/
theorem marked_scalar_commutant : HasScalarCommutant (natural e) := by
  intro f hf
  apply SymplecticConjugatePair.Ambient.Normalizer.Commutant.natural_centralizer_scalar f
  intro g v
  have h := hf (e.symm g) v
  change f (binaryNatural (e (e.symm g)) v) = binaryNatural (e (e.symm g)) (f v) at h
  rwa [e.apply_symm_apply] at h

/-- The natural module has no fixed vector for the component image. -/
theorem marked_natural_fixed : fixed (restrictScalars (k := ZMod 2) (natural e)) = ⊥ := by
  change fixed ((binaryNatural (K := ZMod 2)).comp e.toMonoidHom) = ⊥
  rw [fixed_comp_equiv, binary_natural_fixed]

/-- The cover has dimension five and has a nonzero one-dimensional fixed radical. -/
theorem marked_cover_dimensions :
    finrank (ZMod 2) Cover = 5 ∧
      fixed (cover e) = (formB 2 (ZMod 2)).polarBilin.ker ∧
      finrank (ZMod 2) (fixed (cover e)) = 1 := by
  have hf : fixed (cover e) = radical (K := ZMod 2) := by
    rw [cover, fixed_comp_equiv]
    exact fixed_radical
  exact ⟨space_finrank, hf.trans radical_eq_polar_ker, hf ▸ radical_finrank⟩

/-- The polar form upstairs is the literal pullback of the natural form. -/
theorem marked_polar (u v : Cover) :
    (formB 2 (ZMod 2)).polarBilin u v =
      (formD 2 (ZMod 2)).polarBilin (markedProjection e u) (markedProjection e v) := by
  simp only [polarB_apply, CharTwo.two_eq_zero, zero_mul, add_zero, markedProjection_apply]

/-- No singular vector lies in the projection kernel except zero. -/
theorem marked_kernel_anisotropic (u : Cover) (hp : markedProjection e u = 0)
    (hQ : formB 2 (ZMod 2) u = 0) : u = 0 := by
  apply quadratic_radicalB_trivial u _ hQ
  intro v
  rw [marked_polar e, hp, map_zero, LinearMap.zero_apply]

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.A6Lift
