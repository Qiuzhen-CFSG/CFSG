module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.G2
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.Geometry
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Compatibility with the existing G₂ block consumer

C.2.7's interface describes naturality using a surjective map from the
trace-zero octonions to six binary coordinates, with the scalar line as kernel.
The first isomorphism theorem identifies that module with the canonical G₂(2)′
natural quotient. Conversely, a basis of the canonical six-space constructs
such a projection. Both transports retain the exact core-quotient isomorphism
and conjugation equation.

This discharges the natural-module assumption used by the G₂ branch in
Chapter 13's `SourceSmallModels.BinaryRankTwo`. The forward transport adapts
its checked `G2Models.g2_linearBlock` proof at this earlier interface.

Source: Aschbacher--Smith C.1.30, printed p.135, and C.2.7(3), pp.145–147.
-/

@[expose] public section

open Atlas.G2.Natural
namespace CFSG.Quasithin.ChapterC.G2Source
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
variable {L : Type*} [Group L]

private noncomputable def sourceEquiv
    (pi : octonionTraceZero →ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (hpi : Function.Surjective pi) (hker : pi.ker = octonionScalarLine) :
    Space (ZMod 2) ≃ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
  (Submodule.quotEquivOfEq _ _ hker.symm).trans (pi.quotKerEquivOfSurjective hpi)

/-- The C.2.7 projection-and-kernel predicate supplies the canonical block type.
This uses the literal module and quotient marking already consumed by Chapter 13. -/
theorem of_source
    (h : CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.IsG2TwoBlock L) :
    ChapterC.IsG2TwoBlock L := by
  obtain ⟨hs, rho, ⟨b⟩, pi, hpi, hker, he⟩ := h
  let e := sourceEquiv pi hpi hker
  let eM := e.toAddEquiv.toMultiplicative
  let rho' : commutator (Atlas.G2.Model (ZMod 2)) →*
      MulAut (Multiplicative (Space (ZMod 2))) :=
    (MulAut.congr eM.symm).toMonoidHom.comp rho
  let b' : BlockModuleModel L rho' := {
    quotientIso := b.quotientIso
    moduleIso := b.moduleIso.trans eM.symm
    intertwining := by
      intro l v
      change eM.symm (b.moduleIso _) = eM.symm (rho _ (eM (eM.symm (b.moduleIso _))))
      rw [MulEquiv.apply_symm_apply, b.intertwining] }
  refine ⟨hs, rho', ⟨b'⟩, ?_⟩
  intro g w
  apply e.injective
  change e (e.symm (Multiplicative.toAdd (rho g (eM w)))) = _
  rw [LinearEquiv.apply_symm_apply]
  obtain ⟨x, hx⟩ := mk_surjective (ZMod 2) w.toAdd
  have he' := he g x (traceZeroAction (ZMod 2) g.val x) rfl
  change e (mk (ZMod 2) (traceZeroAction (ZMod 2) g.val x)) =
    (rho g (Multiplicative.ofAdd (e (mk (ZMod 2) x)))).toAdd at he'
  rw [← derivedAction_mk, hx] at he'
  exact he'.symm

/-- A canonical natural block discharges the existing C.2.7 natural-module
predicate. Coordinates give its surjective octonion projection with exactly
the scalar kernel and the original quotient-isomorphism marking. -/
theorem to_source (h : ChapterC.IsG2TwoBlock L) :
    CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.IsG2TwoBlock L := by
  classical
  obtain ⟨b⟩ := h.natural_model
  let e := (Module.finBasisOfFinrankEq (ZMod 2) (Space (ZMod 2))
    (finrank_space (ZMod 2))).equivFun
  let eM := e.toAddEquiv.toMultiplicative
  let rho : commutator (Atlas.G2.Model (ZMod 2)) →*
      MulAut (Multiplicative (Fin 6 → ZMod 2)) :=
    (MulAut.congr eM).toMonoidHom.comp g2TwoNaturalAction
  let b' : BlockModuleModel L rho := {
    quotientIso := b.quotientIso
    moduleIso := b.moduleIso.trans eM
    intertwining := by
      intro l v
      change eM (b.moduleIso _) = eM (g2TwoNaturalAction _ (eM.symm (eM (b.moduleIso _))))
      rw [MulEquiv.symm_apply_apply, b.intertwining] }
  let pi : octonionTraceZero →ₗ[ZMod 2] (Fin 6 → ZMod 2) :=
    e.toLinearMap.comp (mk (ZMod 2))
  refine ⟨h.short, rho, ⟨b'⟩, pi, e.surjective.comp (mk_surjective (ZMod 2)), ?_, ?_⟩
  · ext x
    change e (mk (ZMod 2) x) = 0 ↔ x ∈ octonionScalarLine
    rw [e.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero (scalarLine (ZMod 2))
  · intro g x y hy
    have hy' : y = traceZeroAction (ZMod 2) g.val x := Subtype.ext hy
    subst y
    change e (mk (ZMod 2) (traceZeroAction (ZMod 2) g.val x)) =
      e (derivedAction (ZMod 2) g (e.symm (e (mk (ZMod 2) x))))
    rw [LinearEquiv.symm_apply_apply]
    rfl

/-- The two source-faithful formulations impose exactly the same conditions. -/
theorem source_iff :
    CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.IsG2TwoBlock L ↔
      ChapterC.IsG2TwoBlock L := ⟨of_source, to_source⟩

end CFSG.Quasithin.ChapterC.G2Source
