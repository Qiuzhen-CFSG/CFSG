module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Frames
public import Theory.AtlasPort.LinearGroups.G2.TorusNormalization

/-!
# Extending one short-root element by the long-frame torus

An element acting as C(1) in the supplied additive Leech coordinates gives
all C(a): take the identity at zero and conjugate by the Peirce diagonal
with weights (a, a⁻¹, 1) otherwise. The octonion torus character proves
that these are the literal required root actions. The construction preserves
membership in C(I), and every nonzero value is conjugate to the original
element. Injectivity follows by testing coordinate 1 on the vector supported
at coordinate 3.

This is the parameter-extension step for Aschbacher, *Sporadic Groups*
(1994), Lemma 49.5, pp.283–284. It does not construct the local A₅ or prove
its involution marking. Those premises remain explicit in `shortFrameOfOne`;
`LocalGenerators.Short` consumes it with the scalar-class comparison.
No faithfulness of the action on the U-fixed space is assumed.
-/

open Matrix Atlas.Conway Atlas.Lattices Atlas.SplitOctonion
open scoped MatrixGroups
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators
open OctonionLocals
open PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight

/-- The actual action on all vectors of the supplied coordinate system. -/
def LongFrame.Intertwines (L : LongFrame) (g : LeechCentralQuotient) (x : Model F) : Prop :=
  ∀ v, quotientModTwoRepresentation g (L.coordinates v) = L.coordinates (action x v)

theorem LongFrame.intertwines_long (L : LongFrame) (A : SL(3,F)) :
    L.Intertwines (L.long A) (BlockRealization.blockHom A) :=
  equivariant_of_single _ _ _ (L.on_long A)

theorem LongFrame.Intertwines.mul {L : LongFrame} {g h : LeechCentralQuotient}
    {x y : Model F} (hg : L.Intertwines g x) (hh : L.Intertwines h y) :
    L.Intertwines (g * h) (x * y) := by
  intro v
  simp only [map_mul, LinearEquiv.mul_apply]
  rw [hh, hg]

theorem LongFrame.Intertwines.inv {L : LongFrame} {g : LeechCentralQuotient}
    {x : Model F} (h : L.Intertwines g x) : L.Intertwines g⁻¹ x⁻¹ := by
  intro v
  apply (quotientModTwoRepresentation g).injective
  rw [h]
  simp only [map_inv, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]

/-- The diagonal long element that scales the short-root parameter by a. -/
def shortTorus (a : Fˣ) : SL(3,F) :=
  diagonalSL (peirceWeights a 1) (peirceWeights_prod a 1)

theorem shortTorus_conjugates (a : Fˣ) :
    BlockRealization.blockHom (shortTorus a) * rootC (1 : F) *
      (BlockRealization.blockHom (shortTorus a))⁻¹ = rootC (a : F) := by
  rw [shortTorus, BlockRealization.blockHom_diagonal, torus_rootC, mul_one]

/-- The identity at zero and long-torus conjugates of the given element elsewhere. -/
def shortFromOne (L : LongFrame) (g : LeechCentralQuotient) (a : F) :
    LeechCentralQuotient := by
  classical
  exact if ha : a = 0 then 1 else
    L.long (shortTorus (Units.mk0 a ha)) * g * (L.long (shortTorus (Units.mk0 a ha)))⁻¹

theorem shortFromOne_mem (L : LongFrame) {g : LeechCentralQuotient}
    (hg : g ∈ centralizerI) (a : F) : shortFromOne L g a ∈ centralizerI := by
  unfold shortFromOne
  split
  · exact centralizerI.one_mem
  · exact centralizerI.mul_mem (centralizerI.mul_mem (L.long_mem _) hg)
      (centralizerI.inv_mem (L.long_mem _))

theorem shortFromOne_intertwines (L : LongFrame) {g : LeechCentralQuotient}
    (hg : L.Intertwines g (rootC 1)) (a : F) :
    L.Intertwines (shortFromOne L g a) (rootC a) := by
  unfold shortFromOne
  split
  · rename_i ha
    subst a
    intro v
    simp [rootC_zero]
  · rename_i ha
    have h := ((L.intertwines_long (shortTorus (Units.mk0 a ha))).mul hg).mul
      (L.intertwines_long (shortTorus (Units.mk0 a ha))).inv
    simpa only [shortTorus_conjugates, Units.val_mk0] using h

theorem shortFromOne_isConj (L : LongFrame) (g : LeechCentralQuotient)
    {a : F} (ha : a ≠ 0) : IsConj (shortFromOne L g a) g := by
  apply IsConj.symm
  apply isConj_iff.mpr
  refine ⟨L.long (shortTorus (Units.mk0 a ha)), ?_⟩
  simp only [shortFromOne, dif_neg ha]

/-- Extend one actually marked Leech element to the complete required frame. -/
def shortFrameOfOne (L : LongFrame) (g : LeechCentralQuotient)
    (hg : g ∈ centralizerI) (ha : L.Intertwines g (rootC 1))
    (hm : IsConj g markedInvolution) : ShortFrame L where
  short := shortFromOne L g
  short_mem := shortFromOne_mem L hg
  on_short a j b := shortFromOne_intertwines L ha a (Pi.single j b)
  marked := (shortFromOne_isConj L g one_ne_zero).trans hm


/-- The constructed parameter family is injective already on the fixed space;
no faithfulness assertion for the ambient centralizer is needed. -/
theorem shortFromOne_injective (L : LongFrame) {g : LeechCentralQuotient}
    (hg : L.Intertwines g (rootC 1)) : Function.Injective (shortFromOne L g) := by
  intro a b hab
  have ha := shortFromOne_intertwines L hg a (Pi.single 3 1)
  have hb := shortFromOne_intertwines L hg b (Pi.single 3 1)
  rw [hab] at ha
  have he := L.coordinates_injective (ha.symm.trans hb)
  have h := congrFun he 1
  simpa [action_rootC] using h

/-- Existence of a short frame is exactly the remaining marked one-parameter
construction. The reverse implication here performs the torus extension. -/
theorem nonempty_shortFrame_iff (L : LongFrame) :
    Nonempty (ShortFrame L) ↔ ∃ g ∈ centralizerI,
      L.Intertwines g (rootC 1) ∧ IsConj g markedInvolution := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.short 1, S.short_mem 1,
      equivariant_of_single _ _ _ (S.on_short 1), S.marked⟩
  · rintro ⟨g, hg, ha, hm⟩
    exact ⟨shortFrameOfOne L g hg ha hm⟩

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators
