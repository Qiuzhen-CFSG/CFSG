module

public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.Models
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil
public import CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions.Offenders
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Best offenders at the literal quotient pencil centralizer

Equivariance identifies the actual pointwise centralizer of the quotient
pencil span with its linear kernel. The offender deduction therefore gives
precisely its H-conjugates, in the faithful source actor D, and an actual
isomorphism D ≃ G₂(2). Best offenders are evaluated in the specified module
coordinates; the same coordinates identify the literal quotient U/V₁.

The point marking is constructed by Assembly, with no singularity premise.
The numerical rank/fixed-codimension bounds and the marked BinaryCore.elementary
classification are the explicit B.4.6 inputs owned by qt-b-04-g2. The sibling
qt-14-07-g2-pencil-centralizers supplies hcentralizer. Final instantiation of
these inputs stays with qt-14-07-g2-marked-pencil. This module imports neither
sibling proofs nor a source theorem containing the requested conclusion.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 14.7.55(5),
printed p.1066, PDF p.1083, and B.4.6(13), printed pp.88–90. Model imports use
the existing attributed ATLAS port (LICENSES/ATLAS.txt).
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions
open Atlas.G2 Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil
open CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions
variable {D Q W : Type*} [Group D] [Group Q] [AddCommGroup W] [Module (ZMod 2) W]

/-- The pointwise centralizer of the literal quotient pencil span is the
linear kernel in its actual equivariant coordinates. -/
theorem pencil_fixingSubgroup_eq [MulAction D Q]
    (σ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (i : D →* Model (ZMod 2)) (e : Multiplicative W ≃* Q)
    (he : ∀ d w, d • e (Multiplicative.ofAdd w) = e (Multiplicative.ofAdd (σ (i d) w)))
    (f : SingularMap W) (p : SingularPoints (ZMod 2)) :
    _root_.fixingSubgroup D
      (quotientPencilSpan (transportGeometry f.geometry e)
        ((transportGeometry f.geometry e).point p) : Set Q) =
        subspaceKernel (σ.comp i) (pencilSpan f p) ⊤ := by
  rw [quotientPencilSpan_eq]
  ext d
  rw [mem_fixingSubgroup_iff, mem_subspaceKernel]
  constructor
  · intro hd
    refine ⟨mem_top _, fun w hw => ?_⟩
    have h := hd (e (Multiplicative.ofAdd w)) ⟨Multiplicative.ofAdd w,hw,rfl⟩
    rw [he] at h
    exact congrArg Multiplicative.toAdd (e.injective h)
  · rintro ⟨_,hd⟩ q ⟨w,hw,rfl⟩
    change d • e (Multiplicative.ofAdd w.toAdd) = e (Multiplicative.ofAdd w.toAdd)
    rw [he]
    exact congrArg (fun v => e (Multiplicative.ofAdd v)) (hd w.toAdd hw)

/-- Clause (5) on the literal source quotient. The marking is the output of
`natural_source_actions` or `weyl_source_actions`. The full-actor centralizer
is the same `fixingSubgroup` used by the sibling clause-(4) calculation. -/
theorem source_quotient_ff_bestOffenders
    {H : Type*} [Group H] (π : H →* D) (hπ : Function.Surjective π)
    (U V₁ V₂ : Subgroup H) [(V₁.subgroupOf U).Normal]
    [MulAction D (U ⧸ V₁.subgroupOf U)]
    (σ : Representation (ZMod 2) (Model (ZMod 2)) W)
    (i : D →* Model (ZMod 2)) (hi : Function.Injective i)
    (e : Multiplicative W ≃* U ⧸ V₁.subgroupOf U)
    (he : ∀ d w, d • e (Multiplicative.ofAdd w) = e (Multiplicative.ofAdd (σ (i d) w)))
    (hderived : commutator (Model (ZMod 2)) ≤ i.range)
    (hRank : ∀ A : Subgroup (Model (ZMod 2)), A ≤ commutator (Model (ZMod 2)) →
      IsElementaryTwo A → rank A ≤ 2)
    (hOne : ∀ A : Subgroup (Model (ZMod 2)), IsElementaryTwo A →
      rank A = 1 → 2 ≤ fixedCodim σ A)
    (hTwo : ∀ A : Subgroup (Model (ZMod 2)), A ≤ commutator (Model (ZMod 2)) →
      IsElementaryTwo A → rank A = 2 → 3 ≤ fixedCodim σ A)
    (f : SingularMap W) (p : SingularPoints (ZMod 2))
    (hmark : (V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U)) =
      (transportGeometry f.geometry e).point p)
    (a : Model (ZMod 2))
    (hcentralizer : subspaceKernel σ (pencilSpan f p) ⊤ =
      BinaryCore.elementary.map (MulAut.conj a).toMonoidHom)
    (hB46 : ∀ B : Subgroup (Model (ZMod 2)), IsBestOffender σ B ↔
      ∃ g : Model (ZMod 2), BinaryCore.elementary.map (MulAut.conj g).toMonoidHom = B)
    (hff : IsFFModule (σ.comp i)) :
    (∃ j : D ≃* Model (ZMod 2), ∀ d, j d = i d) ∧
      {B : Subgroup D | IsBestOffender (σ.comp i) B} =
        Set.range (fun h : H =>
          (_root_.fixingSubgroup D
            (quotientPencilSpan (transportGeometry f.geometry e)
              ((V₂.subgroupOf U).map (QuotientGroup.mk' (V₁.subgroupOf U))) :
                Set (U ⧸ V₁.subgroupOf U))).map (MulAut.conj (π h)).toMonoidHom) := by
  rw [hmark, pencil_fixingSubgroup_eq σ i e he f p]
  exact source_ff_pencil_bestOffenders π hπ (σ.comp i) σ i hi
    (LinearEquiv.refl (ZMod 2) W) (fun _ _ => rfl) hderived hRank hOne hTwo f p
    (pencilSpan f p) (Submodule.map_id _) a hcentralizer hB46 hff

end CFSG.Quasithin.Chapter14.Section07.G2Exclusion.MarkedGeometry.MarkedPencil.SourceActions
