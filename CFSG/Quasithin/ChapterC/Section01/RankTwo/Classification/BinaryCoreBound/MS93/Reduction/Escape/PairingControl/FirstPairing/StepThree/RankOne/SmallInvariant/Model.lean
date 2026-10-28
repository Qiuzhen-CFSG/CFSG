module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.Transfer.SpanBound.Cocycle
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Source
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.Residuals
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Standard
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence.FixedGeometry.ValueConstruction.ModelProof.Transport

/-!
# Small invariant subspaces in a binary natural extension

Adapted from CyclicLocalization/SmallModule.lean, with invariance only under
the embedded two-residual. Each marked parabolic residual contains a literal
four-group of transvections. A four-group acting linearly on a subspace of order at most four has a nonidentity
involution fixing each specified vector: an orbit of four nonzero vectors is
impossible. The checked natural-cocycle theorem then places that vector in the
natural submodule plus the global fixed space. This includes nonsplit extensions.

Source: MS93, (1.5)(i), p.843, in the localization on p.883.
-/
public section
open Matrix Representation Representation.OneCohomology
open Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.RankOne.SmallInvariant

private abbrev Four := Multiplicative (ZMod 2 × ZMod 2)
private def fourMatrix (i : Bool) (x : Four) : SL :=
  if i then ⟨!![1,0,x.toAdd.1;0,1,x.toAdd.2;0,0,1],by simp [det_fin_three]⟩
  else ⟨!![1,x.toAdd.1,x.toAdd.2;0,1,0;0,0,1],by simp [det_fin_three]⟩

private def fourHom (i : Bool) : Four →* SL where
  toFun := fourMatrix i
  map_one' := by cases i <;> decide
  map_mul' := by
    have h : ∀ i x y, fourMatrix i (x*y) = fourMatrix i x * fourMatrix i y := by decide +kernel
    exact h i

private theorem four_injective (i : Bool) : Function.Injective (fourHom i) := by
  have h : ∀ i, Function.Injective (fourHom i) := by decide +kernel
  exact h i

private theorem four_mem (i : Bool) (x : Four) :
    fourHom i x ∈ residual (if i then Matrix.PSL3Two.lineParabolicSL else Matrix.PSL3Two.pointParabolicSL) := by
  cases i
  · simp only [Bool.false_eq_true, if_false, point_residual]
    have h : ∀ x, fourHom false x ∈ pointA := by decide +kernel
    exact h x
  · simp only [if_true, line_residual]
    have h : ∀ x, fourHom true x ∈ lineA := by decide +kernel
    exact h x

/-- A small residual-invariant subspace of a natural-by-trivial extension
lies in the natural submodule plus the whole-group fixed space. -/
theorem small_residual_invariant_le_natural_sup_fixed
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (σ : Representation (ZMod 2) SL W) (N : Subrepresentation σ)
    (marking : SL ≃* SL) (e : N.toSubmodule ≃ₗ[ZMod 2] (Fin 3 → ZMod 2))
    (he : ∀ g v, e (N.toRepresentation g v) =
      specialLinearNatural (k := ZMod 2) 3 (marking g) (e v))
    (htriv : HasTrivialQuotient N) (flag : SL) (i : Bool)
    (A : Submodule (ZMod 2) W) [Finite A] (hcard : Nat.card A ≤ 4)
    (hinv : ∀ g ∈ residual (modelParabolic flag i), ∀ w ∈ A, σ g w ∈ A) :
    A ≤ N.toSubmodule ⊔ fixed σ := by
  intro w hw
  by_cases hwzero : w = 0
  · subst w
    exact Submodule.zero_mem _
  let f : Four →* SL := (MulAut.conj flag).toMonoidHom.comp (fourHom i)
  have hf : Function.Injective f := (MulAut.conj flag).injective.comp (four_injective i)
  have hfmem (t : Four) : f t ∈ residual (modelParabolic flag i) := by
    unfold modelParabolic Matrix.PSL3Two.MarkedAutomorphisms.residual
    rw [← Subgroup.map_embedded_pResidual]
    exact Subgroup.mem_map_of_mem _ (four_mem i t)
  let orbit : Four → A := fun t => ⟨σ (f t) w, hinv _ (hfmem t) w hw⟩
  have hnot : ¬ Function.Injective orbit := by
    intro hi
    have hle : Nat.card A ≤ Nat.card Four := by simpa using hcard
    obtain ⟨t,ht⟩ := (hi.bijective_of_nat_card_le hle).surjective 0
    have ht' : σ (f t) w = 0 := congrArg Subtype.val ht
    have hh := congrArg (σ (f t⁻¹)) ht'
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, map_zero] at hh
    exact hwzero hh
  obtain ⟨u,v,huv,hne⟩ := Function.not_injective_iff.mp hnot
  let t : Four := v⁻¹*u
  have htne : f t ≠ 1 := by
    intro ht
    have : t = 1 := hf (ht.trans (map_one f).symm)
    exact hne (inv_mul_eq_one.mp (show v⁻¹*u = 1 from this)).symm
  have htsq : f t ^ 2 = 1 := by
    rw [← map_pow]
    have hs : ∀ x : Four, x^2 = 1 := by decide
    have ht : t^2 = 1 := hs t
    rw [ht,map_one]
  have hfix : σ (f t) w = w := by
    have hh := congrArg (σ (f v⁻¹)) (congrArg Subtype.val huv)
    simpa only [orbit, t, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using hh
  exact DistanceFour.Early.Containment.Transfer.SpanBound.fixed_involution_mem_natural_sup_fixed
    σ N marking e he htriv (f t) htsq htne w hfix

open Subgroup
open RankOnePairing.Incidence.FixedGeometry.ValueConstruction
open ModelProof

/-- The embedded line residual has zero fixed space in the natural module. -/
theorem line_residual_fixed_eq_bot (flag : SL) :
    fixedSpace (residual (modelParabolic flag true)) = ⊥ := by
  have hzero : fixedSpace lineA = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro v hv
    have hs := hv (BinaryLinearThree.shear (Multiplicative.ofAdd (1, 0))) (by decide)
    have hc := hv lineCycle (by decide)
    have test : ∀ w : Fin 3 → ZMod 2,
        (BinaryLinearThree.shear (Multiplicative.ofAdd (1, 0))).val.mulVec w = w →
        lineCycle.val.mulVec w = w → w = 0 := by decide
    exact test v.toAdd hs hc
  unfold modelParabolic Matrix.PSL3Two.MarkedAutomorphisms.residual
  rw [← map_embedded_pResidual]
  change fixedSpace ((residual Matrix.PSL3Two.lineParabolicSL).map _) = ⊥
  rw [line_residual, fixedSpace_conj, hzero, Subgroup.map_bot]

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.RankOne.SmallInvariant
