module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ModuleData
public import Theory.Representation.PSL3Two.IrreducibleCatalogue.Irreducibility
public import Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Vanishing of forms on a homogeneous natural quotient

The natural binary SL₃(2) module is irreducible and inequivalent to its dual,
so its invariant bilinear forms vanish. Applying this to each pair of summands
gives the same conclusion for any number of commonly marked natural copies.

On a commutator-generated module, fixed vectors lie in both radicals of any
invariant form. The form therefore descends through a surjective natural-copy
coordinate map whose kernel is exactly the fixed space. Consequently it is
zero even if the original extension by fixed vectors does not split.

This supplies the form obstruction for the binary specialization of
Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two* (1993),
(4.6.4), printed p.902, using the concrete catalogue of Aschbacher–Smith H.6.1.
-/

public section

set_option backward.isDefEq.respectTransparency false
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanOffender
namespace SelfDualFF
open AbelianCore.QuotientRecognition

private lemma natural_form_zero
    (B : BinaryLinearThree.Vector →ₗ[ZMod 2] Module.Dual (ZMod 2) BinaryLinearThree.Vector)
    (hB : ∀ g v w, B (BinaryLinearThree.W g v) (BinaryLinearThree.W g w) = B v w) :
    B = 0 := by
  let : IsIrreducible BinaryLinearThree.W :=
    BinaryLinearThree.IrreducibleCatalogue.natural_irreducible
  let : IsIrreducible BinaryLinearThree.W.dual :=
    BinaryLinearThree.IrreducibleCatalogue.dual_irreducible
  let f : BinaryLinearThree.W.IntertwiningMap BinaryLinearThree.W.dual := {
    toLinearMap := B
    isIntertwining' g := by
      apply LinearMap.ext
      intro v
      apply LinearMap.ext
      intro w
      change B (BinaryLinearThree.W g v) w = B v (BinaryLinearThree.W g⁻¹ w)
      have h := hB g v (BinaryLinearThree.W g⁻¹ w)
      simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel,
        map_one, Module.End.one_apply] using h
  }
  rcases IsIrreducible.bijective_or_eq_zero f with h | h
  · exact False.elim (BinaryLinearThree.AutomorphismAction.natural_not_equiv_dual
      ⟨f.ofBijective h⟩)
  · exact congrArg IntertwiningMap.toLinearMap h

private lemma homogeneous_form_zero {m : ℕ}
    (B : (Fin m → BinaryLinearThree.Vector) →ₗ[ZMod 2]
      Module.Dual (ZMod 2) (Fin m → BinaryLinearThree.Vector))
    (hB : ∀ g v w, B (fun i => BinaryLinearThree.W g (v i))
      (fun i => BinaryLinearThree.W g (w i)) = B v w) : B = 0 := by
  classical
  have hs (g : SL) (i : Fin m) (v : BinaryLinearThree.Vector) :
      (fun j => BinaryLinearThree.W g ((Pi.single i v : Fin m → BinaryLinearThree.Vector) j)) =
        Pi.single i (BinaryLinearThree.W g v) := by
    ext j
    by_cases h : j = i
    · subst j; simp
    · simp [Pi.single_eq_of_ne h]
  have hb (i j : Fin m) :
      B.compl₁₂ (LinearMap.single (ZMod 2) (fun _ : Fin m => BinaryLinearThree.Vector) i)
        (LinearMap.single (ZMod 2) (fun _ : Fin m => BinaryLinearThree.Vector) j) = 0 := by
    apply natural_form_zero
    intro g v w
    simpa only [LinearMap.compl₁₂_apply, LinearMap.single_apply, hs] using
      hB g (Pi.single i v) (Pi.single j w)
  have hb' (i j : Fin m) (v w : BinaryLinearThree.Vector) :
      B (Pi.single i v) (Pi.single j w) = 0 :=
    LinearMap.congr_fun (LinearMap.congr_fun (hb i j) v) w
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  conv_lhs => rw [← Finset.univ_sum_single v, ← Finset.univ_sum_single w]
  simp only [map_sum, LinearMap.sum_apply, hb', Finset.sum_const_zero,
    LinearMap.zero_apply]

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private lemma linear_form_zero_of_full (ρ : Representation (ZMod 2) SL V)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) (f : Module.Dual (ZMod 2) V)
    (hf : ∀ g v, f (ρ g v) = f v) : f = 0 := by
  have h : subspaceCommutator ρ ⊤ ⊤ ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, _, v, _, rfl⟩
    change f (ρ g v - v) = 0
    rw [map_sub, hf, sub_self]
  rw [hfull] at h
  ext v
  exact h Submodule.mem_top

/-- A commutator-generated module with a homogeneous natural fixed-space
quotient admits no nonzero invariant bilinear form. The marking is common to
all summands. No splitting or symmetry assumption is needed. -/
lemma form_zero_of_moduleQuotient (ρ : Representation (ZMod 2) SL V)
    (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤) {m : ℕ} (q : ModuleQuotient ρ m)
    (B : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
    (hB : ∀ g v w, B (ρ g v) (ρ g w) = B v w) : B = 0 := by
  have hk : q.projection.ker ≤ B.ker := by
    rw [q.kernel]
    intro c hc
    apply linear_form_zero_of_full ρ hfull
    intro g v
    have hgc : ρ g c = c := hc ⟨g, Subgroup.mem_top g⟩
    simpa only [hgc] using hB g c v
  have hk' : q.projection.ker ≤ B.flip.ker := by
    rw [q.kernel]
    intro c hc
    apply linear_form_zero_of_full ρ hfull
    intro g v
    have hgc : ρ g c = c := hc ⟨g, Subgroup.mem_top g⟩
    simpa only [hgc, LinearMap.flip_apply] using hB g v c
  let E := q.projection.quotKerEquivOfSurjective q.surjective
  let b := (B.liftQ₂ _ _ hk hk').compl₁₂ E.symm.toLinearMap E.symm.toLinearMap
  have hb (v w : V) : b (q.projection v) (q.projection w) = B v w := by
    simp [b, E]
  have hbinv (g : SL) (v w : Fin m → BinaryLinearThree.Vector) :
      b (fun i => BinaryLinearThree.W g (v i))
        (fun i => BinaryLinearThree.W g (w i)) = b v w := by
    obtain ⟨a, rfl⟩ := q.marking.surjective g
    obtain ⟨x, rfl⟩ := q.surjective v
    obtain ⟨y, rfl⟩ := q.surjective w
    have hx : (fun i => BinaryLinearThree.W (q.marking a) (q.projection x i)) =
        q.projection (ρ a x) := funext (fun i => (q.equivariant a x i).symm)
    have hy : (fun i => BinaryLinearThree.W (q.marking a) (q.projection y i)) =
        q.projection (ρ a y) := funext (fun i => (q.equivariant a y i).symm)
    rw [hx, hy, hb, hb, hB]
  have hz := homogeneous_form_zero b hbinv
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  rw [← hb, hz]
  rfl

end SelfDualFF
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanOffender
