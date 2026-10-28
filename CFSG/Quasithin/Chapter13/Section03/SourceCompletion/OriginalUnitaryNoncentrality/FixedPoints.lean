module
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global
public import Theory.Representation.G2BinaryNaturalNormalizer
public import Theory.Representation.G2NaturalTransport
/-!
# Fixed points in the original unitary chosen module

The literal induced automizer acts through the natural binary G₂ derived
representation. A vector centralized by the original component is therefore
fixed by the entire model. Nonzero-vector transitivity in that model forces
such a vector to vanish. Thus the unitary choice satisfies the fixed-point
condition of Hypothesis 13.3.13, without a noncentrality or F.9 assumption.

This supplies that applicability condition only; the subsequent reductions
and the plane noncentrality conclusion of 13.3.14 remain separate arguments.
Source: Aschbacher--Smith, Hypothesis 13.3.13 and the opening of the proof of
13.3.16, printed pp.890--891 and 894, combined manuscript of 1 March 2004.
The imported octonion model retains its ATLAS attribution and license.
-/

public section
open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
variable {G : Type*} [Group G] {V : Subgroup G} [IsElementaryAbelian 2 V]
/-- The actual natural component action discharges `C_V(L) = 1` in the
unitary application of Hypothesis 13.3.13. -/
theorem unitary_component_fixed_points_eq_bot (L : Subgroup G)
    (e : inducedAutomizer V L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E : Additive V ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2))
    (he : ∀ (l : inducedAutomizer V L) v, E (automizerRepresentation V l v) =
      Atlas.G2.Natural.derivedAction (ZMod 2) (e l) (E v)) :
    V ⊓ centralizer (L : Set G) = ⊥ := by
  apply bot_unique
  rintro x ⟨hxV,hxL⟩
  let v : Additive V := Additive.ofMul ⟨x,hxV⟩
  have hv : E v = 0 := by
    apply Atlas.G2.Natural.Transport.fixed_eq_zero
    intro g
    obtain ⟨i,rfl⟩ := e.surjective g
    rw [← he]
    congr 1
    obtain ⟨n,hn,hnmap⟩ := i.prop
    apply Subtype.ext
    change ((automizerRepresentation V i.val v).toMul : G) = x
    rw [← hnmap]
    change n.val * x * n.val⁻¹ = x
    have hnx : n.val * x = x * n.val := hxL _ hn
    rw [hnx, mul_inv_cancel_right]
  have hz : v = 0 := E.map_eq_zero_iff.mp hv
  exact congrArg (fun w : Additive V => w.toMul.val) hz
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
