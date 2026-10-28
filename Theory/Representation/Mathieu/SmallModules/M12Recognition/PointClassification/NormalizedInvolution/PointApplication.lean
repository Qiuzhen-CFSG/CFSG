module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.PointClassification.NormalizedInvolution

/-!
# Applying normalized involution conjugacy to the M₁₁ point classification

The certified involution theorem discharges the extension premise in
`equiv_point_of_normalizer_inputs`, with its literal normalizer restriction
and marked generators. Only normalizer classification remains explicit here;
its independent producer is `equiv_normalizer_of_faithful_degree_ten` in
`PointClassification.NormalizerClassification`. The point-classification
owner combines these two branches for the M₁₂ restriction.

Source application: the James input to Aschbacher–Smith G.7.3(2), printed
p.348/PDF p.359; James, J. Algebra 27 (1973), 57–111.
-/

public section
namespace Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution
open Sporadic.Mathieu

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The parent point-classification reduction with its involution-conjugacy
premise discharged by the actual binary M₁₁ algebra certificate. -/
theorem equiv_point_of_normalizer_classification
    (σ : Representation (ZMod 2) M11 V)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 10)
    (hlocal : ∀ τ : Representation (ZMod 2) m11Sylow11Normalizer V,
      Function.Injective τ → Module.finrank (ZMod 2) V = 10 →
      Nonempty (τ.Equiv normalizerRepresentation)) :
    Nonempty (σ.Equiv pointRepresentation) :=
  equiv_point_of_normalizer_inputs σ hf hd hlocal exists_equiv

end Representation.MathieuSmall.M12Recognition.PointClassification.NormalizedInvolution
