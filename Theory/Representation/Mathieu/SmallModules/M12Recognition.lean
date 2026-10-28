module

public import Theory.Representation.Mathieu.SmallModules.M12Recognition.Reduction

/-!
# Reduction of the small faithful binary M₁₂ recognition theorem

The unconditional restriction lemmas prove degree ten and irreducibility
on the actual M₁₁ point stabilizer. The assembly below converts a complete
M₁₁ degree-ten classification and rigidity of its extending M₁₂ actions
into recognition of the original module, including its group marking.

Those two classification inputs remain explicit; the unconditional James
recognition result is not yet proved here. The target is the ten-dimensional
augmentation space modulo constants, as specified in `SmallModules.Models`.

Source: Aschbacher--Smith, G.7.3(2), printed p.348 (PDF p.359), and its
citation of G. D. James, J. Algebra 27 (1973), 57--111.
-/

public section
namespace Representation.MathieuSmall.M12Recognition
open Sporadic.Mathieu

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) M12 V)

/-- Apply the local classification to the literal restriction, discharging
its faithfulness, irreducibility and dimension premises. The two remaining
universal classification inputs are not asserted by this theorem. -/
theorem isM12Heart_of_local_classification [FiniteDimensional (ZMod 2) V]
    (hf : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V ≤ 10)
    (hlocal : ∀ σ : Representation (ZMod 2) M11 V,
      Function.Injective σ → σ.IsIrreducible → Module.finrank (ZMod 2) V = 10 →
      Nonempty (σ.Equiv pointRepresentation))
    (hextension : ∀ τ : Representation (ZMod 2) M12 M12Heart,
      Function.Injective τ → τ.IsIrreducible →
      (∀ g : M11, τ (pointEmbedding g) = m12HeartRepresentation (pointEmbedding g)) →
      IsM12Heart τ) : IsM12Heart ρ := by
  apply isM12Heart_of_point_inputs ρ hf _ hextension
  exact hlocal (ρ.comp pointEmbedding) (hf.comp pointEmbedding_injective)
    (point_restriction_isIrreducible ρ hf hd) (finrank_eq_ten ρ hf hd)

end Representation.MathieuSmall.M12Recognition
