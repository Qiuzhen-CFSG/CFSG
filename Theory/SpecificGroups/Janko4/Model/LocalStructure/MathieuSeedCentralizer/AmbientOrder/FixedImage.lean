module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.AmbientOrder.FixedImage.Coordinates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.AmbientOrder.FixedImage.ContractionRank

/-!
# A small-configuration route to the full seed action image bound

The full ambient centralizer preserves the quadratic and exterior invariants
restricted to the literal seed fixed space. An explicit eleven-dimensional
coordinate candidate and its marked configuration are defined separately.

The reduction below isolates three remaining mathematical obligations: the
actual action must restrict to configuration automorphisms, its restriction
must be faithful, and the concrete configuration stabilizer must have order at
most 908328960. The reduction proves no numerical bound until all three are
supplied. In particular, local-word actors alone do not discharge its premises.

The full centralizer order assembly remains in `AmbientOrder`; this route is
independent of its separate kernel bound. Source motivation is GLS3 Table 5.3i,
with the literal matrices and words documented in `Cardinality.Subgroup`.
-/

public section
namespace Janko4.LocalStructure.MathieuSeedCentralizer.AmbientOrder
open FixedImage

/-- A faithful restriction to the explicit finite configuration bounds the full
action image. Both restriction premises quantify over the entire image. -/
theorem fixedAction_image_card_le_of_configuration
    (hrestrict : ∀ g : fixedAction.range, ∃ h : codeStabilizer,
      g.val.val.comp codeLift = codeLift.comp h.val.val)
    (hfaithful : ∀ g h : fixedAction.range,
      g.val.val.comp codeLift = h.val.val.comp codeLift → g = h)
    (hcount : Nat.card codeStabilizer ≤ 908328960) :
    Nat.card fixedAction.range ≤ 908328960 := by
  classical
  let f : fixedAction.range → codeStabilizer := fun g => (hrestrict g).choose
  have hf (g : fixedAction.range) :
      g.val.val.comp codeLift = codeLift.comp (f g).val.val :=
    (hrestrict g).choose_spec
  have hinj : Function.Injective f := by
    intro g h he
    apply hfaithful g h
    exact (hf g).trans ((congrArg (fun k : codeStabilizer =>
      codeLift.comp k.val.val) he).trans (hf h).symm)
  exact (Nat.card_le_card_of_injective f hinj).trans hcount

end Janko4.LocalStructure.MathieuSeedCentralizer.AmbientOrder
