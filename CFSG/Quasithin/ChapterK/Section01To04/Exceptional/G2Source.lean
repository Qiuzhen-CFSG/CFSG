module

public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.SourceBound
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.G2CubicDegree.BinaryObstruction
public import CFSG.Quasithin.ChapterK.Section01To04.Exceptional.SourceAssembly

/-!
# Source recognition of the G₂ natural module

The completed cubic degree estimates apply to the literal component action
and its full linear normalizer. Natural-module recognition supplies an
actual group isomorphism and module intertwiner. The binary endpoint uses
the derived group of G₂(2) and its separate degree-eight obstruction.

These are representation-recognition theorems. The subsequent natural-module
offender geometry in B.4.6 is a separate source obligation.

Source: Guralnick–Malle, Classification of 2F-modules II, Lemma 8.5;
Aschbacher–Smith K.3 and B.4.6.
-/

public section

namespace CFSG.Quasithin.ChapterK.Exceptional.SourceAssembly
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition
attribute [local instance] ZMod.algebra

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
  [IsIrreducible (ρ.comp L.subtype)]

/-- Source natural-module recognition, retaining the actual derived model
and the intertwiner of the original component action. -/
theorem g2_natural
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {r : ℕ} (hr : 2 ≤ r) (hF : Nat.card F = 2 ^ r)
    (e : L ≃* Atlas.G2.Model F) (hf : Function.Injective ρ) (hc : cubicRatio ρ ≤ 2) :
    ∃ e' : L ≃* commutator (Atlas.G2.Model F),
      ∃ f : V ≃ₗ[ZMod 2] Atlas.G2.Natural.Space F,
        ∀ g : L, ∀ v, f (ρ g v) = derivedNaturalBinary F (e' g) (f v) := by
  apply g2_natural_of_normalizer_degree_bound ρ L hr hF e hf hc
  intro σ hi hf hc
  let := hi
  exact G2CubicDegree.source_degree_lt σ hr hF hf hc

attribute [local instance] BinarySix.scalars

/-- Source recognition at the binary derived-group endpoint. -/
theorem g2_binary_natural
    (e : L ≃* commutator (Atlas.G2.Model (ZMod 2)))
    (hf : Function.Injective ρ) (hc : cubicRatio ρ ≤ 2) :
    ∃ e' : L ≃* commutator (Atlas.G2.Model (ZMod 2)),
      ∃ f : V ≃ₗ[ZMod 2] Atlas.G2.Natural.Space (ZMod 2),
        ∀ g : L, ∀ v, f (ρ g v) = derivedNaturalBinary (ZMod 2) (e' g) (f v) := by
  apply g2_binary_natural_of_normalizer_degree_bound ρ L e hf hc
  intro σ hi hf hc
  let := hi
  exact G2CubicDegree.BinaryObstruction.binary_degree_le_eight σ hf hc

end CFSG.Quasithin.ChapterK.Exceptional.SourceAssembly
