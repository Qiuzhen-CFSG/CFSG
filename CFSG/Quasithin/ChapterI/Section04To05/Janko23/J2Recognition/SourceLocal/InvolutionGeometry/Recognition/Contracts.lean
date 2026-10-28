module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Models

/-!
# Root-four recognition before choosing the order-three vertex

The source first recognizes the centralizer and its root-four normalizer, with
the distinguished involution in the component. The order-three vertex can then
be aligned by conjugation in its centralizer. `UnalignedGeometry` records the
first step with literal subgroup embeddings; it asserts no existence theorem.

Source: Aschbacher, *Sporadic Groups* (1994), 47.1(1), pp.259–260.
-/

@[expose] public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition

variable {G : Type*} [Group G] [Finite G]

/-- The recognized local groups, before aligning their cubic subgroup with `D.X`.
The core and component are intrinsic to the full involution centralizer. -/
structure UnalignedGeometry (D : Seed G) (t : G) where
  model : SecondCentralizer D t
  component_eq : rootComponent t = model.fiveFactor
  z_mem_component : D.z ∈ rootComponent t
  normalizerEquiv : normalizer (rootCore t : Set G) ≃* (A4 × A5)
  normalizer_component :
    ((⊥ : Subgroup A4).prod (⊤ : Subgroup A5)).map
      ((normalizer (rootCore t : Set G)).subtype.comp normalizerEquiv.symm.toMonoidHom) =
      rootComponent t
  normalizer_core :
    ((pCore 2 A4).prod (⊥ : Subgroup A5)).map
      ((normalizer (rootCore t : Set G)).subtype.comp normalizerEquiv.symm.toMonoidHom) =
      rootCore t

/-- The small-centralizer branch of the printed Thompson calculation.
Excluding the resulting order still requires the source Sylow-normalizer argument. -/
theorem card_eq_of_small_centralizer {D : Seed G} (L : LocalCensus D)
    {t : G} (ht : OtherInvolution D t)
    (hC : Nat.card (involutionCentralizer t) = 48)
    (hcount : sourceCount D.z t t = 3) : Nat.card G = 51840 := by
  rw [source_order_formula ht, L.count_at_z t ht, hC, hcount]

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition
