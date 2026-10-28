module

public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.SourceStatements
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.LocalControl
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.IntersectionBounds
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.DiagonalConstruction.Algebra
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.DiagonalConstruction.Inputs
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.DiagonalConstruction.Choice.Four
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.DiagonalConstruction.Choice.GeometryInput
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.StrongClosure.GlobalClosure.ContraryFusion.DiagonalConstruction.Choice.NormalizerGeometry

/-!
# Constructing the marked diagonal four

Clause (c) selects an involution v of A₁ outside the actual conjugate Hᵍ.
The fixed intersection then excludes membership in A₂. The pair-action and
Sylow-placement geometry makes x rootless in C(t), so the diagonal image contains a
four through x = vvᵗ. Choosing the normalizing generator preserves that four,
and its nontrivial square together with the order-two kernel gives order four
for the preimage.

The final theorem discharges the normalizer geometry in the conditional
assembly below. It handles a starting involution in either factor and retains
the literal outside conjugate factor normalized by the selected diagonal.

Source: Aschbacher, *On finite groups of component type* (1975), Lemma 3.4,
printed p.95, the rootless-involution argument through “Then u² = z”.
-/

@[expose] public section
open Subgroup Theory.GroupTheory BenderSuzuki.PFchapter1section1
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
variable {G : Type*} [Group G] [Finite G] {S : Sylow 2 G} {A₁ A₂ : Subgroup G}

/-- The diagonal image and its marked preimage discharge the algebraic
part of the source choice from the two normalizer-geometry clauses. -/
theorem MinimalCounterexample.diagonalChoice_of_normalizer_geometry
    (m : MinimalCounterexample S A₁ A₂) (l : LocalControl S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha2 : orderOf a = 2)
    (hg : g ∉ intersectionGenerated A₁ A₂) (ht : g⁻¹ * a * g ∈ S)
    (hcap : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2)
    (geometry : DiagonalNormalizerGeometry A₁ A₂ g (g⁻¹ * a * g)) :
    DiagonalChoice A₁ A₂ (g⁻¹ * a * g) := by
  let t := g⁻¹ * a * g
  have ha1 : a ≠ 1 := by intro he; simp [he] at ha2
  have ht2 : orderOf t = 2 := by
    simpa only [t, MulAut.conj_apply, inv_inv] using
      (MulAut.conj g⁻¹).orderOf_eq a |>.trans ha2
  have hs := l.swap_of_outside_transporter m.setup ha ha1 hg ht
  have hmodel := m.not_model_of_intersection_card_two l ha ha1 hg ht hcap
  obtain ⟨v, hv, hv2, hvHg⟩ :=
    DiagonalConstruction.exists_left_involution_outside_conjugate m.setup l hg
  have hvout := DiagonalConstruction.outside_conjugate_not_mem_right
    m.setup ha ha1 hs hcap hv hvHg
  have hroot := geometry.rootless v hv hv2 hvout hvHg
  have hvroot := DiagonalConstruction.diagonal_preimage_rootless m.setup hs.1 ht2 hv hroot
  obtain ⟨u, hu, hy2, hfour⟩ := DiagonalConstruction.diagonal_image_four_of_rootless
    m.setup hs ht2 hcap hmodel hv hv2 hvout hroot
  obtain ⟨u', hu', hu2, k, hk, hB⟩ :=
    geometry.placement v hv hv2 hvout hvHg u hu hy2 hfour
  have hx2 := DiagonalConstruction.diagonal_involution m.setup hs hcap hv hv2 hvout
  obtain ⟨hu'A, hy'2, hfour'⟩ :=
    DiagonalConstruction.diagonal_four_replace m.setup hs.1 hv hu hx2 hy2 hfour hu'
  have hu'4 := DiagonalConstruction.diagonal_preimage_order_four m.setup hs hcap hu'A hy'2 hu2
  exact ⟨u', hu'A, hu'4, hy'2, ⟨v, hv, hv2, hvout, hvroot, hroot, hfour'⟩, k, hk, hB⟩

/-- The source choice for an order-two intersection: a rootless diagonal
involution belongs to a Klein four whose selected second generator has an
order-four preimage and normalizes an outside conjugate factor containing t.
The normalizer geometry is derived from the stated local control. -/
theorem MinimalCounterexample.diagonalChoice_of_intersection_card_two
    (m : MinimalCounterexample S A₁ A₂) (l : LocalControl S A₁ A₂)
    {a g : G} (ha : a ∈ (A₁ : Set G) ∪ A₂) (ha2 : orderOf a = 2)
    (hg : g ∉ intersectionGenerated A₁ A₂) (ht : g⁻¹ * a * g ∈ S)
    (hcap : Nat.card (A₁ ⊓ A₂ : Subgroup G) = 2) :
    DiagonalChoice A₁ A₂ (g⁻¹ * a * g) := by
  exact m.diagonalChoice_of_normalizer_geometry l ha ha2 hg ht hcap
    (m.diagonalNormalizerGeometry_of_intersection_card_two l ha ha2 hg ht hcap)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry.StrongClosure.Asc75
end
