module
public import CFSG.Quasithin.Chapter12.Section06.Terminal.CriticalGeometry
public import CFSG.Quasithin.Chapter12.Section06.Nonabelian.Consequences
public import CFSG.Quasithin.Chapter12.Section06.LocalAlternatives.MarkedQuotient

/-!
# The terminal contradiction on the original Section12.6 setup

Take H to be the full point centralizer. The existing abelian equivalence
supplies V ≤ O₂(H), and the source fusion hypotheses supply commutativity
of intersecting conjugates. The four-group marking computes the original
edge-core image order. The critical geometry constructs every remaining
terminal witness and applies the faithful action on the original U_H/V₁.

The actual F.9 application, abelian point span, fusion and local product
markings remain explicit preceding-source premises; no natural-reduction
output or terminal configuration is assumed.

Source: Aschbacher–Smith, 12.6.24–27 and 12.6.31–34,
printed pp.830–838.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup
open Terminal
variable {G : Type*} [Group G] [Finite G] (D : Setup G)

/-- The terminal source application uses the full point centralizer and
retains the literal F.9 setup and the marked local two-core. -/
theorem original_terminal_contradiction
    (h : (D.f9 D.Gz).Hypothesis)
    (hC : centralizer (D.V₅ : Set G) = centralizer (D.V : Set G))
    (hspan : IsMulCommutative (D.VH D.Gz))
    (hfusion : ∀ a : G, MulAut.conj a D.z.val ∈ D.V →
      ∃ n ∈ normalizer (D.V : Set G),
        MulAut.conj n D.z.val = MulAut.conj a D.z.val)
    (horbit : ∀ g : G, g ∉ normalizer (D.V : Set G) →
      ∀ x ∈ D.V ⊓ D.V.map (MulAut.conj g).toMonoidHom, x ≠ 1 →
        ∃ n ∈ normalizer (D.V : Set G), MulAut.conj n x = D.z.val)
    (hlocal : LocalAlternatives.SymmetricProductConclusion D.M D.Gz D.R₁)
    (e : (D.Gz ⧸ pCore 2 D.Gz) ≃* Product)
    (hplace : cubicFactor ≤ ((D.L₁ ⊔ (D.T : Subgroup G)).subgroupOf D.Gz).map
      (productMap (D := D.f9 D.Gz) e))
    (hRK : (D.R₁.subgroupOf D.Gz).map (productMap (D := D.f9 D.Gz) e) ≤
      quinticComponent) : False := by
  have heq := D.lemma_12_6_25 h hC
  have hV : (D.f9 D.Gz).V ≤ (D.f9 D.Gz).QH := heq.1.mp (heq.2.2.mpr hspan)
  apply marked_edge_contradiction h hV rfl hC
    (D.lemma_12_6_27_of_abelian hspan hfusion horbit) e hplace _ hRK
  obtain ⟨f⟩ := hlocal.image_four
  have hfour : Nat.card (star D.Gz D.R₁) = 4 :=
    (Nat.card_congr f.toEquiv).trans (by
      change Nat.card (Fin 2 → ZMod 2) = 4
      norm_num [Nat.card_fun,Nat.card_fin,Nat.card_zmod])
  change Nat.card ((D.R₁.subgroupOf D.Gz).map
    (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D.Gz)))) ≤ 4
  rw [←map_map,card_map_of_injective e.injective]
  exact hfour.le
end CFSG.Quasithin.Chapter12.Section06.Nonabelian.Setup
