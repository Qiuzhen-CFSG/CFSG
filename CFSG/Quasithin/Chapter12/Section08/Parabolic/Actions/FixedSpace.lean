module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.Actions.Displacement

/-!
# The source quotient fixed space and the displacement clause

This is the literal form of the fixed-space assertion in 12.8.9(3),
with S = W X from (2), inside I₂/E. Pulling it back proves (4) for the
actual centralizer in H/V₁. Normality of E is relative to I₂ throughout.
The construction of (1–3), including the marked natural-module action,
belongs to the parabolic assembly; it is not asserted by this interface.

Source: Aschbacher–Smith, Lemma 12.8.9(2–4), printed p.853.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- Precisely the fixed-space equality in (3), using S = W X from (2).
U ≤ I₂ follows from the definition of the span. -/
def ParabolicFixedSpace (F : InvariantFlag T V n) (L : Subgroup G) (g : G)
    [((F.E g).subgroupOf (F.I₂ L)).Normal] : Prop :=
  ∀ u : F.U, (u : G) ∉ F.W →
    ((F.W ⊔ F.X g).subgroupOf (F.I₂ L)).map
        (QuotientGroup.mk' ((F.E g).subgroupOf (F.I₂ L))) ⊓
      centralizer ({QuotientGroup.mk' ((F.E g).subgroupOf (F.I₂ L))
        ⟨u, le_conjugateSpanBy F.U (F.P L) u.property⟩} :
          Set ((F.I₂ L) ⧸ (F.E g).subgroupOf (F.I₂ L))) =
    (F.W.subgroupOf (F.I₂ L)).map
      (QuotientGroup.mk' ((F.E g).subgroupOf (F.I₂ L)))

/-- Apply the actual quotient equality to ambient commutators. -/
theorem parabolicFixedSpace_commutator (F : InvariantFlag T V n)
    (L : Subgroup G) (g : G) (hgP : g ∈ F.P L)
    [((F.E g).subgroupOf (F.I₂ L)).Normal]
    (hfixed : F.ParabolicFixedSpace L g) :
    ∀ u ∈ F.U, u ∉ F.W → ∀ s ∈ F.W ⊔ F.X g,
      ⁅s, u⁆ ∈ F.E g → s ∈ F.W := by
  have hUI : F.U ≤ F.I₂ L := le_conjugateSpanBy _ _
  have hXI : F.X g ≤ F.I₂ L :=
    (map_mono (show F.W ≤ F.U from inf_le_left)).trans
      (le_sup_right.trans (F.U_sup_conjugate_le_I₂ L g hgP))
  intro u hu hnot s hs hc
  exact F.fixedSpace_lift L g hUI hXI ⟨u, hu⟩ (hfixed ⟨u, hu⟩ hnot) s hs hc

/-- Clause 12.8.9(4) as the literal centralizer bound in H/V₁, directly
from the actual quotient fixed-space equality in (3). -/
theorem parabolic_tilde_centralizer_le (F : InvariantFlag T V n) [IsMulCommutative V]
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G)) (hn : 2 ≤ n)
    (g : G) (hgP : g ∈ F.P L) [((F.E g).subgroupOf (F.I₂ L)).Normal]
    (hfixed : F.ParabolicFixedSpace L g) (y : F.X g) (hy : (y : G) ∉ F.W) :
    F.tilde F.U ⊓ centralizer ({F.tildeProjection
      ⟨y, F.X_le_H g (F.P_le_G₂ hn L hL hgP) y.property⟩} : Set F.G₁tilde) ≤
        F.tilde F.W := by
  rintro a ⟨ha, hc⟩
  apply F.tilde_displacement L hL hn g hgP
    (F.parabolicFixedSpace_commutator L g hgP hfixed) y hy ⟨a, ha⟩
  apply Subtype.ext
  change F.tildeProjection _ * a * (F.tildeProjection _)⁻¹ = a
  exact mul_inv_eq_iff_eq_mul.mpr (hc _ (Set.mem_singleton _))

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
