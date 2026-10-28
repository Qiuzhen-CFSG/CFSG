module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Restrictions
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.Models

/-!
# Block deductions for escaping centralizers

The local Sylow, SQTK and characteristic-normalizer inputs to C.1.29 are
proved in `Blocks.Setup`. The corank deductions there apply to an actual
subgroup outside M. `Blocks.Models` specifies the concrete quotient Borels
and the intrinsic even-field torus calculation needed for E.6.11.

The theorem below proves the faithful-action exclusion of E.6.10(3) once
an actual A₃ or A₅ block has been constructed in C_G(U). It transports the
factor of three from that block's actual alternating quotient, then uses
the three-rank bound in N_G(W) for every W ≤ U, including W = 1.

This module does not yet assert E.6.7 or E.6.10: the central product of
blocks, the intrinsic module calculations, and the normal module needed
for the omega-center conclusion still have to be constructed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7 and
E.6.10, printed pp.246 and 248–249 (PDF pp.257 and 259–260).
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06
open Subgroup
variable {G : Type*} [Group G] [Finite G]
variable {𝒦 : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- A constructed alternating block discharges the divisibility premise in
the faithful-action exclusion. No action on W is replaced by an abstract tag. -/
theorem HypothesisE61.no_faithful_nine_of_alternating_block
    (h : HypothesisE61 𝒦 T M V) (hUV : U ≤ V)
    (hLH : L ≤ centralizer (U : Set G))
    {n : ℕ} (hL : ChapterC.IsAlternatingBlock L n) (hn : n = 3 ∨ n = 5)
    (W : Subgroup G) (hWU : W ≤ U)
    (A : Subgroup G) [IsElementaryAbelian 3 A] (hA : Nat.card A = 9)
    (hAN : A ≤ normalizer (W : Set G)) :
    ¬ Function.Injective (W.normalizerMonoidHom.comp (inclusion hAN)) :=
  h.no_faithful_nine_of_three_dvd hUV
    ((three_dvd_card_alternating_block L hL hn).trans (card_dvd_of_le hLH)) W hWU A hA hAN

/-- A normal block module with no fixed points under L is disjoint from U,
since L centralizes U. This discharges the disjointness input to the
central-involution argument once the block orbit module is constructed. -/
theorem omega_center_not_le_of_block_module {D : Subgroup G}
    (hLH : L ≤ centralizer (U : Set G))
    (hDS : D ≤ (T : Subgroup G) ⊓ normalizer (U : Set G))
    (hDn : (D.subgroupOf ((T : Subgroup G) ⊓ normalizer (U : Set G))).Normal)
    (hDne : D ≠ ⊥) (hfix : D ⊓ centralizer (L : Set G) = ⊥) :
    ¬ Stellmacher.omegaOneCenterAmbient ((T : Subgroup G) ⊓ normalizer (U : Set G)) ≤ U := by
  have hd : Disjoint D U := by
    apply disjoint_iff.mpr
    apply eq_bot_iff.mpr
    intro x hx
    exact hfix ▸ (show x ∈ D ⊓ centralizer (L : Set G) from
      ⟨hx.1, le_centralizer_iff.mpr hLH hx.2⟩)
  exact omega_center_not_le_of_normal_disjoint (T : Subgroup G) U D T.isPGroup'
    hDS hDn hDne hd

end CFSG.Quasithin.ChapterE.Section06
