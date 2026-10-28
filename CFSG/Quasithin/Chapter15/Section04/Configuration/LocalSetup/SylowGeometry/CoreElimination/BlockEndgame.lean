module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.SourceData
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.ModelTransport
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.PairQuotient

/-!
# Assembly reductions for the exchanged rank-one block endgame

The concrete Borel and natural-module calculations are in `Models`; the
original source geometry and the surviving block are in `SourceData`.
Transport through the specified conjugation constructs the second block's
model over the same field in `ModelTransport`.
`PairQuotient` allows a common central kernel when placing the four-group in
the pair of module layers; an external direct-product identification or a
splitting of the four-group is unnecessary for that numerical bound.

The fixed seed C_Z(X) already centralizes U, since Z = Ω₁(Z(T)) and U ≤ T.
If it centralizes the first block, then it centralizes the conjugate block
exchanged by an element of U, and therefore all of H = KU. The seed lies
in H: Z lies in the Baumann subgroup, which is contained in U. This gives
centrality in the intrinsic center Z(H), with its embedding retained.
Two-local uniqueness then puts H in M₁, contradicting the outside Y-factor.

These are assembly reductions, not the completed source contradiction.
The two remaining obligations are to construct the source Borel/module
placement and deduce n = 2, and then to prove that the fixed seed centralizes
the first L₂(4)-block. No Borel placement or centrality is added to the
source input records. Final assembly remains in this module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the final
characteristic-two paragraph of the proof of 15.4.20, printed p.1164.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame
open Subgroup Stellmacher
variable {G : Type*} [Group G]

/-- Centralizing the first factor and the exchanging subgroup centralizes their join. -/
theorem centralizes_exchanged_join {A H K L U : Subgroup G} {r : G}
    (hH : K ⊔ U = H) (hK : L ⊔ L.map (MulAut.conj r).toMonoidHom = K)
    (hr : r ∈ U) (hAU : A ≤ centralizer (U : Set G))
    (hAL : A ≤ centralizer (L : Set G)) : H ≤ centralizer (A : Set G) := by
  have hUC : U ≤ centralizer (A : Set G) := le_centralizer_iff.mp hAU
  have hLC : L ≤ centralizer (A : Set G) := le_centralizer_iff.mp hAL
  have hconj : L.map (MulAut.conj r).toMonoidHom ≤ centralizer (A : Set G) := by
    rintro _ ⟨l, hl, rfl⟩
    apply mem_centralizer_iff.mpr
    intro a ha
    have har : Commute a r := mem_centralizer_iff.mp (hUC hr) a ha
    have hal : Commute a l := mem_centralizer_iff.mp (hLC hl) a ha
    exact ((har.mul_right hal).mul_right har.inv_right).eq
  rw [← hH, ← hK]
  exact sup_le (sup_le hLC hconj) hUC

variable [Finite G] {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}
namespace ContraryData
variable (c : ContraryData κ d i j)
include c

/-- Only centrality on the first block remains; conjugation gives the second block. -/
theorem fixed_seed_centralizes_H (b : ExchangedBlock c)
    (hfirst : d.Z ⊓ centralizer (d.wholeX : Set G) ≤ centralizer (b.first : Set G)) :
    c.H ≤ centralizer ((d.Z ⊓ centralizer (d.wholeX : Set G) : Subgroup G) : Set G) :=
  centralizes_exchanged_join c.product b.product b.exchanger_mem
    c.fixed_seed_centralizes_U hfirst

/-- Intrinsic form of the centrality deduction, with the embedding into H explicit. -/
theorem fixed_seed_le_center_H (b : ExchangedBlock c)
    (hfirst : d.Z ⊓ centralizer (d.wholeX : Set G) ≤ centralizer (b.first : Set G)) :
    d.Z ⊓ centralizer (d.wholeX : Set G) ≤ (center c.H).map c.H.subtype := by
  have hUH : c.U ≤ c.H := c.sylow_image ▸ map_subtype_le (c.sylow : Subgroup c.H)
  intro z hz
  refine ⟨⟨z, hUH (c.Z_le_U hz.1)⟩, mem_center_iff.mpr ?_, rfl⟩
  intro h
  apply Subtype.ext
  exact (mem_centralizer_iff.mp (c.fixed_seed_centralizes_H b hfirst h.property) z hz).symm

/-- The final outside-factor contradiction, conditional on the first-block centrality lemma. -/
theorem false_of_fixed_seed_centralizes_first (b : ExchangedBlock c)
    (hfirst : d.Z ⊓ centralizer (d.wholeX : Set G) ≤ centralizer (b.first : Set G)) : False := by
  have hHM := (c.fixed_seed_centralizes_H b hfirst).trans c.fixed_seed_centralizer
  exact c.outside_Y ((d.Y_le_I i j).trans (c.amalgam_le.trans hHM))

end ContraryData
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame
