module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Exceptional.LocalStructure
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Exceptional.FieldAction
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.Exceptional.MarkedQuotient
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.Complement.Exceptional

/-!
# Excluding the exceptional equality in the linear branch

This completes the equality branch of GLS IV, Chapter 2, Lemma 15.7 from
the original local context and the numerical conclusions of Lemma 15.6.
The literal homocyclic commutator and faithful field action are constructed,
so the exceptional action theorem gives q=8 and the marked quotient M/R₀
is SL₂(7). Its quarter-turn element produces a square root of the nonidentity
centralizer element. The original PSL₂(8) centralizer geometry forbids that
square root, giving the required contradiction.
-/

namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)

include d in
/-- The exceptional equality branch of GLS IV, Chapter 2, Lemma 15.7.
The two order assumptions are exactly the output of source Lemma 15.6. -/
public theorem Context.exceptionalCore_false
    (hJ : Nat.card (centralizer (residualGenerated M z t : Set G)) = 2)
    (hR : Nat.card (linearCentralizerClosure M z t) = 2 * (2 ^ n) ^ 2)
    (hRV : linearCentralizerClosure M z t = pCore 2 M) : False := by
  obtain ⟨s⟩ := d.exceptionalLocalStructure hJ hR
  obtain ⟨a⟩ := Context.exceptionalFieldAction s d hJ hR hRV
  obtain ⟨hn,u,R₀,hR₀,hu,hne,eQ,hmark,hfusion⟩ :=
    linear_marked_quotient_of_local_structure_and_action d.minimal.disconnected
      d.reduction d.parameter hR hRV s a
  subst n
  let := hR₀
  obtain ⟨x,hx⟩ := linear_exceptional_square_of_sl2Seven_quotient R₀ u eQ hmark hfusion
  exact linear_centralizer_nonsquare_of_centralizerClosure d.minimal.disconnected
    d.z_mem d.z_mem_M d.model hJ (fun _ hu hi => d.centralizer_closure hu hi)
    u hu hne x hx

end BenderSuzuki.ZD.LinearExclusion
