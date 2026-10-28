module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.FiveNormalizerConsequences
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.FiveNormalizerConstruction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.InvolutionAction
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer.LocalPairs

/-!
# Assembly of the small-centralizer contradiction

The source pair count three and Thompson's formula give order 51840. The
Sylow-five normalizer calculation then supplies its intrinsic three-core
of order 27 and an involution from N_H(P). The involution action forces a
centralizer divisible by nine, contradicting both available involution classes.

The §46 frame constructs an embedded subgroup X₁A₁ of order 48. Under the
order-48 centralizer assumption it is the full centralizer, and its source
pairs are indexed by the three nonidentity elements of E. Conjugacy transports
this count to every representative of the second involution class.

The final theorem `not_card_eq_48` discharges the pair count and the literal
Sylow-five normalizer construction from the seed and local census. The earlier
conditional assemblies remain available with their original interfaces.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 47.1, pp.259–260.
-/

public section

open Subgroup

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer

variable {G : Type*} [Group G] [Finite G]

/-- Apply the action contradiction to the literal embedded three-core and
involution of the Sylow-five normalizer. Normality is only inside N_G(P). -/
theorem FiveNormalizerData.false_of_small {D : Seed G} (N : FiveNormalizerData D)
    {t : G} (ht : OtherInvolution D t)
    (hC : Nat.card (involutionCentralizer t) = 48) : False := by
  let s : G := ((N.s : involutionCentralizer D.z) : G)
  have hsN : s ∈ fiveNormalizer D N.P :=
    (N.P : Subgroup (involutionCentralizer D.z)).le_normalizer_map
      (involutionCentralizer D.z).subtype (mem_map_of_mem _ N.s.property)
  have hn : s ∈ normalizer (normalizerThreeCore D N.P : Set G) := by
    apply (pCore 3 (fiveNormalizer D N.P)).le_normalizer_map (fiveNormalizer D N.P).subtype
    exact mem_map.mpr ⟨⟨s, hsN⟩, by rw [normalizer_eq_top]; trivial, rfl⟩
  have hs : orderOf s = 2 := by
    change orderOf ((N.s : involutionCentralizer D.z) : G) = 2
    rw [orderOf_coe, orderOf_coe, N.s_order]
  exact not_inverted_27 ht hC (normalizerThreeCore D N.P) N.core_card s hs
    (mem_centralizer_singleton_iff.mp (N.s : involutionCentralizer D.z).property)
    N.s_ne_z hn N.z_inverts_core

/-- Conditional source assembly. Its two remaining mathematical premises are
the small-case local pair count and the Sylow-five normalizer construction. -/
theorem not_card_eq_48_of_local_calculations {D : Seed G} (L : LocalCensus D)
    {t : G} (ht : OtherInvolution D t)
    (hcount : Nat.card (involutionCentralizer t) = 48 → sourceCount D.z t t = 3)
    (hnormalizer : Nat.card G = 51840 → Nonempty (FiveNormalizerData D)) :
    Nat.card (involutionCentralizer t) ≠ 48 := by
  intro hC
  obtain ⟨N⟩ := hnormalizer (card_eq_of_small_centralizer L ht hC (hcount hC))
  exact N.false_of_small ht hC

/-- Apply a local pair calculation at the source's chosen representative.
The actual subgroup inclusion and order justify the converse reduction from
order 48; ambient conjugation then transports the pair count to `t`. -/
theorem not_card_eq_48_of_local_subgroup {D : Seed G} (L : LocalCensus D)
    {t u : G} (ht : OtherInvolution D t) (hu : OtherInvolution D u)
    (B : Subgroup G) (hB : B ≤ involutionCentralizer u) (hcard : Nat.card B = 48)
    (hcount : involutionCentralizer u = B → sourceCount D.z u u = 3)
    (hnormalizer : Nat.card G = 51840 → Nonempty (FiveNormalizerData D)) :
    Nat.card (involutionCentralizer t) ≠ 48 := by
  apply not_card_eq_48_of_local_calculations L ht ?_ hnormalizer
  intro hC
  rw [sourceCount_at_other_eq ht hu]
  exact hcount (centralizer_eq_of_le_and_card48 ht hu hC B hB hcard)

/-- The second involution centralizer cannot have order 48. The constructed
§46 frame supplies the pair count three, Thompson's formula gives order
51840, and the actual Sylow-five normalizer supplies the order-27 core whose
involution action contradicts both possible centralizer orders. -/
theorem not_card_eq_48 {D : Seed G} (L : LocalCensus D)
    {t : G} (ht : OtherInvolution D t) :
    Nat.card (involutionCentralizer t) ≠ 48 :=
  not_card_eq_48_of_local_calculations L ht
    (LocalPairs.count_eq_three_of_card48 L ht) (exists_fiveNormalizerData D L)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Recognition.SmallCentralizer
