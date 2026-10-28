module

public import Theory.Representation.Mathieu.SmallModules.M11DegreeTwelve
public import Theory.Representation.Mathieu.SmallModules.M11DegreeTwelve.InducedHeads.Restriction

/-!
# The M11 induced-module degree gap from two twelve-coset actions

Let H contain the marked Sylow-eleven normalizer N, with both [M11 : H]
and [H : N] equal to twelve, and suppose the marked eleven-subgroup normally
generates H. The local fixed-space bound and the two permutation modules
exclude simple binary M11 modules of dimensions eleven and twelve.
Applying this to every actual maximal quotient of the published normalizer
induction proves `SmallInducedHeads` under precisely these group hypotheses.

The independent subgroup construction must supply H and the four hypotheses;
no character table, simple-module classification, or splitting of restrictions
is assumed here. The final theorem applies the existing marked recognition
consumer. Source: James, J. Algebra 27 (1973), 57--111; Aschbacher--Smith K.4,
printed p.457/PDF p.468.
-/

public noncomputable section
namespace Representation.MathieuSmall.M11DegreeTwelve
open Sporadic.Mathieu

/-- Two literal coset actions give the binary simple-degree gap. -/
theorem finrank_le_ten_of_index_twelve
    (H : Subgroup M11) (hNH : m11Sylow11Normalizer ≤ H)
    (hH : H.index = 12) (hN : (m11Sylow11Normalizer.subgroupOf H).index = 12)
    (hgen : Subgroup.normalClosure (↑(m11Sylow11Subgroup.subgroupOf H) : Set H) = ⊤)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) M11 V) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 12) : Module.finrank (ZMod 2) V ≤ 10 := by
  have hPH : m11Sylow11Subgroup ≤ H := Subgroup.le_normalizer.trans hNH
  have hcP : Nat.card (m11Sylow11Subgroup.subgroupOf H) = 11 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPH).toEquiv).trans m11Sylow11Subgroup_card
  have hcN : Nat.card (m11Sylow11Normalizer.subgroupOf H) = 55 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv).trans m11Sylow11_normalizer_card
  have hn : m11Sylow11Normalizer.subgroupOf H ≤
      Subgroup.normalizer (↑(m11Sylow11Subgroup.subgroupOf H) : Set H) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hPH]
  exact InducedHeads.finrank_le_ten_of_two_indices H hH
    (m11Sylow11Subgroup.subgroupOf H) (m11Sylow11Normalizer.subgroupOf H)
    hcP hcN hn hN hgen ρ hd

/-- The finite-module assertion for the literal published induction, with only
its independent group-theoretic overgroup hypotheses left explicit. -/
theorem smallInducedHeads_of_index_twelve
    (H : Subgroup M11) (hNH : m11Sylow11Normalizer ≤ H)
    (hH : H.index = 12) (hN : (m11Sylow11Normalizer.subgroupOf H).index = 12)
    (hgen : Subgroup.normalClosure (↑(m11Sylow11Subgroup.subgroupOf H) : Set H) = ⊤) :
    SmallInducedHeads := by
  intro S hS
  let : S.quotientRepresentation.IsIrreducible :=
    SimpleHeadQuotient.irreducible_quotient_of_isCoatom S hS
  by_cases hd : Module.finrank (ZMod 2) (InducedSpace ⧸ S.toSubmodule) ≤ 12
  · exact Or.inl (finrank_le_ten_of_index_twelve H hNH hH hN hgen S.quotientRepresentation hd)
  · exact Or.inr (Nat.lt_of_not_ge hd)

/-- The degree gap feeds the existing actual M11 recognition consumer,
retaining the full equivariant identification with its marked point module. -/
theorem equiv_point_of_index_twelve
    (H : Subgroup M11) (hNH : m11Sylow11Normalizer ≤ H)
    (hH : H.index = 12) (hN : (m11Sylow11Normalizer.subgroupOf H).index = 12)
    (hgen : Subgroup.normalClosure (↑(m11Sylow11Subgroup.subgroupOf H) : Set H) = ⊤)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) M11 V) (hf : Function.Injective ρ) [ρ.IsIrreducible]
    (hd : Module.finrank (ZMod 2) V ≤ 12) :
    Nonempty (ρ.Equiv M12Recognition.pointRepresentation) :=
  equiv_point_of_smallInducedHeads ρ (smallInducedHeads_of_index_twelve H hNH hH hN hgen) hf hd

end Representation.MathieuSmall.M11DegreeTwelve
