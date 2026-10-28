module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Contracts
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.Endpoint
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.ParabolicReduction

/-!
# Assembly of the inner SL₅ source branches

The end-node support sieve and the endpoint-pair estimate together exclude
all eleven multiple supports. The proved end-node sieve reduces an offending
support to `{0,3}`; the adjoint common-centralizer estimate excludes that pair.
The theorem `inner_estimate` discharges both branches for every faithful
finite-dimensional irreducible binary SL₅ representation, without a degree
cutoff, absolute irreducibility or an assumed module catalogue.

The parabolic consumer applies the fixed-space reduction to a literal subgroup
P of SL₅ and N normal in P. It retains the original actor B, its subgroup in P,
and the quotient map P → P/N. Thus its two alternatives can be used by the
end-node producer without assuming global normality of a parabolic radical.

Source: Guralnick–Malle, *Classification of 2F-modules, II*, author manuscript,
Lemma 4.5 and Proposition 4.7; Aschbacher–Smith K.3.2, printed pp.454–455.
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner

open Representation Representation.BinaryOffender

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) SL5TenDimensional.Group V)

/-- Conditional assembly of the two genuine source branches. The caller still
has to prove both estimates from faithful irreducibility. -/
theorem inner_estimate_of_end_node_and_endpoint
    (hsieve : EndNodeSieve σ) (hendpoint : EndpointEstimate σ) : InnerEstimate σ := by
  intro J v hv hhighest hJ B hB hc hr
  by_contra hnot
  have hsmall := Nat.le_of_not_gt hnot
  obtain ⟨hzero, hthree⟩ := hsieve J v hv hhighest hJ B hB hc hr hsmall
  have hJend := endpoint_of_end_node_bounds J hJ hzero hthree
  subst J
  exact (not_lt_of_ge hsmall) (hendpoint v hv hhighest B hB hc hr)

/-- Every multiple-root highest support of a faithful irreducible binary SL₅
module has common fixed codimension strictly greater than twice the rank of
each nontrivial elementary cubic subgroup of the actual SL₅ group of rank at
most six. The end-node and endpoint estimates are both discharged. -/
theorem inner_estimate [FiniteDimensional (ZMod 2) V]
    (hfaithful : Function.Injective σ) (hirreducible : Representation.IsIrreducible σ) :
    InnerEstimate σ :=
  inner_estimate_of_end_node_and_endpoint σ
    (EndNode.end_node_sieve σ hfaithful hirreducible)
    (Endpoint.endpoint_estimate σ hfaithful hirreducible)

/-- The parabolic alternative for the actual SL₅ actor. All normality and
quotient operations are relative to P, and both resulting actors remain cubic. -/
theorem parabolic_offender_alternative [FiniteDimensional (ZMod 2) V]
    (P : Subgroup SL5TenDimensional.Group) (N : Subgroup P) [N.Normal]
    (B : Subgroup SL5TenDimensional.Group) (hBP : B ≤ P)
    (hB : IsElementaryTwo B) (hc : IsCubic σ B)
    (hsmall : fixedCodim σ B ≤ 2 * rank B) :
    (∃ C : Subgroup P, C ≤ B.subgroupOf P ∧ C ≤ N ∧ IsElementaryTwo C ∧
      IsCubic (σ.comp P.subtype) C ∧
      fixedCodim (σ.comp P.subtype) C ≤ 2 * rank C) ∨
    (IsElementaryTwo ((B.subgroupOf P).map (QuotientGroup.mk' N)) ∧
      IsCubic (Representation.quotientToInvariants (σ.comp P.subtype) N)
        ((B.subgroupOf P).map (QuotientGroup.mk' N)) ∧
      fixedCodim (Representation.quotientToInvariants (σ.comp P.subtype) N)
          ((B.subgroupOf P).map (QuotientGroup.mk' N)) ≤
        2 * rank ((B.subgroupOf P).map (QuotientGroup.mk' N))) := by
  have hmap : (B.subgroupOf P).map P.subtype = B :=
    Subgroup.map_subgroupOf_eq_of_le hBP
  let : IsElementaryAbelian 2 B := hB.2
  have hA : IsElementaryTwo (B.subgroupOf P) := by
    refine ⟨?_, IsElementaryAbelian.subgroupOf hBP⟩
    intro hbot
    exact hB.1 (by rw [← hmap, hbot, Subgroup.map_bot])
  have hrank : rank (B.subgroupOf P) = rank B := by
    rw [← rank_map_injective P.subtype P.subtype_injective, hmap]
  have hcodim : fixedCodim (σ.comp P.subtype) (B.subgroupOf P) = fixedCodim σ B := by
    unfold fixedCodim
    rw [fixedSpace_comp_map, hmap]
  apply normal_offender_alternative (σ.comp P.subtype) N hA
  · intro a ha b hb c hcc v
    exact hc a ha b hb c hcc v
  · simpa only [hcodim, hrank] using hsmall

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner
