module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition.SourceModels
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition.Action

/-!
# Recognition with only the actual irreducible G.9.3 application outstanding

The normal reduction selects the literal minimal normal K* in H*. The local
G.9.3 exclusion concerns only this K* if it acts irreducibly. The surviving two-summand branch invokes the proved G.6.4 only
on its actual constituent images. Coordinates then recognize the entire
actor and its two-residual. The source power form recognizes the plus-type
extraspecial group of order128.

The explicit G.9.3 premise excludes only this actual irreducible action
with its earlier-source data; no complete model list is requested. Its producer remains
with the original-source assembly owner.
Source: Aschbacher–Smith 15.3.57–58, printed pp.1148–1149.
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open NormalReduction SplitBranch
universe u
variable {G : Type u} [Group G] [Finite G] {Z ZS V M : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)] [IsElementaryAbelian 2 V]
  {v : ActorQuotient Z} {s : ℕ}

/-- The only G.9.3 consequence needed by the actual source consumer. -/
def LocalIrreducibleExclusion
    (d : EarlierSourceInputs Z ZS V M KnownSimple.IsKnownSimple v s)
    (_a : EarlierActionInputs d) : Prop :=
  ∀ K : Subgroup (ActorQuotient Z),
    MinimalNormalConclusion KnownSimple.IsKnownSimple d.kernel K v s →
    Representation.IsIrreducible ((actorRepresentation Z ZS d.kernel).comp K.subtype) → False

/-- Both module identifications, with G.6.4 discharged by its proved source. -/
theorem naturalPair_of_local_exclusion
    (d : EarlierSourceInputs Z ZS V M KnownSimple.IsKnownSimple v s)
    (a : EarlierActionInputs d) (hG93 : LocalIrreducibleExclusion d a) :
    Nonempty (NaturalPair d a) := by
  have r := normal_reduction_of_earlier_source d
  obtain ⟨K, hK⟩ := r.normal_actor
  let := hK.minimal.1
  have hsplit : TwoSummandAlternative (actorRepresentation Z ZS d.kernel) K v s := by
    rcases hK.constituents.2 with hi | hs
    · exact False.elim (hG93 K hK hi)
    · exact hs
  let p := SplitPair.ofAlternative hsplit
  obtain ⟨S, hS, hna, _, n, _, ⟨e⟩⟩ := hK.simple_power
  let := hS
  obtain ⟨⟨m₁⟩, ⟨m₂⟩⟩ := natural_models hna K e
    (actorRepresentation Z ZS d.kernel) (actorRepresentation_injective Z ZS d.kernel)
    v s r.positive p a.quadratic a.invariant a.nondegenerate
    d.actorSylow a.sieveData.marked_central r.plane_three
    (QuotientGroup.mk' (pCore 2 (centralizerH Z)))
    (QuotientGroup.mk'_surjective _) d.sqtk
  obtain ⟨hs, hsing₁, hsing₂, hne, hdual⟩ := geometry_of_natural_models
    Z ZS d.kernel K v s p a.quadratic a.invariant a.nondegenerate m₁ m₂
  exact ⟨⟨K, hK, p, m₁, m₂, hs, hsing₁, hsing₂, hne, hdual⟩⟩

/-- The complete actor identification and plus-type conclusion on the actual
source carriers. The specified ambient t-coset is handled separately. -/
theorem actor_and_plus_type
    (d : EarlierSourceInputs Z ZS V M KnownSimple.IsKnownSimple v s)
    (a : EarlierActionInputs d) (b : EarlierPowerInputs d a)
    (hG93 : LocalIrreducibleExclusion d a) :
    ∃ p : NaturalPair d a, Nonempty (ActorRecognition p) ∧
      s = 1 ∧ Nat.card (closureU Z ZS) = 128 ∧
      Nonempty (closureU Z ZS ≃* DihedralCentralProductThree.Model) := by
  obtain ⟨p⟩ := naturalPair_of_local_exclusion d a hG93
  exact ⟨p, ⟨p.actorRecognition⟩, p.s_eq_one, p.card_U, p.plusType b⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition
