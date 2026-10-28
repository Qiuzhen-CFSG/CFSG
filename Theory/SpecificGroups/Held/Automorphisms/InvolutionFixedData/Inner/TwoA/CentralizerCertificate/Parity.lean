module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.CentralizerCertificate.Words
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Noninner
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.OrbitalPreservation

/-!
# Halving the graph centralizer bound by permutation parity

The literal Held centralizer embeds in the centralizer of atlasA in the full
relation-preserving permutation group. All elements of Held have positive
sign, by the proved perfectness of its concrete carrier. The certified outer
involution has negative sign and centralizes atlasA. Multiplication by this
odd element gives a second disjoint copy of the literal centralizer.

Thus a graph-centralizer bound of 322560 gives a bound of 161280 for the
literal fixed subgroup. Together with the independently certified lower
bound for the four generated words, this will give both exhaustion and order.
The graph and generated-subgroup bounds remain explicit premises here.

Source: GLS3 Table 5.3p, printed p.277; the ATLAS HeG1-a2W1 implementer and
its parity are certified in `OuterInvolution/Noninner.lean`.
-/

@[expose] public section
namespace Held.InvolutionFixedData.TwoA.CentralizerCertificate
open Subgroup Held.NormalizerGraph
set_option maxRecDepth 4096

/-- All relation-preserving permutations commuting with the literal atlasA. -/
def graphCentralizer : Subgroup (Equiv.Perm (Fin 2058)) :=
  preservingGroup ⊓ Subgroup.centralizer ({atlasA} : Set (Equiv.Perm (Fin 2058)))

/-- The original permutation representation restricted to the literal centralizer. -/
def graphEmbedding : centralizer →* graphCentralizer where
  toFun g := ⟨representation g.val, by
    refine ⟨Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup
      g.val.property, ?_⟩
    change representation g.val ∈ Subgroup.centralizer ({atlasA} : Set (Equiv.Perm (Fin 2058)))
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hg : g.val ∈ Subgroup.centralizer ({a} : Set He) :=
      (le_of_eq centralizer_eq) g.property
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    exact congrArg representation hg⟩
  map_one' := Subtype.ext (map_one representation)
  map_mul' x y := Subtype.ext (map_mul representation x.val y.val)

theorem graphEmbedding_injective : Function.Injective graphEmbedding := by
  intro x y h
  apply Subtype.ext
  apply representation_injective
  exact congrArg (fun z : graphCentralizer => z.val) h

theorem graphEmbedding_sign (g : centralizer) :
    Equiv.Perm.sign (graphEmbedding g).val = 1 := by
  exact hom_to_commGroup_trivial (Equiv.Perm.sign.comp representation) g.val

private theorem outer_mem_graphCentralizer :
    (OuterInvolution.representative : Equiv.Perm (Fin 2058)) ∈ graphCentralizer := by
  refine ⟨Orbital.normalizer_le_of_invariant
    Realization.MarkedConjugacy.Seventeen.permutationGroup_le_preservingGroup
    OuterInvolution.representative.property, ?_⟩
  change (OuterInvolution.representative : Equiv.Perm (Fin 2058)) ∈
    Subgroup.centralizer ({atlasA} : Set (Equiv.Perm (Fin 2058)))
  rw [Subgroup.mem_centralizer_singleton_iff]
  have ht : Commute OuterInvolution.implementer atlasA := by
    exact (mul_inv_eq_iff_eq_mul.mp OuterInvolution.conj_a :
      OuterInvolution.implementer * atlasA = atlasA * OuterInvolution.implementer)
  exact (ht.pow_left 5).eq

private def oddElement : graphCentralizer :=
  ⟨OuterInvolution.representative, outer_mem_graphCentralizer⟩

private theorem oddElement_sign : Equiv.Perm.sign oddElement.val = -1 :=
  OuterInvolution.representative_sign

private def doubled (p : Bool × centralizer) : graphCentralizer :=
  (if p.1 then oddElement else 1) * graphEmbedding p.2

private theorem doubled_injective : Function.Injective doubled := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  have hs := congrArg (fun g : graphCentralizer => Equiv.Perm.sign g.val) h
  have hij : i = j := by
    cases i <;> cases j
    · rfl
    · simp [doubled, map_mul, graphEmbedding_sign, oddElement_sign] at hs
    · simp [doubled, map_mul, graphEmbedding_sign, oddElement_sign] at hs
    · rfl
  subst j
  have hxy : x = y := graphEmbedding_injective (mul_left_cancel h)
  subst y
  rfl

/-- The odd coset and the even Held centralizer are disjoint. -/
theorem twice_centralizer_card_le_graph :
    2 * Nat.card centralizer ≤ Nat.card graphCentralizer := by
  have h := Nat.card_le_card_of_injective doubled doubled_injective
  simpa only [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] using h

theorem centralizer_card_le_of_graph_bound
    (h : Nat.card graphCentralizer ≤ 322560) : Nat.card centralizer ≤ 161280 := by
  have hh := twice_centralizer_card_le_graph
  omega

/-- Assembly of generation and cardinality from the two independent finite bounds. -/
theorem centralizer_certificate_of_bounds
    (hl : 161280 ≤ Nat.card generated)
    (hu : Nat.card graphCentralizer ≤ 322560) :
    generated = centralizer ∧ Nat.card centralizer = 161280 :=
  ⟨generated_eq_centralizer_of_bounds hl (centralizer_card_le_of_graph_bound hu),
    centralizer_card_of_bounds hl (centralizer_card_le_of_graph_bound hu)⟩

end Held.InvolutionFixedData.TwoA.CentralizerCertificate
