module

public import Theory.Representation.IrreducibleTraceIndependence
public import Theory.Representation.PRegularTrace

/-!
# Independence of simple traces on odd-order elements

Over an algebraically closed field of characteristic two, the ordinary
field-valued traces of a finite family of pairwise inequivalent irreducible
representations of a finite group are linearly independent after restriction
to its odd-order elements. The vector spaces may vary with the family index;
irreducibility and equivalence are the actual representation predicates.
These are residue-field traces, not characteristic-zero Brauer characters.
This theorem supplies the modular independence input for lifting genuine
Brauer characters by an evaluation determinant.

The imported arbitrary-characteristic trace-independence theorem uses
simultaneous Jacobson density on the associated simple group-algebra modules,
with Schur's lemma identifying the diagonal endomorphisms. The imported
p-regular trace reduction gives one odd-order element with the same trace
as any chosen group element in every representation: suitable commuting
powers have nilpotent difference, whose trace vanishes. Consequently a
relation on odd-order elements extends to the whole group and all its
coefficients vanish. Neither Maschke's theorem nor ordinary-character
orthogonality is used, and the group order need not be invertible.

The mathematical foundations and their proofs are in
`Theory.Representation.IrreducibleTraceIndependence` and
`Theory.Representation.PRegularTrace`; this module specializes and combines
them at the characteristic-two modular-character boundary.
-/

namespace ModularBlock

/-- Actual simple representations have independent characteristic-two traces
on odd-order elements, without an invertibility assumption on the group order. -/
public theorem linearIndependent_twoRegular_simple_traces
    {k G ι : Type*} [Field k] [IsAlgClosed k] [CharP k 2]
    [Group G] [Finite G] [Finite ι]
    (V : ι → Type*) [∀ index, AddCommGroup (V index)] [∀ index, Module k (V index)]
    [∀ index, FiniteDimensional k (V index)]
    (representations : ∀ index, Representation k G (V index))
    [∀ index, Representation.IsIrreducible (representations index)]
    (hne : Pairwise fun first second =>
      IsEmpty (Representation.Equiv (representations first) (representations second))) :
    LinearIndependent k (fun index (regular : {element : G // Odd (orderOf element)}) =>
      (representations index).character regular) := by
  classical
  let := Fintype.ofFinite ι
  have hind := Representation.linearIndependent_characters_of_pairwise_inequivalent
    V representations hne
  have htrace (element : G) :
      ∃ regular : {element : G // Odd (orderOf element)},
        ∀ index, (representations index).character element =
          (representations index).character regular := by
    obtain ⟨regular, hregular, heq⟩ :=
      Representation.exists_pRegular_same_character (F := k) 2 element
    refine ⟨⟨regular, ?_⟩, fun index => heq (V index) (representations index)⟩
    exact Nat.not_even_iff_odd.mp (fun heven => hregular (even_iff_two_dvd.mp heven))
  rw [Fintype.linearIndependent_iff]
  intro coefficients hsum
  apply (Fintype.linearIndependent_iff.mp hind) coefficients
  funext element
  obtain ⟨regular, heq⟩ := htrace element
  have hvalue := congrFun hsum regular
  simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, heq] using hvalue

end ModularBlock
