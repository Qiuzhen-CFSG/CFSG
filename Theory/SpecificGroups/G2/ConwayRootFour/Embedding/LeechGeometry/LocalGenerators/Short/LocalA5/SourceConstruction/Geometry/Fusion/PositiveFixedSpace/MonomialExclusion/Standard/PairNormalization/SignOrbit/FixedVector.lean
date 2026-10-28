module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.PairNormalization.Reduction

/-!
# A separating vector for the reference quaternion signs

The displayed integral Leech vector is fixed modulo twice the lattice by the
first reference generator. If the two literal quotient kernels agree, half its
displacement under the second generator belongs to the Leech lattice. The
negative-square condition restricts the second sign to a six-bit family; two
32-case kernel-checked congruence calculations leave only the reference sign
and its negative. `second_sign` includes the application to the actual signed
Golay elements and their quotient fixed spaces.

Only lattice congruences are computed, not the full 24-by-24 quotient matrices.
Completeness of the computable congruence test is proved from the existing
Golay decoder. The test vector has integral basis-coordinate bit mask 0x41922a
in `StandardCoordinates`; its lattice membership and fixedness are checked
independently of that diagnostic description.

Source context: Aschbacher, *Sporadic Groups* (1994), Lemma 49.5, pp.283–284,
and the root-four conventions on p.269. The Golay encoder and Leech lattice
are the existing attributed ATLAS models. These separating-vector calculations
are new and use no external computational oracle.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
open scoped BigOperators Matrix
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.PairNormalization.SignOrbit
open StandardCoordinates

private theorem golayCheck_complete (w : BinaryWord) (hw : w ∈ golay) : golayCheck w := by
  obtain ⟨⟨h,r,e⟩,rfl⟩ := hw
  unfold golayCheck
  rw [golay_decode_encode]
  refine ⟨(parityCode_mem 5 r.val).mp r.property, ?_⟩
  have hh : hexEncoder (hexDecoder h.val) = h.val := by
    obtain ⟨t,ht⟩ := h.property
    rw [← ht, hex_decode_encode]
  change jWord (hexEncoder (hexDecoder h.val)) + rho r.val + e • eta = _
  rw [hh]
  rfl

private theorem leechCheck_complete (x : IntegerCoordinates) (hx : x ∈ leech) : leechCheck x := by
  obtain ⟨m,_,hpar,hcode,hsum⟩ := (mem_leech x).mp hx
  have hm := hpar ((0,0),0)
  change (∀ i, x i % 2 = x ((0,0),0) % 2) ∧
    golayCheck (halfResidue x (x ((0,0),0) % 2)) ∧ (∑ i, x i) % 8 = 4 * (x ((0,0),0) % 2)
  rw [hm]
  exact ⟨hpar,golayCheck_complete _ hcode,hsum⟩

private def testCoordinates : IntegerCoordinates := fun i =>
  ![0,2,0,2,0,2,0,6,0,2,0,6,2,8,6,12,2,4,6,8,8,10,12,14] (flat i)
private theorem test_mem : testCoordinates ∈ leech := leechCheck_sound (by decide)
private def testVector : leech := ⟨testCoordinates,test_mem⟩
private def halfDisplacement (s : BinaryWord) (p : Omega → Omega) : IntegerCoordinates :=
  fun i => ((if s i = 0 then testCoordinates (p i) else -testCoordinates (p i)) -
    testCoordinates i) / 2
private theorem test_even (i : Omega) : testCoordinates i % 2 = 0 := by revert i; decide
private theorem halfDisplacement_double (s : BinaryWord) (p : Omega → Omega) (i : Omega) :
    2 * halfDisplacement s p i =
    (if s i = 0 then testCoordinates (p i) else -testCoordinates (p i)) - testCoordinates i := by
  have h₁ := test_even i
  have h₂ := test_even (p i)
  unfold halfDisplacement
  split_ifs <;> omega

private theorem reference_half_mem :
    halfDisplacement (jWord referenceHexB) referencePullA ∈ leech :=
  leechCheck_sound (by decide)

private theorem test_fixed (a : GolayMonomialGroup)
    (hp : ∀ i, monomialPull a i = referencePullA i)
    (hs : a.left.toAdd.val = jWord referenceHexB) :
    leechReduction testVector ∈ binaryFixed (monomialEmbedding a) := by
  change leechModTwoRepresentation (monomialEmbedding a) _ - _ = 0
  rw [leechModTwoRepresentation_reduce, LinearMap.id_apply, ← map_sub, leechReduction_eq_zero]
  refine ⟨⟨_,reference_half_mem⟩,?_⟩
  apply Subtype.ext
  funext i
  change 2 * halfDisplacement (jWord referenceHexB) referencePullA i =
    ((monomialEmbedding a).val testVector).val i - testVector.val i
  rw [monomialEmbedding_apply, hs, hp]
  exact halfDisplacement_double _ _ _

private theorem halfCheck_of_fixed (b : GolayMonomialGroup)
    (hp : ∀ i, monomialPull b i = referencePullB i)
    (hf : leechReduction testVector ∈ binaryFixed (monomialEmbedding b)) :
    leechCheck (halfDisplacement b.left.toAdd.val referencePullB) := by
  have hz : leechReduction ((monomialEmbedding b).val testVector - testVector) = 0 := by
    rw [map_sub, ← leechModTwoRepresentation_reduce]
    exact hf
  obtain ⟨y,hy⟩ := (leechReduction_eq_zero _).mp hz
  have he : halfDisplacement b.left.toAdd.val referencePullB = y.val := by
    funext i
    have hi := congrArg (fun v : leech => v.val i) hy
    change 2 * y.val i = ((monomialEmbedding b).val testVector).val i - testVector.val i at hi
    rw [monomialEmbedding_apply, hp] at hi
    change 2 * y.val i = (if b.left.toAdd.val i = 0 then testCoordinates (referencePullB i)
      else -testCoordinates (referencePullB i)) - testCoordinates i at hi
    unfold halfDisplacement
    omega
  rw [he]
  exact leechCheck_complete _ y.property

private def candidateB (u : Bit) (r : Fin 5 → Bit) : BinaryWord :=
  jWord (referenceHexA + referenceHexB + u • referenceHexB) + rho (parityEncoder 5 r)

private def baseSign (h : HexParameters) (e : Bit) : BinaryWord := jWord (hexEncoder h) + e • eta

set_option Elab.async false in
private theorem opposite_base : ∀ (h : HexParameters) (e : Bit),
    (∀ i, baseSign h e (referencePullB i) = baseSign h e i + 1) →
    ∃ u : Bit, baseSign h e = jWord (referenceHexA + referenceHexB + u • referenceHexB) := by
  intro h e
  rcases bit_cases e with he | he <;> subst e <;> revert h <;> decide +kernel

private theorem opposite_candidates (s : golay)
    (hs : ∀ i, s.val (referencePullB i) = s.val i + 1) :
    ∃ (u : Bit) (r : Fin 5 → Bit), s.val = candidateB u r := by
  obtain ⟨⟨⟨h,hh⟩,⟨r,hr⟩,e⟩,he⟩ := s.property
  obtain ⟨h,rfl⟩ := hh
  obtain ⟨r,rfl⟩ := hr
  have he' : s.val = baseSign h e + rho (parityEncoder 5 r) := by
    rw [← he]
    change (jWord _ + rho _) + e • eta = (jWord _ + e • eta) + rho _
    abel
  have hs' : ∀ i, baseSign h e (referencePullB i) = baseSign h e i + 1 := by
    intro i
    have hi := hs i
    rw [he'] at hi
    change baseSign h e (referencePullB i) + rho (parityEncoder 5 r) i =
      (baseSign h e i + rho (parityEncoder 5 r) i) + 1 at hi
    exact add_right_cancel (hi.trans (by abel))
  obtain ⟨u,hu⟩ := opposite_base h e hs'
  exact ⟨u,r,he'.trans (by rw [hu]; rfl)⟩

set_option Elab.async false in
private theorem check_zero : ∀ r : Fin 5 → Bit,
    leechCheck (halfDisplacement (candidateB 0 r) referencePullB) →
    ∀ i, candidateB 0 r i = jWord (referenceHexA + referenceHexB) i + candidateB 0 r ((0,0),0) := by
  decide
set_option Elab.async false in
private theorem check_one : ∀ r : Fin 5 → Bit,
    leechCheck (halfDisplacement (candidateB 1 r) referencePullB) →
    ∀ i, candidateB 1 r i = jWord (referenceHexA + referenceHexB) i + candidateB 1 r ((0,0),0) := by
  decide

/-- Once the first sign is fixed, equality on the literal quotient forces the
second reference sign up to central negation. -/
theorem second_sign (a b : GolayMonomialGroup)
    (hpa : ∀ i, monomialPull a i = referencePullA i)
    (hpb : ∀ i, monomialPull b i = referencePullB i)
    (hsa : a.left.toAdd.val = jWord referenceHexB)
    (hb : (monomialEmbedding b) ^ 2 = negationIsometry)
    (he : binaryFixed (monomialEmbedding a) = binaryFixed (monomialEmbedding b)) :
    ∀ i, b.left.toAdd.val i = jWord (referenceHexA + referenceHexB) i + b.left.toAdd.val ((0,0),0) := by
  have hf := test_fixed a hpa hsa
  rw [he] at hf
  have hc := halfCheck_of_fixed b hpb hf
  obtain ⟨u,r,hr⟩ := opposite_candidates b.left.toAdd (by
    intro i
    have hi := (monomial_square_negation_parameters b hb).2.1 i
    change b.left.toAdd.val (monomialPull b i) = _ at hi
    rwa [hpb] at hi)
  rw [hr] at hc ⊢
  rcases bit_cases u with hu | hu
  · subst u; exact check_zero r hc
  · subst u; exact check_one r hc
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.PairNormalization.SignOrbit
