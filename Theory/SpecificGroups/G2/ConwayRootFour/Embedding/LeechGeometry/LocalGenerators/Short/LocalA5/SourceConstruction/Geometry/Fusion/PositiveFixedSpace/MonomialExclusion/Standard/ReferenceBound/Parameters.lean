module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Fusion.PositiveFixedSpace.MonomialExclusion.Standard.Reference

/-!
# Literal parameters of the reference centralizer

The marked translations have the six standard tetrads as their orbits.
Injectivity of the signed-coordinate embedding turns the square and commutation
relations into explicit equations for the inverse permutation and the Golay sign.
The coordinate permutation consequently belongs to the actual sextet stabilizer,
so its existing affine hexacode parametrization applies.

These are reductions for the reference calculation used in Aschbacher,
*Sporadic Groups* (1994), Lemma 49.5, pp.283–284, with the convention on p.269.
They make no assertion that the candidate enumeration is exhaustive.
-/

open Atlas.Conway Atlas.Codes Atlas.Lattices
@[expose] public noncomputable section
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound

theorem referencePair_parts (a b : GolayMonomialGroup) (hp : ReferenceQuaternionPair a b) :
    quaternionParts a b = distinguishedUnorderedSextet.val := by
  classical
  have ht (i : Omega) : quaternionTetrad (monomialPull a) (monomialPull b) i =
      tetrad i.1 := by
    simp only [quaternionTetrad, hp.2.2.1, hp.2.2.2]
    exact (show ∀ i : Omega,
      ({i, referencePullA i, referencePullB i, referencePullA (referencePullB i)} : Finset Omega) =
        tetrad i.1 by decide) i
  change Finset.univ.image _ = Finset.univ.image tetrad
  ext T
  simp only [Finset.mem_image, Finset.mem_univ, true_and, ht]
  constructor
  · rintro ⟨i, hi⟩; exact ⟨i.1, hi⟩
  · rintro ⟨i, hi⟩; exact ⟨(i,0), hi⟩


/-- Necessary equations for a signed monomial centralizing the literal reference pair.
The pullback is the inverse coordinate permutation, as in `monomialEmbedding_apply`. -/
structure CentralizerParameters (m : GolayMonomialGroup) : Prop where
  sextet : m.right ∈ sextetStabilizer
  involutive : Function.Involutive (monomialPull m)
  square_sign : ∀ i, m.left.toAdd.val i + m.left.toAdd.val (monomialPull m i) = 0
  pull_a : ∀ i, monomialPull m (referencePullA i) = referencePullA (monomialPull m i)
  pull_b : ∀ i, monomialPull m (referencePullB i) = referencePullB (monomialPull m i)
  sign_a : ∀ i, m.left.toAdd.val i + jWord referenceHexB (monomialPull m i) =
    jWord referenceHexB i + m.left.toAdd.val (referencePullA i)
  sign_b : ∀ i, m.left.toAdd.val i + jWord (referenceHexA + referenceHexB) (monomialPull m i) =
    jWord (referenceHexA + referenceHexB) i + m.left.toAdd.val (referencePullB i)

/-- The exact hypotheses of `ReferenceQuaternionBound` supply all enumeration premises. -/
theorem centralizerParameters_of_reference (a b m : GolayMonomialGroup)
    (hp : ReferenceQuaternionPair a b)
    (hm : monomialEmbedding m ^ 2 = 1)
    (hma : Commute (monomialEmbedding m) (monomialEmbedding a))
    (hmb : Commute (monomialEmbedding m) (monomialEmbedding b)) :
    CentralizerParameters m := by
  have hmm : m * m = 1 := monomialEmbedding_injective (by simpa only [map_mul, map_one, pow_two] using hm)
  have hma' : m * a = a * m := monomialEmbedding_injective (by simpa only [map_mul] using hma.eq)
  have hmb' : m * b = b * m := monomialEmbedding_injective (by simpa only [map_mul] using hmb.eq)
  refine ⟨standard_commuting_coordinate_stabilizer a b m (referencePair_parts a b hp) hma hmb,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact congrArg (fun n : GolayMonomialGroup => monomialPull n i) hmm
  · intro i
    exact congrArg (fun n : GolayMonomialGroup => n.left.toAdd.val i) hmm
  · intro i
    have h := congrArg (fun n : GolayMonomialGroup => monomialPull n i) hma'
    change monomialPull a (monomialPull m i) = monomialPull m (monomialPull a i) at h
    simpa only [hp.2.2.1] using h.symm
  · intro i
    have h := congrArg (fun n : GolayMonomialGroup => monomialPull n i) hmb'
    change monomialPull b (monomialPull m i) = monomialPull m (monomialPull b i) at h
    simpa only [hp.2.2.2] using h.symm
  · intro i
    have h := congrArg (fun n : GolayMonomialGroup => n.left.toAdd.val i) hma'
    change m.left.toAdd.val i + a.left.toAdd.val (monomialPull m i) =
      a.left.toAdd.val i + m.left.toAdd.val (monomialPull a i) at h
    simpa only [hp.1, hp.2.2.1] using h
  · intro i
    have h := congrArg (fun n : GolayMonomialGroup => n.left.toAdd.val i) hmb'
    change m.left.toAdd.val i + b.left.toAdd.val (monomialPull m i) =
      b.left.toAdd.val i + m.left.toAdd.val (monomialPull b i) at h
    simpa only [hp.2.1, hp.2.2.2] using h


/-- The affine sextet API applies to the inverse permutation used by the action.
Commutation fixes both marked letters under the destination local maps. -/
theorem centralizer_affine_parameters (m : GolayMonomialGroup) (h : CentralizerParameters m) :
    ∃ (t : hexacode) (g : HexAutomorphisms),
      (∀ i, monomialPull m i = affinePermutation t.val g.val i) ∧
      (∀ i, g.val.localMap (g.val.perm i) (referenceHexA i) = referenceHexA (g.val.perm i)) ∧
      (∀ i, g.val.localMap (g.val.perm i) (referenceHexB i) = referenceHexB (g.val.perm i)) := by
  let s : SextetStabilizer := ⟨m.right⁻¹, sextetStabilizer.inv_mem h.sextet⟩
  obtain ⟨x, hx⟩ := sextetAffineEquiv.surjective s
  have hp : ∀ i, monomialPull m i = affinePermutation x.left.toAdd.val x.right.val i := by
    intro i
    exact (congrArg (fun y : SextetStabilizer => y.val.val i) hx).symm
  refine ⟨x.left.toAdd, x.right, hp, ?_, ?_⟩
  · intro i
    have hc := congrArg (fun z : Omega => rowLabel z.2) (h.pull_a (i,0))
    rw [hp, hp] at hc
    simp only [referencePullA, affinePermutation_apply, Equiv.apply_symm_apply,
      show rowLabel 0 = 0 from rfl, zero_add, map_zero] at hc
    exact add_right_cancel (hc.trans (add_comm _ _))
  · intro i
    have hc := congrArg (fun z : Omega => rowLabel z.2) (h.pull_b (i,0))
    rw [hp, hp] at hc
    simp only [referencePullB, affinePermutation_apply, Equiv.apply_symm_apply,
      show rowLabel 0 = 0 from rfl, zero_add, map_zero] at hc
    exact add_right_cancel (hc.trans (add_comm _ _))


end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.Fusion.ReferenceBound
