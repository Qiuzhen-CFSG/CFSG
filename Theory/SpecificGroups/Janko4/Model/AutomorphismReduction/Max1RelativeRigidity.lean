module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.Commutant
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.CommutatorImage
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.PairOrbit
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.RelativeCocycles
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.Max1RelativeRigidity.QuotientFixers

/-!
# Actual max1 action, relative automorphism rigidity and the kernel-pair orbit

The four local results concern the literal ATLAS max1 subgroup `M`, its
2048-element kernel `K`, its generators `x,y`, and its marked kernel pair `v`,
all at the canonical matrix-generator proofs:

* `commutant_endomorphism` gives precisely the zero and identity endomorphisms
  commuting with the actual action; `commutant_automorphism` gives the identity
  as the only automorphism. `fixes_kernel_of_quotient_fixed` applies this to
  automorphisms inducing the identity on `M/K`.
* `mem_kernel_of_commutator_image` puts `c` in `K` whenever every right
  commutator `c⁻¹*e*c*e⁻¹`, for `e ∈ K`, lies in `⟨v⟩`. Faithfulness and
  quotient involution coverage reduce this to two checked displacement pairs.
* `relative_cocycle_rigidity` proves that a pointwise kernel fixer whose right
  displacement on `C_M(v)` lies in `⟨v⟩` is conjugation by one or v. Five actual
  stabilizer words constrain the two generator displacements to the two
  principal possibilities. `relative_rigidity_of_quotient_fixed` supplies
  the equivalent route starting from identity on the quotient.
* `pair_orbit_card`, `pair_centralizer_index` and `pair_centralizer_card` give
  the actual orbit size and index 1771, and centralizer order 283115520,
  using the checked 2048-mask orbit tree and the coordinate bijection.

The action commutant uses left conjugation. The displacement uses the right
cocycle convention `delta(gh) = h⁻¹ * delta(g) * h * delta(h)`. All finite
calculations are connected to the certified actual kernel basis; none remains
as a hypothesis. These are local relative results and do not assert global
innerness or vanishing of the whole first cohomology group.

Sources: literal ATLAS `J4G1-max1W1`, documented in `Cardinality.Subgroup`,
and the local structure in GLS3, Table 5.3i.
-/
