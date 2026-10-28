module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Ambient
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Syntheme

/-!
# Two-cores for the six-letter permutation models

The actual duad and syntheme stabilizers in `A₆` have elementary abelian
two-cores of order four, and those in `S₆` have elementary abelian two-cores
of order eight. Each parabolic modulo its intrinsic two-core is `S₃`, and
the kernel of conjugation on the core is exactly the core itself. Explicit
binary coordinates and quotient equivalences are exported for all four
parabolics.

The even parabolics act irreducibly on their cores, with normality taken in
the parabolic. Each symmetric parabolic instead has a normal subgroup of
order two strictly inside its core: the two-letter factor for the duad and
the simultaneous within-block swap for the syntheme. This retains the
reducible-action exception in the source argument. Both ambient groups have
trivial two-core and trivial center.

The proofs identify the actual stabilizers with `S₂ × S₄` and `C₂ wr S₃`,
and restrict these identifications to the even subgroups. Their surjections
onto `S₃`, whose two-core is trivial, identify the displayed kernels with
the intrinsic cores. The conjugation calculations then give the asserted
centralizers and invariant-subgroup statements.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, I.5.7,
printed pp. 420–421. These are the local model facts used in its proof;
the ambient D-system and geometric conclusions are assembled by its consumer.
-/
