module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.ModuleContradiction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.PostSylowInputs
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.RatioSource.SourceAssembly
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.SourceFactors.Permutation.SourceModules
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.SourceEndgame
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceExclusion
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.BinaryBranch.SourceClassification.QuasisimpleApplication

public import Theory.GroupTheory.OrderFourIntersectionObstruction
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification
public import CFSG.Quasithin.Chapter15.Section04.SourceReduction

/-!
# Completing the case with no noncentral local components

Aschbacher--Smith, *The Classification of Quasithin Groups*, combined manuscript,
1 March 2004, §15.4, printed pp. 1155–1166.

The terminal intersection argument for Theorem 15.4.24 is supplied by
`Subgroup.no_dihedral_join_of_order_four_intersections`. Its inputs correspond
to `A = O₂(X₁)`, `A' = O₂(X₂)`, `B = O₂(Y₁)`, and `E = O₂(X)` in the final
paragraph of the proof on p. 1165. The argument forces `B ≤ E`, contradicting
the dihedral structure of `A ⊔ B`.

The source-module variant now derives the contradiction from actual normal
A₆ supplements and S₆ quotients for both factor choices. Its abelian
containing subgroup is V(M₁), so it does not need the stronger E₁₆ equality.
The centralizer-overgroup split in Theorem E is also proved, including
nonemptiness before inferring uniqueness. Source 15.4.17 now has all earlier
inheritance premises discharged. After the original 15.4.19–20 inputs, one
family of Sylow choices supplies the central-involution hypotheses and
fitting implications for all four factor pairs. Construction of the local data
and recognition inputs, and the full Theorems 15.4.24 and 15.4.25, remain
with their source assembly owners.

The four-clause source 15.4.2 family is assembled on its original quotient,
including the cubic-ratio case split and its Xi-minus application. The
B.6.8(5) input is discharged; universal A/C, D.1, solvable E.2.9 and 3.1.1
remain with their earlier source producers.

The double-case Y-module action now constructs its actual residual factor
pair, the maximal-overgroup permutation action, Sylow interchange and the
index-two factor stabilizer. The same pair has individually Baumann-invariant
factors, the required Thompson commutator identities, and complementary
order-four modules. The surviving exchanged-block case of the contrary
Sylow argument is excluded from its actual block data; construction of that
data and the other cases remain with the source Sylow assembly.
The preceding source inputs now construct 15.4.19 for all four factor pairs,
with the actual J(T), central four-group, index-three subgroups and their
intersections. The full 15.4.20 overgroup-Sylow conclusion remains separate.
-/
