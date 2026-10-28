module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.NormalizerEligibility
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.Representatives
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.GraphComponent
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.PlaneAction
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.FixedLine
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.RepresentativeEnvelope
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.OrdinaryNormalizer
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.GlobalGeometry.Assembly

/-!
# Global geometry of the diagonal cover: normalizer and graph component

The uniform local-cover reduction identifies I with N_G(V₁). Its application
to the larger component is justified by actual outside-family and local-family
membership, relative normality from 1.2.4, exact three-rank two, and the fact
that a perfect subgroup normalizing V₁ centralizes it. This last fact proves
the required noncontainment of Y₊ in the larger component.

Given the representative geometry, the graph-centralizer theorem constructs
an ordinary component from the intrinsic PSL₂(4) residual and E₉ odd-core
models. TI is derived from that geometry. The dihedral lift supplies the
conjugation used to bound the odd core; neither transfer fusion nor a global
component is assumed. The extra centralization premise of I.3.1(2) is proved.

The natural action now constructs the transitive subgroup, and the two-group
center argument with plane interchange proves |Z_S ∩ V₁|=2. Source 15.3.6(3)
then gives the representative-centralizer Sylow subgroup. The precise earlier
I.3.1(3) input constructs an ordinary normal component there, and verified
local-family membership allows 1.2.4 to attach its actual A.3.12 embedding.

`global_geometry_of_local_cover` completes the conditional assembly. The
actual marking transports to the representative-centralizer envelope; the
proved A.3.12 specialization and M₂₃ multiplier exclusion identify its
component with L, yielding C_G(v)≤I. The theorem constructs
`RepresentativeGeometry` and an ordinary component of C_G(τ) for the supplied
Sylow lift. It also derives the fixed-line order from the actual natural
Sylow interchange, and the local SQTK hypotheses from the standing QTKE data.

The cover-reduction consumer retains source 15.3.38 assembly and discharge
of the explicit earlier theorems, uniform local-cover reductions, Sylow lift,
M₂₃ multiplier and intrinsic local cover calculations. This conditional
geometry theorem does not itself assert source 15.3.38.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
proof of 15.3.38, printed pp.1136--1137; I.3.1--2, pp.414--415;
Definition 1.2.3 and Lemma 1.2.4, p.505.
-/
