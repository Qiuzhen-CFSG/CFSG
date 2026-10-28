module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.OrbitModels
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.CompatibleFlags.Transport
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.CompatibleFlags.Geometry
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.Marking.CompatibleFlags.Assembly

/-!
# Compatible flags and the source quotient-centralizer image

The natural normalizer and augmentation extension construct faithful
permutation actions of the actual H*, extending the marked alternating
component. Relative component normality follows from the source H=KT. A marked source
point identifies its quotient centralizer with the duad stabilizer, whose
image is H1 or L1. Normalization of the binary point puts the actual Sylow
subgroup in that preimage; normalization of the order-two V₁ gives its
centralization by H.

The actual Sylow image supplies a single coordinate change marking both
source flags. In the augmentation cover, the earlier identity
Ṽ₃ = ⟨Ṽ₂^J⟩ yields generation in weight four. Dimension and invariance
then prove the plane marking and retain weight four for all nonzero cover
vectors. No plane marking or image of K₂ is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.7.6(3),
printed pp.938–939, 13.8.6, printed p.948, and §B.3, printed pp.83–85.
`natural_compatible_marking` and `augmentation_compatible_marking` assemble
both flags, the compatible full action and the actual quotient-centralizer
image. The cover result includes faithful descent through `coreToNatural`.
Earlier-source applicability and the remaining clauses of 13.8.6 stay with
the parent parabolic-marking assembly.
-/
