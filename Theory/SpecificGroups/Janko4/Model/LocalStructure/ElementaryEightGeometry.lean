module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Data
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Rows
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.FixedMasks
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.PairImages
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.KernelCentralizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.PairKernel
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Lifts
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Application

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Nondegenerate
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Loewy.Assembly
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.IsotropicNormalizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.NormalizerAssembly

/-!
# Native elementary order-256 geometry

This umbrella exports the literal Figure 1/2 rows, corrected native word
lifts, and two elementary subgroups of order 256 with nondegenerate intrinsic
forms. The full quotient centralizers identify the full ambient centralizers
of both displayed unprimed rows and the signed primed (d) row, and prove
self-centralization. Application retains literal conjugation, whole-normalizer
enlargement, maximal two-local equality at the centralizer stage, and arbitrary
radical restriction with unchanged normalizer and local-core maps. Source-wide
selection remains with the cover. Bounded kernel corrections now identify
the full centralizers of arbitrary elementary lifts of all three selected
images, and the explicit native fusion word gives their common conjugacy
class. An explicit zero-form sixteen and its selected-row transports are
also constructed. The canonical displacement layers and their rank-defect set
are preserved by the whole normalizer. The checked Loewy certificates identify
the rank-defect set with the explicit isotropic sixteen, and the resulting
normalizer containment feeds the fusion transports, maximal two-local equalities,
and radical restrictions with their literal local-core maps.
Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988),
Propositions 2.3.4--2.3.5 and Corollary 2.3.6.
-/
