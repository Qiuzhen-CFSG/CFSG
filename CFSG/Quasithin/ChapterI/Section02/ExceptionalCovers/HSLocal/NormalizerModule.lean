module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Setup
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Action
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Fusion
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.NormalizerModule.Assembly

/-!
# The HS normalizer cover

The actual normalizer quotient and two-core count are constructed in Setup.
Action constructs the faithful binary representation on Qbar and the precise
bridge from linear displacements to involution-coset fusion. Assembly discharges
the concrete model, abelian-section and nonsplitting premises: Q is abelian,
its Sylow-seven decomposition gives E ≃ C₂³, and its four-dimensional Frattini
module is faithful and indecomposable with a natural central quotient.

The genuine universal B.4.8(2) supplies the fixed-displacement identity for the
constructed involution j. This proves fusion in M/E and conjugacy into the
centralizer core; together with the marking inside Q, every involution of M
with nontrivial image has a two-central image in HS. The earlier cover-centralizer
facts and universal B.4.8(2) remain explicit for the higher I.2.2(5) assembly.
All results use the original M, Q, E, Qbar, modelMap and localMap.

Source: Aschbacher–Smith I.2.2(5), final HS paragraph, printed p.412 / PDF p.423,
and B.4.8(2), printed p.91 / PDF p.102.
-/
