module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.MovingLayer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.Conventions
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.Reconstruction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.Classification

/-!
# Binary MS93 module alternatives and local estimates

`alternatives` proves the four exhaustive binary alternatives of MS93 (3.2)
from the actual local source, its critical geometry, and positive critical
distance. The natural maps keep the specified quotient and a common marking;
both nonsplit extensions are retained.

`Classification` combines the source edge generation from `Reconstruction`
with `FixedGeneration` to prove the central-sum identity for Z. This proves
[X,Ltilde] = U and Z = C U before transporting the abstract attachment
classification, including the order-two central kernel and [X:Z] = 2.

`BadEstimates` proves offender uniqueness and the source (3.3), (2.3)(c,d)
commutator estimates conditional on the actual bad alternatives. It keeps the
endpoint Z(a,a') in X_a' and nonnormality relative to G_a.
`alternatives_with_estimates` packages these consequences with the exhaustive
alternatives when b > 2. Their later exclusion by source (3.8) remains with
the natural-structure assembly.
Source: Meierfrankenfeld–Stellmacher (1993), pp.857–858,863–868,877–878.
-/
