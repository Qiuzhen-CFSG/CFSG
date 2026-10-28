module

public import CFSG.Quasithin.Chapter16.Section04To05.Basic
public import CFSG.Quasithin.Chapter16.Section04To05.Fusion
public import CFSG.Quasithin.Chapter16.Section04To05.Terminal
public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Models
public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Products
public import Theory.GroupTheory.Perm.SevenPointIndexTen
public import Theory.GroupAction.OddFourGroupLine

/-!
# Non-rank-two component elimination: common obstructions

The intended outputs are Lemmas 16.5.11–12 of Aschbacher–Smith, combined
manuscript of 1 March 2004, printed pp.1199–1201. Their source-theorem
assembly remains open. This module currently exports the exact output
catalogue and proved ingredients: the noncentral coset-product construction,
the odd-action obstruction to characteristic lines and distinguished squares
in a four-group, and the faithful seven-point order/index contradiction.

The remaining obligations are the covered sporadic configuration, the
noncentral sporadic reduction including J₄/M₂₄ transfer, and the binary
linear configuration and orbit arguments. Those obligations must be proved
from genuine earlier source outputs before exporting either numbered lemma.
-/
