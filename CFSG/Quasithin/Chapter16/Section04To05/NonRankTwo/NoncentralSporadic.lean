module

public import CFSG.Quasithin.Chapter16.Section04To05.Basic
public import CFSG.Quasithin.Chapter16.Section04To05.Fusion
public import CFSG.Quasithin.Chapter16.Section04To05.Terminal
public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Models
public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Products
public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.NoncentralSporadic.Basic
public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.NoncentralSporadic.CosetReduction
public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.NoncentralSporadic.Mathieu22

/-!
# Noncentral sporadic components: M₂₂ and structural reductions

The M₂₂ case of the noncentral branch of 16.5.11 is proved. The exported
reductions identify the actual common residual, transfer a faithful small
centralizer bound to elementary R and T_C with trivial Frattini subgroups,
exclude order-four projections over elementary T_C, and construct the final
contradiction from intrinsic residual/coset fusion data.

The full noncentral exclusion remains open. Its remaining obligations are the
faithful small-centralizer calculations, the J₄/M₂₄ transfer cases, and the
covering/fusion calculations for M₁₂, J₂, HS and Ru. These are not assumed
as earlier source results, and no numbered 16.5.11 theorem is asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.1199–1200, proof of Lemma 16.5.11. The central-projection branch is separate.
-/
