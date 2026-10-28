module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.Generation
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.Fusion
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.Selection
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.SourceAssembly

/-!
# Conditional A₆ involution-fusion and rank-one theorem

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 2.5.26, printed pp.568–569.

`primeRank_eq_one_of_source_alternatives` assembles the conditional source
argument. The exceptional A₈ branch gives S_C≃D₈, |S|=256, cyclic-four TI
fusion and |T|=512. The actual C₂×S₈ extension and its two characteristic-two
overgroups contradict Γe0=∅. This establishes the component claim at every
involution of S_C and its relative normality, discharging the missing premise
of the centralizer-generation and quasithin rank-one argument.

`RankOneSetup`, `SourceAlternatives`, and `EarlierSelection` state the earlier
source inputs. `FiniteModelIdentities` enumerates the five remaining Aut(A₆)
inputs. The parent source-theorem owner must supply them and the earlier
fusion and normalizer-index identities; this module proves their substantive
conditional implication, not those earlier results.
-/
