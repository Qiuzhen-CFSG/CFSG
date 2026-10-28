module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Covers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.CoverageReduction
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.TwoCore.Definitions
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.TwoCore.Max4Core
public import Theory.GroupTheory.PCoreFromTwoNormalizers

/-!
# Rudvalis maximal two-cores from local generation

Choose a Sylow two-subgroup of max4, and consider its ambient image P,
the image U of O₂(max4), and the image V of Z(P). If U is nontrivial,
then P and V are nontrivial too. The two-normalizer generation condition
forces every proper odd-index subgroup to have a nontrivial intrinsic
two-core, by the coset fixed-point and subgroup-union arguments in
`Theory.GroupTheory.PCoreFromTwoNormalizers`.

The nontrivial max4 core is constructed from three explicit commuting
involutions in `TwoCore.Max4Core`. The exhaustive double-coset cover and
representative word checks in `TwoCore.Generation` discharge the generation
premise. Thus `rudvalis_oddIndexMaximalTwoCore` proves the requested
maximal-subgroup exclusion unconditionally on the actual degree-4060 model.
The source consumer's PairInput and radical-cover hypothesis are unnecessary
for this conclusion. Identifying the maximal subgroups with the two ATLAS
candidates remains the separate coverage assembly's responsibility.

Source: Aschbacher--Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528), citing Aschbacher, *Overgroups of Sylow subgroups in sporadic
groups*, Memoirs AMS 60 (1986), no.343. The concrete generation calculation
uses checked word certificates, independently of GLS3 Table 5.3r and of the
candidate cardinality bounds.
-/

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining

open Subgroup Rudvalis.SylowOvergroups.TwoCore

/-- The fixed-local core and generation calculation suffice for the
requested maximal two-core theorem. The next corollary supplies the core
premise; the generation premise remains a separate obligation. -/
public theorem rudvalis_oddIndexMaximalTwoCore_of_nontrivialCore_of_generatorRecovery
    (hcore : pCore 2 Rudvalis.SylowOvergroups.max4 ≠ ⊥)
    (hgen : GeneratorRecovery) :
    Rudvalis.SylowOvergroups.OddIndexMaximalTwoCore := by
  obtain ⟨S, hS⟩ := hgen
  have hP := sylowImage_isPGroup S
  have hUP := coreImage_le S
  have hU : coreImage ≠ ⊥ := fun h => hcore
    (((pCore 2 Rudvalis.SylowOvergroups.max4).map_eq_bot_iff_of_injective
      Rudvalis.SylowOvergroups.max4.subtype_injective).mp h)
  let _ : Nontrivial (sylowImage S) := (nontrivial_iff_ne_bot _).mpr
    (fun hb => hU (bot_unique (hUP.trans_eq hb)))
  have hV : centerImage S ≠ ⊥ := fun h => hP.bot_lt_center.ne'
    (((center (sylowImage S)).map_eq_bot_iff_of_injective
      (sylowImage S).subtype_injective).mp h)
  intro M hM hodd
  exact pCore_ne_bot_of_two_normalizers_of_index_primeTo
    (sylowImage S) coreImage (centerImage S) M hP hUP (centerImage_le S)
    hU hV hS hM.ne_top hodd

/-- The explicit max4 core discharges the local nontriviality obligation,
reducing the maximal two-core assertion to the generation calculation. -/
public theorem rudvalis_oddIndexMaximalTwoCore_of_generatorRecovery
    (hgen : GeneratorRecovery) :
    Rudvalis.SylowOvergroups.OddIndexMaximalTwoCore :=
  rudvalis_oddIndexMaximalTwoCore_of_nontrivialCore_of_generatorRecovery
    max4_pCore_ne_bot hgen

/-- Every odd-index maximal subgroup of the concrete Rudvalis model has
nontrivial two-core, taken intrinsically inside that maximal subgroup. -/
public theorem rudvalis_oddIndexMaximalTwoCore :
    Rudvalis.SylowOvergroups.OddIndexMaximalTwoCore :=
  rudvalis_oddIndexMaximalTwoCore_of_generatorRecovery rudvalis_generatorRecovery

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicRemaining
