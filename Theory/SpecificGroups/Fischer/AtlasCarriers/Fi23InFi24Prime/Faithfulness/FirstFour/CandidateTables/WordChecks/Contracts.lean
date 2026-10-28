module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.CandidateTables.WordChecks.Data
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Faithfulness.FirstFour.CandidateTables.Reduction

/-!
# Independent numerical contracts for the shared-word certificates

The dictionary contract has eleven two-map compositions. The A-family contract
compares the three words v, r, w with their 12/13-stage dictionary evaluations;
the B-family contract adds u and s. These are exhaustive numerical obligations,
not hypotheses supplied by GLS3. `Assembly` discharges the five long-word
comparisons once these independent finite certificates have been constructed.

All quantifiers range over the entire ambient set. Source: `WordEvaluation`,
the retained ATLAS F24G1-p306936B0 data, and GLS3 Table 5.3v.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables.WordChecks
open Certificate Certificate.Ambient

structure DictionaryChecks : Prop where
  d04 : ∀ x, d04Map x = aMap (bInvMap (x))
  d05 : ∀ x, d05Map x = aMap (bMap (x))
  d06 : ∀ x, d06Map x = d04Map (d04Map (x))
  d07 : ∀ x, d07Map x = d05Map (d05Map (x))
  d08 : ∀ x, d08Map x = d04Map (d05Map (x))
  d09 : ∀ x, d09Map x = d04Map (d07Map (x))
  d10 : ∀ x, d10Map x = d08Map (d06Map (x))
  d11 : ∀ x, d11Map x = d07Map (d06Map (x))
  d12 : ∀ x, d12Map x = d05Map (d06Map (x))
  d13 : ∀ x, d13Map x = d10Map (d07Map (x))
  d14 : ∀ x, d14Map x = d06Map (d09Map (x))

structure OutputChecksA : Prop where
  v : ∀ x, vMap x = d14Map (d05Map (d09Map (d09Map (d11Map (d12Map (d10Map (d09Map (d10Map (d13Map (d08Map (d04Map (aMap (x)))))))))))))
  r : ∀ x, rMap x = d12Map (d13Map (d07Map (d05Map (d09Map (d07Map (d11Map (d07Map (d13Map (d12Map (d11Map (d08Map (aMap (x)))))))))))))
  w : ∀ x, wMap x = d10Map (d09Map (d11Map (d14Map (d09Map (d14Map (d11Map (d14Map (d06Map (d07Map (d08Map (d04Map (x))))))))))))

structure OutputChecksB : Prop where
  u : ∀ x, uMap x = bInvMap (d10Map (d09Map (d07Map (d10Map (d08Map (d09Map (d12Map (d06Map (d06Map (d13Map (aMap (x))))))))))))
  s : ∀ x, sMap x = bMap (d11Map (d11Map (d10Map (d10Map (d12Map (d09Map (d07Map (d05Map (d09Map (d09Map (d08Map (d04Map (x)))))))))))))

end Sporadic.Fischer.Fi24Prime.Fi23Lift.CandidateTables.WordChecks
