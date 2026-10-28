module

public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru.Max6Core.CentralizerBound
public import CFSG.Quasithin.Defs

/-!
# Characteristic two of the actual Rudvalis max6 subgroup

The five explicit conjugates of the first ATLAS generator's fifth power generate
an abelian normal two-subgroup. Its intrinsic centralizer has at most 128
elements and contains that seed, which has at least 64 elements. The centralizer
is consequently a normal two-subgroup as well. Both lie in O₂(max6), so
C_max6(O₂(max6)) lies in that centralizer and hence in O₂(max6).

Every subgroup and centralizer is taken inside the unchanged RuG1-max6W1
subgroup of the original degree-4060 model. No ambient order, Sylow certificate,
maximal-local catalogue or asserted extension structure enters this calculation.
Source: Aschbacher--Smith, Theorem 0.1.2(5), printed p.4, repeated as
Theorem 0.1.1(5), printed p.482;
GLS3 Table 5.3r, p.279, the 2A centralizer row.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.RuEven
open Rudvalis.SylowOvergroups Max6Core

/-- The intrinsic two-core of the literal ATLAS max6 subgroup is self-centralizing. -/
public theorem max6_pCore_selfCentralizing :
    Subgroup.centralizer (pCore 2 max6 : Set max6) ≤ pCore 2 max6 := by
  have hseed : normalSeed ≤ pCore 2 max6 :=
    le_sSup ⟨normalSeed_normal, normalSeed_isPGroup⟩
  have hnormal : seedCentralizer.Normal :=
    inferInstanceAs (Subgroup.centralizer (normalSeed : Set max6)).Normal
  have hc : seedCentralizer ≤ pCore 2 max6 :=
    le_sSup ⟨hnormal, seedCentralizer_isPGroup⟩
  exact (Subgroup.centralizer_le hseed).trans hc

/-- Characteristic two of the actual sixth Rudvalis ATLAS subgroup. -/
public theorem max6_characteristicTwo : HasCharacteristicTwo max6 :=
  max6_pCore_selfCentralizing

end CFSG.Quasithin.MainConverse.SporadicLocal.RuEven
