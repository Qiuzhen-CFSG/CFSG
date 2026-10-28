module

public import CFSG.Quasithin.Defs
public import Theory.Quasithin.EvenCharacteristic

/-!
# Transport from concrete carriers in the converse

Classification model witnesses may identify a group in an arbitrary universe
with a concrete carrier in Type. Transport the even-characteristic condition
across such witnesses by mapping the Sylow subgroup and maximal 2-local,
then using the induced equivalence on the local groups and their two-cores.

Source: Aschbacher–Smith, Theorem 0.1.2 and condition E, printed pp.3–4.
-/

namespace CFSG.Quasithin.MainConverse

public theorem evenCharacteristic_of_model_equiv {G H : Type*} [Group G] [Group H]
    [Finite G] [Finite H] (e : G ≃* H) (hH : IsEvenCharacteristic H) :
    IsEvenCharacteristic G := by
  intro T M hM hTM
  let P := T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hle : (P : Subgroup H) ≤ M.map e.toMonoidHom := by
    simpa [P, Sylow.coe_mapSurjective] using
      Subgroup.map_mono (f := e.toMonoidHom) hTM
  have hlocal := hH P (M.map e.toMonoidHom)
    (Theory.GroupTheory.isMaximalTwoLocal_map e hM) hle
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (Subgroup.equivMapOfInjective M e.toMonoidHom e.injective)).mpr hlocal

end CFSG.Quasithin.MainConverse
