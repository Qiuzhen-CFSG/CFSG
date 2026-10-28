module
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SevenSylowOvergroups

/-!
# Seven-divisible overgroups of any Sylow subgroup in G₂(2)′

Conjugate the specified Sylow subgroup to the checked positive-root model,
apply its seven-divisibility generation theorem, and transport back through
that same conjugation. This keeps the concrete model calculation separate
from the nested source star-quotient types in the 12.3.3 application.

Source: the binary G₂ local geometry used in Aschbacher–Smith C.2.7
and Lemma 12.3.3, p.808. The imported ATLAS model retains its attribution
and license through LICENSES/ATLAS.txt.
-/

public section
open Subgroup
namespace Atlas.G2.BinaryParabolicPair.SevenSylowOvergroups

theorem eq_top_of_sylow_of_seven_dvd
    (P : Sylow 2 DerivedModel) (D : Subgroup DerivedModel)
    (hPD : (P : Subgroup DerivedModel) ≤ D) (h7 : 7 ∣ Nat.card D) : D = ⊤ := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq DerivedModel P derivedSylow
  let b := MulAut.conj g
  have hs : (P : Subgroup DerivedModel).map b.toMonoidHom = derivedSylow :=
    congrArg Sylow.toSubgroup hg
  have ht := eq_top_of_seven_dvd (D.map b.toMonoidHom) (hs ▸ map_mono hPD) (by
    rwa [←Nat.card_congr (D.equivMapOfInjective b.toMonoidHom b.injective).toEquiv])
  exact map_injective b.injective (ht.trans (map_top_of_surjective _ b.surjective).symm)

end Atlas.G2.BinaryParabolicPair.SevenSylowOvergroups
