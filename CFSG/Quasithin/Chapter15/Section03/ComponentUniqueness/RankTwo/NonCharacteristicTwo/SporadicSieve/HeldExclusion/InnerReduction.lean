module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.Definitions
public import CFSG.Quasithin.MainConverse.Transport
public import Theory.SpecificGroups.Held.TwoLocalCandidates
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Reducing the inner Held case to the three literal local candidates

Even characteristic and maximality subject to F*=O₂ make the specified
local subgroup maximal two-local. Conjugating its Sylow subgroup into
the Sylow used by the supplied exhaustive catalogue identifies the local
subgroup with a conjugate of max3, max4 or max5. Actual isomorphisms then
transport the three-core of its two-core quotient.

The catalogue is the corrected catalogue of maximal two-local normalizers,
not the impossible legacy equality between elementary subgroups and whole
candidates. Exhaustive coverage and the three candidate bounds remain
explicit premises. This does not assert the inner Held exclusion.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.41--42,
printed p.1138; GLS3 Table 5.3p.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion

private theorem card_threeCore_quotient_congr {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) : Nat.card (pCore 3 (A ⧸ pCore 2 A)) = Nat.card (pCore 3 (B ⧸ pCore 2 B)) := by
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  rw [← pCore_map_iso 3 q]
  exact (card_map_of_injective (f := q.toMonoidHom) q.injective).symm

/-- The adequate normalizer cover and the three concrete core bounds exclude
nine from the local three-core in the inner Held case. -/
theorem inner_local_profile_of_cover {H : Type*} [Group H] [Finite H]
    (e : H ≃* Held.He) (K M Y S : Subgroup H) (d : LocalConfiguration K M Y S)
    (heven : IsEvenCharacteristic Held.He)
    (hcover : ∃ T : Sylow 2 Held.He, ∀ N : Subgroup Held.He,
      IsMaximalTwoLocal N → (T : Subgroup Held.He) ≤ N →
      ∃ (i : Fin 3) (g : Held.He),
        N = (Held.TwoLocalCandidates.subgroup i).map (MulAut.conj g).toMonoidHom)
    (hcores : ∀ i : Fin 3, ¬ 9 ∣ Nat.card (pCore 3
      (Held.TwoLocalCandidates.subgroup i ⧸ pCore 2 (Held.TwoLocalCandidates.subgroup i)))) :
    ¬ 9 ∣ Nat.card (pCore 3 (M ⧸ pCore 2 M)) := by
  obtain ⟨P, hP⟩ := d.sylow
  have hevenH : IsEvenCharacteristic H :=
    CFSG.Quasithin.MainConverse.evenCharacteristic_of_model_equiv e heven
  obtain ⟨N, hMN, hN⟩ := Finite.exists_le_maximal d.twoLocal
  have hF := generalizedFitting_eq_pCore_of_selfCentralizing 2
    (hevenH P N hN ((hP.symm ▸ d.sylow_le).trans hMN))
  have hM : IsMaximalTwoLocal M := (d.maximal N hMN hF) ▸ hN
  have hmapM := Theory.Quasithin.isMaximalTwoLocal_map e hM
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hQM : (Q : Subgroup Held.He) ≤ M.map e.toMonoidHom :=
    map_mono (hP.symm ▸ d.sylow_le)
  obtain ⟨T, hcover⟩ := hcover
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Held.He Q T
  have hm := (Theory.Quasithin.maximalTwoLocal_overgroup_conj_iff g Q
    (M.map e.toMonoidHom)).mpr ⟨hmapM, hQM⟩
  rw [hg] at hm
  obtain ⟨i, c, he⟩ := hcover _ hm.1 hm.2
  let f : M ≃* Held.TwoLocalCandidates.subgroup i :=
    ((e.subgroupMap M).trans ((MulAut.conj g).subgroupMap (M.map e.toMonoidHom))).trans
      ((MulEquiv.subgroupCongr he).trans ((MulAut.conj c).subgroupMap _).symm)
  rw [card_threeCore_quotient_congr f]
  exact hcores i

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion
