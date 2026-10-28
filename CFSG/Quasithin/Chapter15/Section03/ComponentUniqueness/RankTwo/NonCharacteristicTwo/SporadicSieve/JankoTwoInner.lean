module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.JankoTwoExtension
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ShadowBounds
public import CFSG.Quasithin.MainConverse.SporadicLocal.J2.LocalCover
public import CFSG.Quasithin.MainConverse.SporadicLocal.J2.EvenCharacteristic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PairNormalizer
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic

/-!
# The surviving J₂ component has its full automorphism group

First rule out a rank-two local configuration inside the actual J₂ carrier.
Even characteristic and the source maximality condition make the specified
local subgroup maximal two-local. Sylow conjugacy then applies the exhaustive
two-candidate catalogue. The first candidate has order 1920, not divisible
by 36. The second has order 1152 and two-core order 64; the full Frattini
shadow would force its order to be at least 36 · 64 = 2304.

Thus a component quotient marked as J₂ is proper in I/C_I(L). Its sharp
outer bound supplies surjectivity of the faithful canonical action, producing
the requested compatible `JankoTwoIdentification`. No additional local,
order, simplicity, or automorphism premise remains in the J₂ case.
The nine other sporadic carriers require their separate exclusions.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.41--42,
printed p.1138; GLS3 Table 5.3g. The actual fixed ATLAS J2G1-p100B0 carrier
and the imported finite certificates are used throughout.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.JankoTwoInner
open Sporadic.LeechRelated.J2
open Sporadic.LeechRelated.J2.ExceptionalParabolics
open CFSG.Quasithin.MainConverse.SporadicLocal

variable {H : Type*} [Group H] [Finite H]

private theorem localCover (P : Sylow 2 Carrier) (M : Subgroup Carrier)
    (hM : IsMaximalTwoLocal M) (hPM : (P : Subgroup Carrier) ≤ M) :
    Nonempty (M ≃* Seed.l₁) ∨ Nonempty (M ≃* Seed.p₂) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Carrier P J2Even.sylowTwo
  have hm := (Theory.Quasithin.maximalTwoLocal_overgroup_conj_iff g P M).mpr ⟨hM, hPM⟩
  rw [hg] at hm
  rcases J2Even.sylowLocalCover _ hm.1 hm.2 with h | h
  · obtain ⟨e⟩ := h
    exact Or.inl ⟨((MulAut.conj g).subgroupMap M).trans e⟩
  · obtain ⟨e⟩ := h
    exact Or.inr ⟨((MulAut.conj g).subgroupMap M).trans e⟩

private theorem core_card_of_equiv (A B : Type*) [Group A] [Group B] (e : A ≃* B) :
    Nat.card (pCore 2 A) = Nat.card (pCore 2 B) := by
  rw [← pCore_map_iso 2 e, card_map_of_injective e.injective]

/-- Neither Sylow-containing local candidate in the actual J₂ carrier admits the source shadow. -/
theorem no_localConfiguration (e : H ≃* Carrier) (K M Y S : Subgroup H)
    (d : LocalConfiguration K M Y S) : False := by
  obtain ⟨P, hP⟩ := d.sylow
  have heven : IsEvenCharacteristic H :=
    CFSG.Quasithin.MainConverse.evenCharacteristic_of_model_equiv e J2Even.evenCharacteristic
  obtain ⟨N, hMN, hN⟩ := Finite.exists_le_maximal d.twoLocal
  have hF := generalizedFitting_eq_pCore_of_selfCentralizing 2
    (heven P N hN ((hP.symm ▸ d.sylow_le).trans hMN))
  have hM : IsMaximalTwoLocal M := (d.maximal N hMN hF) ▸ hN
  have hmapM := Theory.Quasithin.isMaximalTwoLocal_map e hM
  have he : Function.Surjective e.toMonoidHom := e.surjective
  have hPM : ((P.mapSurjective he : Sylow 2 Carrier) : Subgroup Carrier) ≤
      M.map e.toMonoidHom := by
    change (P : Subgroup H).map e.toMonoidHom ≤ M.map e.toMonoidHom
    exact map_mono (hP.symm ▸ d.sylow_le)
  obtain ⟨hdiv, hbound⟩ := shadow_local_order_bounds P M Y S hP d.sylow_le
    (d.yplus_le.trans inf_le_left) d.shadow
  rcases localCover (P.mapSurjective he) _ hmapM hPM with h | h
  · obtain ⟨f⟩ := h
    have hcard := (Nat.card_congr ((e.subgroupMap M).trans f).toEquiv).trans FirstParabolic.card_l₁
    rw [hcard] at hdiv
    norm_num at hdiv
  · obtain ⟨f⟩ := h
    have hf := (e.subgroupMap M).trans f
    have hcard := (Nat.card_congr hf.toEquiv).trans PairNormalizer.card_p₂
    have hcore := (core_card_of_equiv _ _ hf).trans
      (PairNormalizer.p₂_core_and_quotient SecondParabolic.l₂_core_card).1
    rw [hcard, hcore] at hbound
    norm_num at hbound

variable {G : Type*} [Group G] [Finite G] {I L M Y S : Subgroup G}
variable [(L.subgroupOf I).Normal]

/-- The local configuration forces a genuine extension of the J₂ component image. -/
theorem componentImage_ne_top (d : ComponentSetup I L M Y S)
    (e : L ⧸ pCore 2 L ≃* Carrier) : componentImage I L L ≠ ⊤ := by
  intro htop
  let a : ComponentQuotient I L ≃* componentImage I L L :=
    (Subgroup.topEquiv).symm.trans (MulEquiv.subgroupCongr htop.symm)
  exact no_localConfiguration (a.trans (componentModel d e)) _ _ _ _ d.quotient_local

/-- The complete J₂ case, with both model isomorphisms and their inner compatibility. -/
theorem jankoTwo_identification (d : ComponentSetup I L M Y S)
    (e : L ⧸ pCore 2 L ≃* Carrier) : Nonempty (JankoTwoIdentification I L) :=
  ⟨JankoTwoExtension.identificationOfProper d e (componentImage_ne_top d e)⟩


end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.JankoTwoInner
