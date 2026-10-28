module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveFaithfulSylow
public import CFSG.Quasithin.ClassificationModels.Families
public import CFSG.Quasithin.MainConverse.MathieuLocal.M11Even
public import CFSG.Quasithin.MainConverse.MathieuLocal.M12Even
public import CFSG.Quasithin.MainConverse.MathieuLocal.M22Even
public import CFSG.Quasithin.MainConverse.MathieuLocal.M23Even
public import CFSG.Quasithin.MainConverse.MathieuLocal.M24Even
public import CFSG.Quasithin.MainConverse.SporadicLocal.J2.EvenCharacteristic
public import CFSG.Quasithin.MainConverse.SporadicLocal.J4.SylowCenterEven
public import CFSG.Quasithin.MainConverse.SporadicLocal.HS
public import CFSG.Quasithin.MainConverse.SporadicLocal.He
public import CFSG.Quasithin.MainConverse.SporadicLocal.Ru
public import Theory.SpecificGroups.Janko4.Model.Cardinality
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup
public import Theory.Mathieu.M24.Properties.Order

/-!
# Sporadic containers of a full-Sylow local A₅

All sporadic carriers in the Theorem C list satisfy even characteristic,
and their orders are divisible by sixteen. A full normalizing Sylow acts
faithfully on the actual A₅ and hence has order dividing eight. This
excludes these containing rows without a maximal-subgroup catalogue.
The additional J₁ row is deliberately retained by the eventual shortlist.

Source: Aschbacher--Smith A.3.14 and10.2.1, printed pp.49--50 and743.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFive
variable {G : Type*} [Group G] [Finite G]

private theorem held_sixteen : 16 ∣ Nat.card Held.He := by
  open Held.LocalPairs.SylowGeometry.Calculations in
  obtain ⟨n,hn⟩ := representative_isPGroup.exists_card_eq
  have hl := Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.representative_card_ge_of_orbit_labels
    Held.LocalPairs.SylowGeometry.Calculations.InnerNormalizer.orbitSizeLabel_eq_card_orbit
  have hn4 : 4 ≤ n := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    exact (by decide : 2 ^ 4 ≤ 1024).trans (hn ▸ hl)
  have hd : 16 ∣ Nat.card Held.LocalPairs.SylowGeometry.Calculations.representative := by
    rw [hn]
    exact pow_dvd_pow 2 hn4
  exact hd.trans (card_subgroup_dvd_card _)

private theorem hs_sixteen : 16 ∣ Nat.card Sporadic.LeechRelated.HS.Carrier := by
  apply dvd_trans (b := Nat.card Sporadic.LeechRelated.HS.EvenLocalCandidates.subgroup)
  · rw [Sporadic.LeechRelated.HS.EvenLocalCandidates.subgroup_card]
    decide
  · exact card_subgroup_dvd_card _

/-- No sporadic carrier in Theorem C has a normalized full-Sylow local A₅. -/
theorem not_sporadic (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (eB : B ≃* alternatingGroup (Fin 5))
    (name : ClassificationModels.SporadicName) (hne : name ≠ .j3)
    (he : Nonempty (G ≃* name.Carrier)) : False := by
  obtain ⟨e⟩ := he
  have hs (hE : IsEvenCharacteristic G) : ¬ 16 ∣ Nat.card G :=
    not_sixteen_dvd_of_evenCharacteristic S (hE S) hB hSB eB
  cases name with
  | m11 =>
    change G ≃* Sporadic.Mathieu.M11 at e
    apply hs (MainConverse.evenCharacteristic_of_model_equiv e MainConverse.m11_evenCharacteristic)
    rw [Nat.card_congr e.toEquiv]
    rw [Sporadic.Mathieu.m11_order]
    decide
  | m12 =>
    change G ≃* Sporadic.Mathieu.M12 at e
    apply hs (MainConverse.evenCharacteristic_of_model_equiv e MainConverse.m12_evenCharacteristic)
    rw [Nat.card_congr e.toEquiv]
    rw [Sporadic.Mathieu.m12_order]
    decide
  | m22 =>
    change G ≃* Sporadic.Mathieu.M22 at e
    apply hs (MainConverse.evenCharacteristic_of_model_equiv e MainConverse.m22_evenCharacteristic)
    rw [Nat.card_congr e.toEquiv]
    rw [Sporadic.Mathieu.m22_order]
    decide
  | m23 =>
    change G ≃* Sporadic.Mathieu.M23 at e
    apply hs (MainConverse.evenCharacteristic_of_model_equiv e MainConverse.m23_evenCharacteristic)
    rw [Nat.card_congr e.toEquiv]
    rw [Sporadic.Mathieu.m23_order]
    decide
  | m24 =>
    change G ≃* Sporadic.Mathieu.M24 at e
    apply hs (MainConverse.evenCharacteristic_of_model_equiv e MainConverse.m24_evenCharacteristic)
    rw [Nat.card_congr e.toEquiv]
    rw [Sporadic.Mathieu.m24_order]
    decide
  | j2 =>
    change G ≃* Sporadic.LeechRelated.J2.Carrier at e
    apply hs (MainConverse.SporadicLocal.J2Even.evenCharacteristic_of_equiv e)
    rw [Nat.card_congr e.toEquiv]
    rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier]
    decide
  | j3 => exact hne rfl
  | j4 =>
    change G ≃* Janko4.Model at e
    apply hs (MainConverse.SporadicLocal.J4SylowCenterEven.evenCharacteristic_of_equiv e)
    rw [Nat.card_congr e.toEquiv]
    rw [Janko4.Cardinality.model_card]
    decide
  | hs =>
    change G ≃* Sporadic.LeechRelated.HS.Carrier at e
    apply hs (MainConverse.evenCharacteristic_of_model_equiv e MainConverse.SporadicLocal.hs_evenCharacteristic)
    rw [Nat.card_congr e.toEquiv]
    exact hs_sixteen
  | he =>
    change G ≃* Held.He at e
    apply hs (MainConverse.SporadicLocal.he_evenCharacteristic_of_equiv e)
    rw [Nat.card_congr e.toEquiv]
    exact held_sixteen
  | ru =>
    change G ≃* Rudvalis.Model at e
    apply hs (MainConverse.evenCharacteristic_of_model_equiv e MainConverse.SporadicLocal.ru_evenCharacteristic)
    rw [Nat.card_congr e.toEquiv]
    rw [Rudvalis.model_card]
    decide

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFive
