module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Obstructions
public import BenderSuzuki.SE.Section11Lemma114Models
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.SpecificGroups.Tits.FiniteImageOrder

/-!
# Five characteristic-two branches of the seven-component inspection

Binary PSL₂ has cyclic Sylow three-subgroups, while Suzuki has three-free
order. The actual small derived symplectic group is A₆; the actual derived
G₂(2) embeds in a group of order 12096. These exclude respectively the
three-rank, factor three, factor seven, and factor five required by a seven
component. For Parrott's Tits presentation, the supplied simplicity makes
its certified map onto the group of order 17971200 injective; that order
has no factor seven. Independent simplicity certification is unnecessary.

Every result concerns the entire two-subgroup of actual automorphisms.
The proofs exclude even arbitrary seven subgroups, so they do not require
any invalid upward transfer of ordinary component membership.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.18,
printed p.252; Theorem C and Remark A.2.4, printed p.33. The concrete model
calculations and their original source attributions are in the imports.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
variable {S : Type*} [Group S]

/-- The complete binary PSL₂ branch, including every allowed field degree. -/
theorem linear_rank_one [Finite S] {f : ℕ} (hf : 2 ≤ f)
    (h : ClassicalGroup.IsPSL S 2 (2 ^ f)) : SevenActionInspection S := by
  apply inspection_of_primeRank_le_one
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  let _ := Fintype.ofFinite F
  let _ := Fintype.ofFinite (BenderSuzuki.PFAppendixIII.BinaryGaloisField f)
  let ef : F ≃+* BenderSuzuki.PFAppendixIII.BinaryGaloisField f :=
    FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard]
      exact (GaloisField.card 2 f (by omega)).symm)
  let em := e.trans (Theory.PSL2.OuterSolvable.projectiveRingEquiv ef)
  let P : Sylow 3 S := Classical.choice inferInstance
  exact P.primeRank_le_one_of_isCyclic
    (BenderSuzuki.lemma114_psl2_oddSylow_isCyclic_of_equiv hf em 3 (by decide) P)

/-- The complete Suzuki branch uses the order of the actual matrix model. -/
theorem suzuki {m : ℕ} (hm : 1 ≤ m)
    (h : Nonempty (S ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) :
    SevenActionInspection S := by
  obtain ⟨e⟩ := h
  apply inspection_of_not_dvd_card
  intro hd
  have hthree : 3 ∣ Nat.card S := (by decide : 3 ∣ 2520).trans hd
  rw [Nat.card_congr e.toEquiv] at hthree
  exact BenderSuzuki.MatrixGroups.suzukiMatrixGroup_three_free m (by omega) hthree

/-- The actual commutator of the projective binary symplectic group is A₆. -/
theorem symplectic_derived
    (h : Nonempty (S ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    SevenActionInspection S := by
  obtain ⟨e⟩ := h
  let a := e.trans
    Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix
  apply inspection_of_not_dvd_card
  rw [Nat.card_congr a.toEquiv, nat_card_alternatingGroup]
  norm_num

/-- The actual G₂(2) commutator embeds in the five-free full octonion group. -/
theorem g2_derived (h : Nonempty (S ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    SevenActionInspection S := by
  obtain ⟨e⟩ := h
  apply inspection_of_not_dvd_card
  intro hd
  have hfive : 5 ∣ Nat.card S := (by decide : 5 ∣ 2520).trans hd
  rw [Nat.card_congr e.toEquiv] at hfive
  have hfull := hfive.trans (commutator (Atlas.G2.Model (ZMod 2))).card_subgroup_dvd_card
  rw [Atlas.G2.card_Model] at hfull
  norm_num at hfull

private theorem tits_card [IsSimpleGroup S] (e : S ≃* Tits.ParrottGroup) :
    Nat.card S = 17971200 := by
  let f := Tits.parrottFiniteImageMap.comp e.toMonoidHom
  have hf : Function.Surjective f := Tits.parrottFiniteImageMap_surjective.comp e.surjective
  have hi : Function.Injective f := by
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hk | hk
    · exact (MonoidHom.ker_eq_bot_iff f).mp hk
    · have hfone : f = 1 := MonoidHom.ker_eq_top_iff.mp hk
      have ht : (⊤ : Subgroup Tits.Atlas1600Group) = ⊥ := by
        rw [← MonoidHom.range_eq_top.mpr hf, hfone]
        simp
      have hc : Nat.card Tits.Atlas1600Group = 1 := by
        rw [← Nat.card_congr (Subgroup.topEquiv :
          (⊤ : Subgroup Tits.Atlas1600Group) ≃* Tits.Atlas1600Group).toEquiv, ht]
        simp
      rw [Tits.atlas1600Group_card] at hc
      omega
  exact (Nat.card_congr (MulEquiv.ofBijective f ⟨hi, hf⟩).toEquiv).trans
    Tits.atlas1600Group_card

/-- The Tits branch uses inherited simplicity and the certified finite image. -/
theorem tits [IsSimpleGroup S] (h : Nonempty (S ≃* Tits.ParrottGroup)) :
    SevenActionInspection S := by
  obtain ⟨e⟩ := h
  apply inspection_of_not_dvd_card
  rw [tits_card e]
  decide

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie
