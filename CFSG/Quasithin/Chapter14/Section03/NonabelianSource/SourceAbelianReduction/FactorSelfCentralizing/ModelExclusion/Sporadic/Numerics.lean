module
public import CFSG.Quasithin.ClassificationModels.Families
public import Theory.Mathieu.M11.Properties.ThreeInvolutions
public import Theory.Mathieu.SmallModuleRanks.M12
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerTransport
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoCentral
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.InvolutionCentralizerOdd
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Placement
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.Classes
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoA.FiniteStructure
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.TwoB
public import Theory.SpecificGroups.Rudvalis.Model.InvolutionCentralizers.ThreePart

/-!
# Numerical exclusions for the sporadic marked models

The elementary sixteen excludes M₁₁ and M₁₂. The marked centralizers in
M₂₃, M₂₄, J₄, HS, He and Ru are larger than 2304; the J₂ centralizers
have order divisible by five. These statements use the existing intrinsic
carriers and their proved centralizer and rank results. M₂₂ remains:
its centralizer has order 384, so this numerical argument does not exclude it.

Source: Aschbacher--Smith, final paragraph of 14.3.20, printed p.998,
and the sporadic model list in 1.1.5(3)(f), p.502.
-/

public section
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing.Sporadic
open ClassificationModels Sporadic.Mathieu

private theorem j2_five (t : _root_.Sporadic.LeechRelated.J2.Carrier) (ht : orderOf t = 2) :
    5 ∣ Nat.card (centralizer ({t} : Set _)) := by
  open _root_.Sporadic.LeechRelated.J2 in
  rcases InnerInvolutionCores.involution_fusion t ht with h | h
  · rw [← card_centralizer_eq_of_isConj _ _ h,
      Nat.card_congr InnerInvolutionCores.a_centralizer_equiv.toEquiv,
      Nat.card_prod, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [InnerInvolutionCores.E4, InnerInvolutionCores.C2, Nat.card_fun, Nat.factorial]
  · rw [← card_centralizer_eq_of_isConj _ _ h]
    change 5 ∣ Nat.card _root_.Sporadic.LeechRelated.J2.ExceptionalParabolics.Seed.l₁
    rw [_root_.Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_l₁]
    decide

private theorem j4_large (t : Janko4.Model) (ht : orderOf t = 2) :
    2304 < Nat.card (centralizer ({t} : Set _)) := by
  rcases Janko4.InvolutionCentralizers.centralizer_equiv_first_or_second t ht with he | he
  · obtain ⟨e⟩ := he
    have hc := (pCore 2 Janko4.InvolutionCentralizers.First.centralizer).card_le_card_group
    rw [Janko4.InvolutionCentralizers.First.centralizer_twoCore_card] at hc
    rw [Nat.card_congr e.toEquiv]
    omega
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, Janko4.InvolutionCentralizers.Second.ambient_card]
    decide

attribute [local irreducible] Held.TwoLocalCandidates.max5First

private theorem held_large (t : Held.He) (ht : orderOf t = 2) :
    2304 < Nat.card (centralizer ({t} : Set _)) := by
  rcases Held.InvolutionFixedData.Coverage.innerInvolutionCoverage t ht with ⟨c, hc⟩ | ⟨c, hc⟩
  · rw [← card_centralizer_eq_of_isConj _ _ (isConj_iff.mpr ⟨c, hc⟩),
      ← MulAut.fixedSubgroup_conj]
    change 2304 < Nat.card Held.InvolutionFixedData.TwoA.centralizer
    rw [Held.InvolutionFixedData.TwoA.FiniteStructure.centralizer_card]
    decide
  · rw [← card_centralizer_eq_of_isConj _ _ (isConj_iff.mpr ⟨c, hc⟩),
      ← MulAut.fixedSubgroup_conj, Held.InvolutionFixedData.twoB_fixedSubgroup_card]
    decide

private theorem m23_large (t : M23) (ht : orderOf t = 2) :
    2304 < Nat.card (centralizer ({t} : Set M23)) := by
  obtain ⟨e⟩ := M23Geometry.InvolutionCentralizer.centralizer_equiv_representative ht
  rw [Nat.card_congr e.toEquiv, M23Geometry.involutionRepresentative_centralizer_card]
  decide

private theorem m24_large (t : M24) (ht : orderOf t = 2) (hc : TwoCentral t) :
    2304 < Nat.card (centralizer ({t} : Set M24)) := by
  rw [M24InvolutionCentralizers.card_centralizer_of_twoCentral t ht hc]
  decide

private theorem hs_large (t : _root_.Sporadic.LeechRelated.HS.Carrier)
    (ht : orderOf t = 2) (hc : TwoCentral t) :
    2304 < Nat.card (centralizer ({t} : Set _)) := by
  have he := (ChapterI.Section02.ExceptionalCovers.HSLocal.twoCentral_iff_isConj_e0 t ht).mp hc
  rw [← card_centralizer_eq_of_isConj _ _ he,
    Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.centralizer_card]
  decide

/-- The elementary sixteen and the order of its marked centralizer leave only
M₂₂ among the actual sporadic carriers. The kernel and subnormality needed to
exclude that row are handled separately. -/
theorem name_eq_m22_of_rank_and_centralizer
    (name : SporadicName) (hne : name ≠ .j3) (hr : 4 ≤ primeRank 2 name.Carrier)
    (t : name.Carrier) (ht : orderOf t = 2) (hc : TwoCentral t)
    (hd : Nat.card (centralizer ({t} : Set name.Carrier)) ∣ 2304) : name = .m22 := by
  have hb := Nat.le_of_dvd (by decide : 0 < 2304) hd
  cases name with
  | m11 =>
      have hh := (primeRank_le_of_injective 2 MulAut.conj
        (MulAut.conj_injective_of_center_eq_bot m11_center_eq_bot)).trans
          m11_automorphism_twoRank_le_two
      change 4 ≤ primeRank 2 M11 at hr
      omega
  | m12 =>
      change 4 ≤ primeRank 2 M12 at hr
      have hh := m12_twoRank_le_three
      omega
  | m22 => rfl
  | m23 => exact (not_lt_of_ge hb (m23_large t ht)).elim
  | m24 => exact (not_lt_of_ge hb (m24_large t ht hc)).elim
  | j2 =>
      have hh := (j2_five t ht).trans hd
      norm_num at hh
  | j3 => exact (hne rfl).elim
  | j4 => exact (not_lt_of_ge hb (j4_large t ht)).elim
  | hs => exact (not_lt_of_ge hb (hs_large t ht hc)).elim
  | he => exact (not_lt_of_ge hb (held_large t ht)).elim
  | ru =>
      change Nat.card (Rudvalis.InvolutionCentralizers.Centralizer t) ≤ 2304 at hb
      rcases Rudvalis.InvolutionCentralizers.centralizer_representatives t ht with ⟨h, _⟩ | ⟨h, _⟩
      · rw [Rudvalis.InvolutionCentralizers.first_centralizer_card h] at hb
        omega
      · rw [Rudvalis.InvolutionCentralizers.second_class_centralizer_card h] at hb
        omega

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.SelfCentralizing.Sporadic
