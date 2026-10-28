module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six.Ordinary
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six.OddTernary
public import CFSG.Quasithin.MainConverse.SporadicLocal.HS.EvenLocalCover
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.LargeNormalizerThreePart
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.EvenLocalCandidates.CentralNormalizerThreePart
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.TwoLocalOrder

/-!
# The remaining sporadic order-32 A₆ containing cases

The normalizer of the embedded two-core contains both the local component
and its full normalizing Sylow subgroup. The genuine HS and Ru two-local
catalogues make such a normalizer's order indivisible by nine, whereas the
A₆ quotient forces divisibility by nine. Together with the ordinary-carrier
sieve and the odd ternary exclusion, this leaves M₂₄, J₄ and He explicitly.

The final theorem retains the original SQTK ambient group, its given Sylow,
its local component and its containing component. It makes no remaining
local-classification assumption. Source: Aschbacher–Smith A.3.12, pp.47–48;
GLS3 Tables 5.3m and 5.3r for the two sporadic catalogues.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six
open Chapter1.Section02.LocalModels ClassificationModels

private theorem all_local_bounds {H : Type*} [Group H] [Finite H]
    (T : Sylow 2 H)
    (ht : ∀ N : Subgroup H, IsMaximalTwoLocal N → (T : Subgroup H) ≤ N →
      ¬ 9 ∣ Nat.card N)
    (S : Sylow 2 H) (N : Subgroup H) (hN : IsMaximalTwoLocal N)
    (hSN : (S : Subgroup H) ≤ N) : ¬ 9 ∣ Nat.card N := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq H S T
  have hm := (Theory.Quasithin.maximalTwoLocal_overgroup_conj_iff g S N).mpr ⟨hN,hSN⟩
  rw [hg] at hm
  have hh := ht _ hm.1 hm.2
  rwa [card_map_of_injective (MulAut.conj g).injective] at hh

private theorem not_section_of_local_bounds {G H : Type*} [Group G] [Finite G]
    [Group H] [Finite H] (e : G ≃* H)
    (hb : ∀ (T : Sylow 2 H) (N : Subgroup H), IsMaximalTwoLocal N →
      (T : Subgroup H) ≤ N → ¬ 9 ∣ Nat.card N)
    (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) : False := by
  have hne : pCore 2 B ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hcore
    omega
  let U := (pCore 2 B).map B.subtype
  have hU : U ≠ ⊥ := fun he => hne
    ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  have hloc : IsTwoLocal (normalizer (U : Set G)) :=
    ⟨U,hU,pCore_isPGroup.map B.subtype,rfl⟩
  have hnorm := normalizer_le_normalizer_characteristic_image B (pCore 2 B)
  have hBN : B ≤ normalizer (U : Set G) := B.le_normalizer.trans hnorm
  have hSN : (S : Subgroup G) ≤ normalizer (U : Set G) := hn.trans hnorm
  obtain ⟨N,hNN,hN⟩ := Finite.exists_le_maximal hloc
  have hd : 9 ∣ Nat.card N :=
    ((card_of_shape hcore hA6).symm ▸ (by decide : 9 ∣ 11520)).trans
      (card_dvd_of_le (hBN.trans hNN))
  have hnm := hb (S.mapSurjective e.surjective) (N.map e.toMonoidHom)
    (Theory.Quasithin.isMaximalTwoLocal_map e hN)
    (show (S : Subgroup G).map e.toMonoidHom ≤ N.map e.toMonoidHom from
      map_mono (hSN.trans hNN))
  rw [card_map_of_injective e.injective] at hnm
  exact hnm hd

private theorem higmanSims_local_bound
    (S : Sylow 2 Sporadic.LeechRelated.HS.Carrier)
    (N : Subgroup Sporadic.LeechRelated.HS.Carrier)
    (hN : IsMaximalTwoLocal N) (hSN : (S : Subgroup _) ≤ N) :
    ¬ 9 ∣ Nat.card N := by
  open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates in
  obtain ⟨T,_,_,_,_,hcover⟩ :=
    MainConverse.SporadicLocal.HSEvenLocalCover.exists_normal_local_cover_of_card_dvd
      card_carrier_dvd
  apply all_local_bounds T _ S N hN hSN
  intro M hM hTM hd
  obtain ⟨i,⟨e⟩⟩ := hcover M hM hTM
  have h9 : 9 ∣ Nat.card (Sporadic.LeechRelated.HS.EvenLocalCandidates.localGroup i) :=
    (Nat.card_congr e.toEquiv) ▸ hd
  by_cases hi : i = 0
  · subst i
    exact Sporadic.LeechRelated.HS.EvenLocalCandidates.central_localGroup_nine_not_dvd h9
  · exact Sporadic.LeechRelated.HS.EvenLocalCandidates.large_localGroup_nine_not_dvd i hi h9

/-- The original full-Sylow order-32 A₆ section is excluded in HS. -/
theorem not_higmanSims {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)))
    (e : G ≃* Sporadic.LeechRelated.HS.Carrier) : False :=
  not_section_of_local_bounds e higmanSims_local_bound S B hn hcore hA6

/-- The original full-Sylow order-32 A₆ section is excluded in Ru. -/
theorem not_rudvalis {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)))
    (e : G ≃* Rudvalis.Model) : False := by
  apply not_section_of_local_bounds e _ S B hn hcore hA6
  intro T N hN hTN hd
  exact Rudvalis.SylowOvergroups.not_nine_dvd_card_twoLocal T N hN.1 hTN hd

/-- Under the actual core-free SQTK hypotheses, only the three indicated
sporadic ordinary carriers remain for a proper containing component. -/
theorem remaining_sporadic {G : Type*} [Group G] [Finite G]
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B < K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) :
    ∃ name : SporadicName, (name = .m24 ∨ name = .j4 ∨ name = .he) ∧
      Nonempty (K ≃* name.Carrier) := by
  have hm := ordinary_models_remaining hG hO T hB hK hBK hTB hcore hA6
  obtain ⟨S,_,hl,hn,_,hc,ha⟩ := source_sylow_restriction T hB hK hBK hTB hcore hA6
  rcases hm with ⟨p,unitary,hp,ho,hm⟩ | ⟨name,hnames,he⟩
  · exact (not_odd_ternary S (B.subgroupOf K) hl hn hc ha hp ho unitary hm).elim
  · rcases hnames with rfl | rfl | rfl | rfl | rfl
    · exact ⟨.m24,Or.inl rfl,he⟩
    · exact ⟨.j4,Or.inr (Or.inl rfl),he⟩
    · exact (not_higmanSims S (B.subgroupOf K) hn hc ha he.some).elim
    · exact ⟨.he,Or.inr (Or.inr rfl),he⟩
    · exact (not_rudvalis S (B.subgroupOf K) hn hc ha he.some).elim

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six
