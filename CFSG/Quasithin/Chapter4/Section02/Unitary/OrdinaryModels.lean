module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.OrdinaryQuotient
public import CFSG.Quasithin.Chapter4.Section02.Unitary.OrdinaryLocal
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.SourceA5Normality
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.OrderBound

/-!
# Five remaining ordinary central quotients for the unitary source

Apply the proved Theorem C catalogue to the actual ordinary component.
The two-local rank bounds exclude the infinite rows; order divisibility
excludes the alternating and binary linear rows, the smaller Mathieu groups
and HS. The strict order bound excludes the binary derived G₂ quotient.
Only the actual M₂₄, J₂, J₄, He and Ru carriers remain, each with its central
quotient equivalence. This is a reduction toward the source Rudvalis case,
not an assertion that the remaining local geometries have been recognized.

Source: Aschbacher–Smith C.3.1,C.4.8, pp.149–154, and 4.2.12–13, pp.610–612.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open ChapterA.Section02 ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}
local notation "D" => commutator (Atlas.G2.Model (ZMod 2))

theorem no_unitary_ordinary_alternating
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K)
    {n : ℕ} (hn : n ≤ 8) (e : K ⧸ center K ≃* alternatingGroup (Fin n)) : False := by
  have hd := h.unitary_ordinary_order_dvd a K hK
  rw [Nat.card_congr e.toEquiv] at hd
  have hf := hd.trans (alternatingGroup (Fin n)).card_subgroup_dvd_card
  rw [Nat.card_perm,Nat.card_fin] at hf
  exact (by decide : ¬ 6048 ∣ Nat.factorial 8) (hf.trans (Nat.factorial_dvd_factorial hn))

theorem no_unitary_ordinary_linear_binary
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K)
    {n : ℕ} (hn : n = 4 ∨ n = 5) (hm : ClassicalGroup.IsPSL (K ⧸ center K) n 2) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hd := h.unitary_ordinary_order_dvd a K hK
  rw [Nat.card_congr e.toEquiv] at hd
  rcases hn with rfl | rfl
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    norm_num [hF,Fin.prod_univ_succ] at hc
    rw [hc] at hd
    norm_num at hd
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
    norm_num [hF,Fin.prod_univ_succ] at hc
    rw [hc] at hd
    norm_num at hd

theorem no_unitary_ordinary_small_sporadic
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K)
    (n : SporadicName) (hn : n = .m11 ∨ n = .m12 ∨ n = .m22 ∨ n = .m23 ∨ n = .hs)
    (e : K ⧸ center K ≃* n.Carrier) : False := by
  have hd := h.unitary_ordinary_order_dvd a K hK
  rw [Nat.card_congr e.toEquiv] at hd
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · change 6048 ∣ Nat.card Sporadic.Mathieu.M11 at hd
    rw [Sporadic.Mathieu.m11_order] at hd
    norm_num at hd
  · change 6048 ∣ Nat.card Sporadic.Mathieu.M12 at hd
    rw [Sporadic.Mathieu.m12_order] at hd
    norm_num at hd
  · change 6048 ∣ Nat.card Sporadic.Mathieu.M22 at hd
    rw [Sporadic.Mathieu.m22_order] at hd
    norm_num at hd
  · change 6048 ∣ Nat.card Sporadic.Mathieu.M23 at hd
    rw [Sporadic.Mathieu.m23_order] at hd
    norm_num at hd
  · exact (by decide : ¬ 6048 ∣ 2 ^ 9 * 3 ^ 2 * 5 ^ 3 * 7 * 11)
      (hd.trans Sporadic.LeechRelated.HS.card_carrier_dvd)

/-- Every ordinary component is one of five actual sporadic central quotients.
The model equivalence is retained; this does not yet recognize the Rudvalis row. -/
theorem unitary_ordinary_five_sporadic_models
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K) :
    ∃ n : SporadicName, (n = .m24 ∨ n = .j2 ∨ n = .j4 ∨ n = .he ∨ n = .ru) ∧
      Nonempty (K ⧸ center K ≃* n.Carrier) := by
  let := hK.2
  have hm := Chapter1.QuasisimpleInvolutions.quotient_model (h.sqtk.subgroup K)
    theoremA_knownSimple theoremC_knownSimple
  cases hm with
  | alternating n hn e => exact (h.no_unitary_ordinary_alternating a K hK hn e.some).elim
  | odd hm => exact (h.no_ordinary_component_of_theoremC_odd_model K hK hm).elim
  | bender hm =>
    cases hm with
    | linear f hf hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      exact (h.no_ordinary_component_sl2_central_quotient K hK
        (e.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm)).elim
    | unitary f hf hm => exact (h.no_ordinary_component_binary_unitary_three K hK hf hm).elim
    | suzuki m hm e => exact (h.no_ordinary_component_suzuki_central_quotient K hK hm e.some).elim
  | rank_two f hm =>
    exfalso
    cases hm with
    | linear hf hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      exact h.no_unitary_ordinary_psl3 a K hK e
    | symplectic hf hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      exact h.no_unitary_ordinary_sp4 a K hK
        (e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm)
    | g2 hf hm =>
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      apply h.no_unitary_ordinary_g2 a K hK e
      rw [hF]
      exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hf)
    | triality hf hm => exact h.no_unitary_ordinary_triality a K hK hf hm
    | ree_f4 m hm hf e => exact h.no_unitary_ordinary_ree a K hK hm e.some
    | symplectic_derived hf e =>
      exact h.no_unitary_ordinary_alternating a K hK (by decide : 6 ≤ 8)
        (e.some.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)
    | g2_derived hf e =>
      have hc := h.unitary_ordinary_order_gt a K hK
      rw [Nat.card_congr e.some.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hc
      omega
    | tits hf e =>
      have hd := h.unitary_ordinary_order_dvd a K hK
      rw [Nat.card_congr e.some.toEquiv,Tits.parrottGroup_card] at hd
      norm_num at hd
  | linear_binary n hn hm => exact (h.no_unitary_ordinary_linear_binary a K hK hn hm).elim
  | sporadic hm =>
    rcases hm with ⟨n,hn,⟨e⟩⟩ | ⟨e⟩
    · cases n with
      | m11 => exact (h.no_unitary_ordinary_small_sporadic a K hK _ (by simp) e).elim
      | m12 => exact (h.no_unitary_ordinary_small_sporadic a K hK _ (by simp) e).elim
      | m22 => exact (h.no_unitary_ordinary_small_sporadic a K hK _ (by simp) e).elim
      | m23 => exact (h.no_unitary_ordinary_small_sporadic a K hK _ (by simp) e).elim
      | hs => exact (h.no_unitary_ordinary_small_sporadic a K hK _ (by simp) e).elim
      | j3 => exact (hn rfl).elim
      | m24 => exact ⟨.m24,by simp,⟨e⟩⟩
      | j2 => exact ⟨.j2,by simp,⟨e⟩⟩
      | j4 => exact ⟨.j4,by simp,⟨e⟩⟩
      | he => exact ⟨.he,by simp,⟨e⟩⟩
      | ru => exact ⟨.ru,by simp,⟨e⟩⟩
    · exact (h.no_ordinary_component_janko_central_quotient K hK e.some).elim
end CFSG.Quasithin.ChapterC.HypothesisC28
