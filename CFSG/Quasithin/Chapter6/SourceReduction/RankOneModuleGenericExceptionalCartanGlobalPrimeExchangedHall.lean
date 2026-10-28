module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalExchangedHall
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeSylowAlternating

/-!
# Applying the exchanged Hall plane to escaping prime actors

The genuine exchanged PSL₂(4) source row constructs the prescribed right
Hall subgroup B as E₉. A cubic escaping actor centralizes B and joins it
to E₂₇ in N_G(L), contrary to quasithinness. Thus the actor is quintic.
The smaller-Sylow alternating containing models force a cubic actor and
are excluded, retaining the literal generated group and its normal component.
The selected right factor R is not identified with the source H-component C.
The intrinsic A₅ quotient also constructs the Hall plane without an
independent field marking, and local control gives the desired residual
normalization when the original left field degree is two.

Source: Aschbacher–Smith 5.2.2, printed pp.648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- The original prescribed B, rather than a newly selected complement, is E₉ in the exchanged four-field row. -/
theorem CartanPair.right_cubic_plane_of_exchanged_four {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (_hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4)
    (hm : ModelBorelPair ((normalizer (L : Set G)).subgroupOf H) C
      (BenderSuzuki.Converse.PBorel F)) : IsElementaryAbelian 3 B ∧ Nat.card B = 9 := by
  let M := (normalizer (L : Set G)).subgroupOf H
  let eM : M ≃* (normalizer (L : Set G) ⊓ H : Subgroup G) :=
    (M.equivMapOfInjective H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr (subgroupOf_map_subtype _ _))
  let Y := (B.subgroupOf (normalizer (L : Set G) ⊓ H)).map eM.symm.toMonoidHom
  have hY : IsHallSubgroup OddHall.oddPrimes Y :=
    ⟨fun p hp => c.right_hall.p_in_pi_of_p_dvd_card p
        (hp.trans (card_map_dvd _ eM.symm.toMonoidHom)),
      fun p hp => c.right_hall.p_in_pi_of_p_dvd_index p
        (hp.trans (index_map_dvd _ eM.symm.surjective))⟩
  have hr : primeRank 3 M ≤ 2 := by
    rw [primeRank_equiv 3 eM]
    exact (primeRank_mono 3 inf_le_left).trans
      (isQuasithin_iff_twoLocal.mp h.qtke.quasithin
        (normalizer (L : Set G)) h.maximal.1 3 (by decide) (by decide))
  obtain ⟨he,hcard⟩ := ExchangedCartan.hall_plane_of_linear_four hC hqs hc
    (comap_mono h.sylow_normalizes) T.isPGroup'.comap_subtype hr hF hm Y hY
  let := he
  let eB : B ≃* Y := (subgroupOfEquivOfLe c.right_le).symm.trans
    (eM.symm.subgroupMap (B.subgroupOf (normalizer (L : Set G) ⊓ H)))
  exact ⟨IsElementaryAbelian.of_injective eB.toMonoidHom eB.injective,
    (Nat.card_congr eB.toEquiv).trans hcard⟩

/-- The literal exchanged E₉ excludes cubic escaping actors by the source E₂₇ contradiction. -/
theorem CartanPair.exchanged_four_actor_prime {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hd : CartanPrimeActor A H p D)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4)
    (hm : ModelBorelPair ((normalizer (L : Set G)).subgroupOf H) C
      (BenderSuzuki.Converse.PBorel F)) : p = 5 := by
  rcases hd.prime with hp | hp
  · subst p
    obtain ⟨hB,hBc⟩ := c.right_cubic_plane_of_exchanged_four h hH hC hqs hc hF hm
    exact (h.prime_actor_excluded_of_cubic_plane c hd hB hBc
      ((c.right_le.trans inf_le_right).trans (le_normalizer_residual H))
      (h.prime_actor_not_normalizes hH hd)).elim
  · exact hp

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- The original exchanged four-field row excludes the two alternating containers,
including when the selected right factor is in a parabolic. -/
theorem LocalData.exchanged_four_not_alternating_container
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4)
    (hm : ModelBorelPair ((normalizer (L : Set G)).subgroupOf H) C
      (BenderSuzuki.Converse.PBorel F))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R))
    (hRK : R ≤ K) (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hKn : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).Normal) :
    ¬ (Chapter1.Section02.LocalModels.IsAlternating (K ⧸ pCore 2 K) 7 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (K ⧸ pCore 2 K) 7) := by
  intro hmK
  have hp := c.exchanged_four_actor_prime h hd hH hC hqs hc hF hm
  have hthree := d.source_overcomponent_alternating_seven_prime h hH c hd hz
    hSyl hRK hKX hK hKn hmK
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- The intrinsic A₅ quotient of the actual exchanged component constructs B = E₉. -/
theorem CartanPair.right_cubic_plane_of_exchanged_A5 {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n f : ℕ}
    (c : CartanPair T L H A B) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    (hm : ExchangedModel ((normalizer (L : Set G)).subgroupOf H) C f)
    (hA5 : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4) :
    IsElementaryAbelian 3 B ∧ Nat.card B = 9 := by
  obtain ⟨F,_,_,_,hF,hb⟩ := ExchangedCartan.linear_four_marking_of_A5 hC hc hm hA5
  exact c.right_cubic_plane_of_exchanged_four h hH hC hqs hc hF hb

/-- The original degree-two Cartan normalizes the residual in the exchanged A₅ source row. -/
theorem Input.cartan_normalizes_of_exchanged_A5_degree_two {κ : GroupClass}
    {T : Sylow 2 G} {L W H A B : Subgroup G} {f : ℕ}
    (h : Input κ T L W 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : ExchangedClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H))
    (hm : ExchangedModel ((normalizer (L : Set G)).subgroupOf H) C f)
    (hA5 : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4) :
    A ≤ normalizer (residual H : Set G) := by
  obtain ⟨F,_,_,_,hF,hb⟩ := ExchangedCartan.linear_four_marking_of_A5 hC hc hm hA5
  exact h.cartan_normalizes_of_exchanged_linear_small_degree hH c hcontrol
    (Or.inl rfl) (dvd_refl 2) hC hqs hc (f := 2) hF hb

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
