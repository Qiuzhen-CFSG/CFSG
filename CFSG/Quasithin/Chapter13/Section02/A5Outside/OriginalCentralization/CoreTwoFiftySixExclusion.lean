module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.CoreFiveOrbit
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.CoreMarkedQuotient
public import Theory.Representation.BinaryPermutation.FiveOrbitMarkedQuotient

/-!
# Excluding the original commuting pair through core order256

The actual central quotient has a five-point orbit. Its resulting
permutation coordinates are aligned with the original A5 quotient map.
The alternating commutator pairing then makes the whole original core
commutative. It would lie in the opposite core, contradicting the original
incomparability. Thus both cores in a surviving commuting pair have order
at least512. No action classifier, extension splitting, or residual lift is
assumed. Larger original cores remain a separate source duty.

Source application: Aschbacher--Smith 13.2.8(1), printed p.880.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

/-- The original commuting pair has no core of order at most256. -/
theorem original_commuting_pair_core_card_gt_twoFiftySix
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hd : Function.Surjective d.localActor)
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 H)
    (he : ∀ h : H, ∀ w : BinaryPermutation.core (Fin 5),
      h.val * e.flag.module.map (Multiplicative.ofAdd w) * h.val⁻¹ =
        e.flag.module.map (Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 5) (q h) w)))
    (hVW : V ≤ centralizer (W : Set G)) :
    256 < Nat.card (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) := by
  by_contra! hsmall
  obtain ⟨hV,ρ,hρ,hA,hAe,hker,hfive,a,ha,horbit⟩ :=
    original_commuting_pair_core_five_orbit d e hjoin hH hd q hq hk he hVW hsmall
  let := hV
  let := hAe
  obtain ⟨c,hc⟩ := BinaryPermutation.core_marking_of_five_orbit_and_prescribed_quotient
    ρ d.flag.module.action d.flag.module.onto (hker.trans d.flag.action_kernel.symm)
    hA hfive a ha horbit
  let := d.core_commutative_of_marked_quotient hV ρ hρ c hc
  let J := L ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  let : IsMulCommutative Q := Subgroup.map_isMulCommutative
    (H := pCore 2 J) (f := J.subtype)
  have hQT : Q ≤ (T : Subgroup G) :=
    (d.sylow_centralizer d.normalizes_L).ge.trans inf_le_left
  have hWQ : W ≤ Q := by
    rw [show Q = (T : Subgroup G) ⊓ centralizer (V : Set G) from
      (d.sylow_centralizer d.normalizes_L).symm]
    exact le_inf e.chosen.le_sylow (le_centralizer_iff.mp hVW)
  apply (original_pair_cores_incomparable d hH hd q hq hk).2
  rw [←hjoin,←e.sylow_centralizer e.normalizes_L]
  exact le_inf hQT ((le_centralizer Q).trans (centralizer_le hWQ))

/-- Both literal cores in the remaining original commuting pair have order
at least512. The equality of their original orders is retained. -/
theorem original_commuting_pair_core_cards_ge_fiveTwelve
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hd : Function.Surjective d.localActor)
    (q : H →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 H)
    (he : ∀ h : H, ∀ w : BinaryPermutation.core (Fin 5),
      h.val * e.flag.module.map (Multiplicative.ofAdd w) * h.val⁻¹ =
        e.flag.module.map (Multiplicative.ofAdd
          (BinaryPermutation.coreRepresentation (Fin 5) (q h) w)))
    (hVW : V ≤ centralizer (W : Set G)) :
    512 ≤ Nat.card (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) ∧
      512 ≤ Nat.card (pCore 2 H) := by
  have hlarge := original_commuting_pair_core_card_gt_twoFiftySix
    d e hjoin hH hd q hq hk he hVW
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2)
    (G := (L ⊔ (T : Subgroup G) : Subgroup G))).exists_card_eq
  have hnine : 9 ≤ n := by
    by_contra! hnsmall
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show n ≤ 8 by omega)
    rw [←hn] at hh
    norm_num at hh
    omega
  have hfirst : 512 ≤ Nat.card (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) := by
    rw [hn]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hnine
  have heq := original_pair_core_cards d hH.1.1.2 hd q hq hk
  rw [pCoreIn,pCoreIn,card_map_of_injective H.subtype_injective,
    card_map_of_injective (L ⊔ (T : Subgroup G)).subtype_injective] at heq
  exact ⟨hfirst,heq.symm ▸ hfirst⟩

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
