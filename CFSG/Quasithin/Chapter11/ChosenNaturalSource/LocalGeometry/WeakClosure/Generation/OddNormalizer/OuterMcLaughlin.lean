module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterJankoThree
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.McL.ThreeRank.Elements

/-!
# Excluding the actual McL component cover in both actions

The word a b a b³ a b² in the native ATLAS degree-275 generators has
order eight. Lean checks its eighth power and a moved point of its fourth
power directly. Its square places a cyclic four-group in the Frattini
subgroup of a Sylow two-group. The certified McL order bounds that Sylow
subgroup by 128, hence its Frattini quotient by 32. The PSL₃(4) section
obstruction excludes the original outer action, retaining the full cover.
The placed action was already incompatible with McL's two-part.

Source consumes this exclusion on the original selected component and
literal Hall kernel. The other outer rows and moved J₄ remain with
qt-d-1222-natural-odd-kernel-normalizer; final 11.2.1 assembly remains with
qt-d-1222-natural-weak-closure-source.
Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622, using I.3.1;
ATLAS McLG1-p275B0, with the unchanged left-action generator convention
and kernel-checked generator tables from McL.ThreeRank.Elements.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
open Sporadic.LeechRelated.McL

private def mclEight : Carrier :=
  ThreeRank.a * ThreeRank.b * (ThreeRank.a * ThreeRank.b ^ 3) *
    (ThreeRank.a * ThreeRank.b ^ 2)

private theorem mclEight_order : orderOf mclEight = 8 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 2)
  · intro h
    have hh := congrArg (fun x : Carrier => x.val 0) h
    exact (by decide +kernel : (mclEight ^ 4).val 0 ≠ (1 : Carrier).val 0) hh
  · apply Subtype.ext
    apply Equiv.ext
    apply ThreeRank.allFin
    decide +kernel

/-- The native degree-275 word gives every McL Sylow subgroup a Frattini
subgroup of order at least four, hence a quotient of order at most 32. -/
theorem mcl_frattini_card_le_thirtytwo {Q : Type*} [Group Q] [Finite Q]
    (e : Q ≃* Carrier) (P : Sylow 2 Q) :
    Nat.card (P ⧸ frattini P) ≤ 32 := by
  have hcyc : IsPGroup 2 (zpowers mclEight) := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_zpowers, mclEight_order]
    norm_num)
  obtain ⟨U,hU⟩ := hcyc.exists_le_sylow
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let a : P ≃* P' := e.subgroupMap (P : Subgroup Q)
  rw [SylowFrattiniBounds.card_congr a, SylowFrattiniBounds.card_congr (P'.equiv U)]
  let z : U := ⟨mclEight,hU (mem_zpowers _)⟩
  have hz : orderOf z = 8 := by
    rw [←orderOf_injective (U : Subgroup Carrier).subtype Subtype.val_injective z]
    exact mclEight_order
  let : Fact (IsPGroup 2 U) := ⟨U.isPGroup'⟩
  have hsq : zpowers (z ^ 2) ≤ frattini U :=
    zpowers_le.mpr (pth_power_mem_frattini_of_isPGroup (p := 2) z)
  have hfour : 4 ≤ Nat.card (frattini U) := by
    have hc : Nat.card (zpowers (z ^ 2)) = 4 := by
      rw [Nat.card_zpowers,orderOf_pow,hz]
      norm_num
    exact hc ▸ card_le_of_le hsq
  have hcard : Nat.card U ≤ 128 := by
    obtain ⟨k,hk⟩ := U.isPGroup'.exists_card_eq
    have hd := (U : Subgroup Carrier).card_subgroup_dvd_card
    rw [hk,Nat.card_congr Theory.SpecificGroups.McLaughlin.Multiplier.permutationModelEquiv.toEquiv,
      Atlas.Sporadic.McLaughlin.card] at hd
    have hk7 : k ≤ 7 := by
      by_contra! h
      have hd' : 2 ^ 8 ∣ Atlas.Sporadic.McLaughlin.order :=
        (pow_dvd_pow 2 (by omega : 8 ≤ k)).trans hd
      norm_num [Atlas.Sporadic.McLaughlin.order] at hd'
    rw [hk]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hk7
  have hprod := card_eq_card_quotient_mul_card_subgroup (frattini U)
  nlinarith

open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

/-- The actual McL component cover cannot carry the original simple outer section. -/
theorem moved_outer_not_mcl {A : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (ho : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f)
    (e : (K ⧸ center K) ≃* Carrier) : False := by
  let P : Sylow 2 (K ⧸ center K) := default
  exact moved_outer_not_of_frattini_le_thirtytwo D S K hK ho
    (.sporadic (Or.inr (Or.inr ⟨e⟩))) P (mcl_frattini_card_le_thirtytwo e P)

open Chapter4 Chapter4.Section04
/-- McL is excluded on the same original moved component, in both actions. -/
theorem moved_component_not_mcl {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (V : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    (e : (K ⧸ center K) ≃* Carrier) : False := by
  rcases moved_component_inner_or_outer_section D S hA hodd K hK with hi | ho
  · obtain ⟨_,_,_,_,_,_,hdiv⟩ :=
      moved_component_placement_of_inner D S hA hodd hu hout K hK houtK hi
    rw [Nat.card_congr e.toEquiv,
      Nat.card_congr Theory.SpecificGroups.McLaughlin.Multiplier.permutationModelEquiv.toEquiv,
      Atlas.Sporadic.McLaughlin.card] at hdiv
    norm_num [Atlas.Sporadic.McLaughlin.order] at hdiv
  · exact moved_outer_not_mcl D S K hK ho e

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
