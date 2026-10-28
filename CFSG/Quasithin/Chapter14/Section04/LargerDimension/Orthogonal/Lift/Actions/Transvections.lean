module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.Centralizers
public import Theory.ElementaryAbelian.ExtraspecialCentralFunctionals

/-!
# The full central-functional action on the orthogonal lift base

For A = [U,i]⟨z⟩ and Z = ⟨z⟩, the actual commutator map identifies U/A
with Hom(A/Z,Z). Its associated automorphism sends a to a f(aZ), using
the literal inclusion Z ≤ A. Every such automorphism is conjugation by
an element of U. In particular this is the full group of transvections
with center Z on the order-32 elementary base, as asserted in the proof
of Aschbacher–Smith Lemma 14.4.9, printed p.1010.

The reusable calculation takes the established elementary and order facts.
Here extraspeciality supplies centrality and the commutator bound, and
`liftBase_self_centralizer` supplies the exact kernel calculation. The final
consumer constructs the elementary base from the irreducible moved section.
The ordinary left conjugation and the source's inverse convention have the
same action, since every central-functional automorphism is involutory.
-/

@[expose] public section
open Subgroup ExtraspecialCentralFunctionals
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
variable {G : Type*} [Group G] [Finite G]

/-- The literal lift satisfies the hypotheses of central-functional duality. -/
theorem liftBase_centralFunctionalConfiguration
    (U : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hz : orderOf z = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G))
    (hUcard : Nat.card U = 512)
    (hA : IsElementaryAbelian 2 (liftBase U z i))
    (hAcard : Nat.card (liftBase U z i) = 32) :
    Configuration U (liftBase U z i) (zpowers z) := by
  have hzU : zpowers z ≤ U := by rw [← hZ]; exact map_subtype_le _
  refine {
    base_le := sup_le
      (le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hiU)) hzU
    center_le := le_sup_right
    central := ?_
    commutator_le := ?_
    self_centralizing := liftBase_self_centralizer U z i hZ hiU hUcard hA hAcard
    center_card := by rw [Nat.card_zpowers, hz]
    card_eq := by rw [hAcard, hUcard]; norm_num }
  · rw [← hZ]
    rintro _ ⟨a, ha, rfl⟩ u hu
    exact congrArg Subtype.val (mem_center_iff.mp ha (⟨u,hu⟩ : U))
  · have hh := map_mono (f := U.subtype)
      (IsExtraspecial.quotient_elementary_abelian 2 U).commutator_le_center_of_central_quotient
    simpa only [map_subtype_commutator, hZ] using hh

section ElementaryBase
variable (U : Subgroup G) [IsExtraspecial 2 U] (z i : G)
variable (hz : orderOf z = 2)
variable (hZ : (center U).map U.subtype = zpowers z)
variable (hiU : i ∈ normalizer (U : Set G))
variable (hUcard : Nat.card U = 512)
variable [hA : IsElementaryAbelian 2 (liftBase U z i)]
variable [IsElementaryAbelian 2 (zpowers z)]
variable (hAcard : Nat.card (liftBase U z i) = 32)

/-- Commutator duality for the exact source quotients U/A and A/⟨z⟩. -/
noncomputable def liftBaseFunctionalEquiv :
    let c := liftBase_centralFunctionalConfiguration U z i hz hZ hiU hUcard hA hAcard
    let _ := ExtraspecialCentralFunctionals.normal c
    (U ⧸ (liftBase U z i).subgroupOf U) ≃*
      ((liftBase U z i ⧸ (zpowers z).subgroupOf (liftBase U z i)) →* zpowers z) :=
  quotientEquiv (liftBase_centralFunctionalConfiguration U z i hz hZ hiU hUcard hA hAcard)

theorem liftBaseFunctionalEquiv_apply (u : U) (a : liftBase U z i) :
    let c := liftBase_centralFunctionalConfiguration U z i hz hZ hiU hUcard hA hAcard
    let _ := ExtraspecialCentralFunctionals.normal c
    (liftBaseFunctionalEquiv U z i hz hZ hiU hUcard hAcard
      (QuotientGroup.mk' ((liftBase U z i).subgroupOf U) u)
      (QuotientGroup.mk' ((zpowers z).subgroupOf (liftBase U z i)) a) : G) =
      ⁅(u : G),(a : G)⁆ :=
  quotientEquiv_apply _ u a

/-- Kernel, surjectivity and exact image equality for the actual lift action. -/
theorem liftBase_full_transvections :
    let c := liftBase_centralFunctionalConfiguration U z i hz hZ hiU hUcard hA hAcard
    (pairing c).ker = (liftBase U z i).subgroupOf U ∧
    Function.Surjective (pairing c) ∧
    Function.Injective (twists c.center_le) ∧
    (ExtraspecialCentralFunctionals.conjugation c).range = (twists c.center_le).range := by
  exact ⟨pairing_ker _, pairing_surjective _, twists_injective _, conjugation_range _⟩

end ElementaryBase

/-- Source application: irreducibility of the actual moved section constructs
the elementary base, and its complete central-functional action follows. -/
theorem liftBase_full_transvections_of_irreducible
    (U K : Subgroup G) [IsExtraspecial 2 U] (z i : G)
    (hz : orderOf z = 2) (hi : orderOf i = 2)
    (hZ : (center U).map U.subtype = zpowers z)
    (hiU : i ∈ normalizer (U : Set G)) (hiz : i ∈ centralizer ({z} : Set G))
    (hout : i ∉ U) (hKU : K ≤ normalizer (U : Set G))
    (hKi : K ≤ centralizer ({i} : Set G)) (hUcard : Nat.card U = 512)
    (hmoved : Nat.card (((⁅U,zpowers i⁆).subgroupOf U).map
      (QuotientGroup.mk' (center U))) = 16)
    (hirr : ∀ E : Subgroup G, zpowers z ≤ E → E ≤ liftBase U z i →
      K ≤ normalizer (E : Set G) → E = zpowers z ∨ E = liftBase U z i) :
    ∃ (hA : IsElementaryAbelian 2 (liftBase U z i))
      (hZE : IsElementaryAbelian 2 (zpowers z)),
      let _ := hA
      let _ := hZE
      ∃ c : Configuration U (liftBase U z i) (zpowers z),
        (pairing c).ker = (liftBase U z i).subgroupOf U ∧
        Function.Surjective (pairing c) ∧
        Function.Injective (twists c.center_le) ∧
        (ExtraspecialCentralFunctionals.conjugation c).range = (twists c.center_le).range := by
  obtain ⟨_, _, hA, hAcard⟩ := centralizerLift_elementary_and_card
    U K z i hz hi hZ hiU hiz hout hKU hKi hmoved hirr
  let _ := hA
  have hz2 : z^2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  let hZE := IsElementaryAbelian.zpowers_of_pow_eq_one hz2
  refine ⟨hA, hZE,
    liftBase_centralFunctionalConfiguration U z i hz hZ hiU hUcard hA hAcard, ?_⟩
  exact liftBase_full_transvections U z i hz hZ hiU hUcard hAcard

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal
