module

import all Theory.SpecificGroups.PSL2.QuinticInnerFusion
public import Theory.GroupTheory.SylowCentralInvolutionEscape
public import Theory.SpecificGroups.PSL2.NonabelianSylowNormalizer
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.PPrimeCoreReduction
public import Theory.GroupTheory.PGroup.RankOneInvolution
public import GorensteinWalter.PSL2OddCore
public import GorensteinWalter.KleinFourMapInjective
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Central involution escape in extensions of odd PSL₂

For an actual self-centralizing normal PSL₂ subgroup with nonabelian Sylow
subgroups, a central involution of the supplied Sylow subgroup cannot remain
weakly closed in the two-core of a normalized quintic supplement. The inner
part of that core has a unique involution, because no Klein four centralizes
a nontrivial odd cyclic subgroup of PSL₂. This derives the hypotheses of
the corefree Z-star escape lemma from the actual normal component and core.

This is the cyclic elementary-subgroup step for the quadratic field case
in the final paragraph of Aschbacher--Smith 6.1.4, printed p.666.
-/

public section
open Subgroup GorensteinWalter Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PSL2

private theorem sylow_normalizer_of_inner
    {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    (T : Sylow 2 G) (hgen : N ⊔ (T : Subgroup G) = ⊤)
    (hN : ∀ U : Sylow 2 N, normalizer (U : Set N) = (U : Subgroup N)) :
    normalizer (T : Set G) = (T : Subgroup G) := by
  obtain ⟨U, hU⟩ := T.exists_subgroupOf_eq_of_normal N
  apply le_antisymm _ (T : Subgroup G).le_normalizer
  intro g hg
  obtain ⟨k, hk, t, ht, rfl⟩ := mem_sup_of_normal_left.mp (hgen ▸ mem_top g)
  have hkT : k ∈ normalizer (T : Set G) := by
    have he : k = (k * t) * t⁻¹ := by group
    rw [he]
    exact (normalizer (T : Set G)).mul_mem hg
      ((normalizer (T : Set G)).inv_mem ((T : Subgroup G).le_normalizer ht))
  have hkN : (⟨k, hk⟩ : N) ∈ normalizer (U : Set N) := by
    change (⟨k, hk⟩ : N) ∈ normalizer ((U : Subgroup N) : Set N)
    rw [hU]
    exact (le_normalizer_comap N.subtype) hkT
  rw [hN U, hU] at hkN
  exact (T : Subgroup G).mul_mem hkN ht

/-- A Sylow-central involution of the actual quintic two-core has an inner
conjugate returning to the supplied Sylow subgroup and escaping that core.
The odd core, Sylow normalizer, and inner involution control are derived. -/
theorem odd_quintic_central_involution_escape
    {G : Type*} [Group G] [Finite G]
    {F : Type} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (h8 : 8 ∣ Nat.card PSL(2,F))
    (N : Subgroup G) [N.Normal] (e : N ≃* PSL(2,F))
    (hC : centralizer (N : Set G) = ⊥)
    (T : Sylow 2 G) (hgen : N ⊔ (T : Subgroup G) = ⊤)
    (X : Subgroup G) (hXN : X ≤ N) (hfive : Nat.card X = 5)
    (hTX : (T : Subgroup G) ≤ normalizer X)
    (a : G) (haS : a ∈ (X ⊔ (T : Subgroup G)).pCoreIn 2)
    (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1)
    (haT : a ∈ centralizer (T : Set G)) :
    ∃ g ∈ N, g * a * g⁻¹ ∈ (T : Subgroup G) ∧
      g * a * g⁻¹ ∉ (X ⊔ (T : Subgroup G)).pCoreIn 2 := by
  classical
  let H := X ⊔ (T : Subgroup G)
  let S := H.pCoreIn 2
  let R := S ⊓ N
  have hST : S ≤ (T : Subgroup G) := by
    have hh := H.pCoreIn_le_sylow (T.subtype (show (T : Subgroup G) ≤ H from le_sup_right))
    change S ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)] at hh
  have hTS : (T : Subgroup G) ≤ normalizer S :=
    (show (T : Subgroup G) ≤ H from le_sup_right).trans
      (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hTR : (T : Subgroup G) ≤ normalizer R :=
    (le_inf hTS le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  have hSC : S ≤ centralizer (X : Set G) := quintic_join_core_centralizes X T hfive hTX
  let Y := (X.subgroupOf N).map e.toMonoidHom
  have hYcard : Nat.card Y = 5 := by
    rw [card_map_of_injective e.injective]
    exact (Nat.card_congr (subgroupOfEquivOfLe hXN).toEquiv).trans hfive
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let : IsCyclic Y := isCyclic_of_prime_card hYcard
  have hYne : Y ≠ ⊥ := by intro he; simp [he] at hYcard
  have hYodd : Odd (Nat.card Y) := by rw [hYcard]; decide
  let f : R →* PSL(2,F) := e.toMonoidHom.comp (inclusion (show R ≤ N from inf_le_right))
  have hf : Function.Injective f := e.injective.comp (inclusion_injective inf_le_right)
  have hfour (V : Subgroup R) (hV : IsElementaryAbelian 2 V) (hc : Nat.card V = 4) : False := by
    let : IsElementaryAbelian 2 V := hV
    let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
    have hi := isKleinFour_map_of_injective V
      (show IsKleinFour V from ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩) f hf
    apply psl2_no_kleinFour_centralizes_odd_cyclic F hF Y (V.map f)
      inferInstance hYne hYodd hi
    rintro _ ⟨v, hv, rfl⟩ _ ⟨x, hx, rfl⟩
    have he : x * inclusion (show R ≤ N from inf_le_right) v =
        inclusion (show R ≤ N from inf_le_right) v * x :=
      Subtype.ext (hSC v.property.1 x hx)
    change e x * e (inclusion (show R ≤ N from inf_le_right) v) =
      e (inclusion (show R ≤ N from inf_le_right) v) * e x
    simpa only [map_mul] using congrArg e he
  have hinner (z : G) (hz : z ∈ R) (hz2 : z ^ 2 = 1) :
      z ∈ centralizer (T : Set G) := by
    by_cases hz1 : z = 1
    · simp [hz1]
    let : Nontrivial R := (nontrivial_iff_ne_bot R).mpr (by
      intro he
      exact hz1 (mem_bot.mp (he ▸ hz)))
    have hR : IsPGroup 2 R := (isPGroup_pCoreIn 2 H).to_inf_left
    obtain ⟨u, _, _, hu⟩ := hR.exists_central_involution_of_no_elementary_four hfour
    have hzu : (⟨z, hz⟩ : R) = u := (hu ⟨z, hz⟩ (Subtype.ext hz2)).resolve_left
      (fun he => hz1 (congrArg Subtype.val he))
    intro t ht
    have hm : t * z * t⁻¹ ∈ R := (mem_normalizer_iff.mp (hTR ht) z).mp hz
    have hp : (t * z * t⁻¹) ^ 2 = 1 := by
      change (MulAut.conj t z) ^ 2 = 1
      rw [← map_pow, hz2, map_one]
    have hn : t * z * t⁻¹ ≠ 1 := by
      intro he
      exact hz1 ((MulAut.conj t).injective (he.trans (map_one _).symm))
    have he := (hu ⟨t * z * t⁻¹, hm⟩ (Subtype.ext hp)).resolve_left
      (fun hh => hn (congrArg Subtype.val hh))
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val (he.trans hzu.symm))
  have hNT : normalizer (T : Set G) = (T : Subgroup G) := by
    apply sylow_normalizer_of_inner N T hgen
    intro U
    apply map_injective (f := e.toMonoidHom) e.injective
    change (normalizer ((U : Subgroup N) : Set N)).map e.toMonoidHom = _
    rw [map_equiv_normalizer_eq]
    exact large_sylow_normalizer hF h8
      (U.mapSurjective (f := e.toMonoidHom) e.surjective)
  have hcore : pPrimeCore 2 G = ⊥ :=
    pPrimeCore_eq_bot_of_selfCentralizing N
      (pPrimeCore_eq_bot_of_equiv e (psl2_pPrimeCore_two_eq_bot F hF))
      (hC.le.trans bot_le)
  have haG : a ∉ center G := by
    intro ha
    apply ha1
    exact mem_bot.mp (hC ▸ (show a ∈ centralizer (N : Set G) from
      fun n hn => mem_center_iff.mp ha n))
  exact sylow_central_involution_escape N T S hgen hNT hcore hST hinner a haS ha2 ha1 haT haG

end Theory.PSL2
