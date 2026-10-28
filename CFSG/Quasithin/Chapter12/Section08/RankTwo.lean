module

public import CFSG.Quasithin.Chapter12.Section08.Defs
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.GroupTheory.AbelianConjugateSpan
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.ElementaryAbelian.PrimePlane

/-!
# The actual rank-two seed

Under Hypothesis 12.8.1(2), the printed assumption m₂(V)=2 already implies
that V=⟨Ω₁(Z(T))ᴹ⟩ is elementary abelian of order four. Indeed O₂(M) lies
in T, so Z=Ω₁(Z(T)) centralizes O₂(M). Normality extends this to V.
Characteristic two puts V inside O₂(M), making V abelian, and its involution
generators then give exponent two. The prime-rank comparison gives order four.

This proves the elementary-module input directly from the source hypotheses;
it does not assume it as part of the setup. The normalizer and natural-action
identifications in 12.8.3 remain separate.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed p.849.
-/

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section08
universe u
variable {G : Type u} [Group G]

public theorem centerIn_le_centralizer (A : Subgroup G) :
    centerIn A ≤ centralizer (A : Set G) := by
  rintro x ⟨x, hx, rfl⟩ y hy
  exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)

public theorem sylowOmega_le (T : Sylow 2 G) : sylowOmega T ≤ (T : Subgroup G) :=
  (omegaOneAmbient_le _).trans (map_subtype_le _)

public theorem sylowOmega_centralizes (T : Sylow 2 G) :
    sylowOmega T ≤ centralizer (T : Set G) :=
  (omegaOneAmbient_le _).trans (centerIn_le_centralizer _)

public theorem sylowOmega_elementary (T : Sylow 2 G) : IsElementaryAbelian 2 (sylowOmega T) := by
  let : IsMulCommutative (centerIn (T : Subgroup G)) :=
    map_isMulCommutative (center (T : Subgroup G)) (T : Subgroup G).subtype
  let : IsElementaryAbelian 2 (omega₁ (centerIn (T : Subgroup G)) (p := 2)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  exact IsElementaryAbelian.map (centerIn (T : Subgroup G)).subtype

variable [Finite G]

public theorem rankTwoSeed_elementary {K : GroupClass.{u}} {T : Sylow 2 G}
    {L M : Subgroup G} (h : RankTwoHypothesis K T L M) :
    IsElementaryAbelian 2 (rankTwoSeed T M) := by
  let Q := M.pCoreIn 2
  let Z := sylowOmega T
  let V := rankTwoSeed T M
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le h.sylow_le] using
      pCoreIn_le_sylow M (T.subtype h.sylow_le)
  have hZC : Z ≤ centralizer (Q : Set G) :=
    (sylowOmega_centralizes T).trans (centralizer_le hQT)
  have hN : M ≤ normalizer (Q : Set G) :=
    M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hVC : V ≤ centralizer (Q : Set G) := le_centralizer_iff.mp
    (le_centralizer_conjugateSpanBy_of_normalizes Q Z M hN (le_centralizer_iff.mp hZC))
  have hVM : V ≤ M := conjugateSpanBy_le_self ((sylowOmega_le T).trans h.sylow_le)
  have hchar := h.simpleQTKE.evenCharacteristic T M h.maximal h.sylow_le
  have hVQ : V ≤ Q := by
    intro x hx
    have hxC : (⟨x, hVM hx⟩ : M) ∈ centralizer (pCore 2 M : Set M) := by
      intro y hy
      exact Subtype.ext (mem_centralizer_iff.mp (hVC hx) y (mem_map_of_mem M.subtype hy))
    exact mem_map_of_mem M.subtype (hchar hxC)
  let : IsMulCommutative (closure {x | ∃ m ∈ M, ∃ z ∈ sylowOmega T, m * z * m⁻¹ = x}) :=
    le_centralizer_iff_isMulCommutative.mp
    (hVC.trans (centralizer_le hVQ))
  let : IsElementaryAbelian 2 Z := sylowOmega_elementary T
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro x ⟨m, _, z, hz, rfl⟩
  rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian z hz, mul_one, mul_inv_cancel]

public theorem rankTwoSeed_card {K : GroupClass.{u}} {T : Sylow 2 G}
    {L M : Subgroup G} (h : RankTwoHypothesis K T L M) : Nat.card (rankTwoSeed T M) = 4 := by
  let := rankTwoSeed_elementary h
  exact IsElementaryAbelian.card_eq_prime_sq_of_primeRank_two h.rank

end CFSG.Quasithin.Chapter12.Section08
