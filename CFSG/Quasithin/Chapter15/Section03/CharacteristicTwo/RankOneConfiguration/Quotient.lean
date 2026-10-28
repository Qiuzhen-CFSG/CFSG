module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.ConjugatePair
public import Theory.GroupTheory.NormalJoinQuotientProduct

/-!
# The quotient by the common action centralizer

The denominator is the centralizer of the actual join `W = U ⊔ Uᵗ`
inside `N = XS`. Normalization of both factors proves its normality.
If both action centralizers lie in `S`, this is exactly `C_S(W)`.
The images of the two centralizers in the resulting quotient form an
internal direct product. Identifying their join with `O₂(N)` gives
the source's assertion about `P⁺`.

The equality generating `O₂(N)` is an explicit remaining obligation,
requiring the irreducible parabolic action and normalizer contradiction.
It is not part of the definition of the quotient or a consequence of
disjointness of the two modules alone.

Source: Aschbacher–Smith 15.3.32(6), combined manuscript (1 March 2004),
printed p.1133.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration

open Subgroup

variable {G : Type*} [Group G]

/-- The centralizer is intrinsic to the indicated local overgroup. -/
def actionCentralizer (N U : Subgroup G) : Subgroup N :=
  (centralizer (U : Set G)).subgroupOf N

/-- The denominator of the common action quotient. -/
abbrev pairKernel (N U V : Subgroup G) : Subgroup N :=
  actionCentralizer N (U ⊔ V)

/-- The common action kernel is the intersection of the individual kernels. -/
theorem pairKernel_eq_inf (N U V : Subgroup G) :
    pairKernel N U V = actionCentralizer N U ⊓ actionCentralizer N V := by
  have hc : centralizer ((U ⊔ V : Subgroup G) : Set G) =
      centralizer (U : Set G) ⊓ centralizer (V : Set G) := by
    apply le_antisymm (le_inf
      (centralizer_le (show U ≤ U ⊔ V from le_sup_left))
      (centralizer_le (show V ≤ U ⊔ V from le_sup_right)))
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)
  change (centralizer ((U ⊔ V : Subgroup G) : Set G)).subgroupOf N = _
  rw [hc]
  rfl

/-- Normalization of the vectors proves relative normality of their centralizer. -/
theorem actionCentralizer_normal {N U : Subgroup G}
    (hNU : N ≤ normalizer (U : Set G)) : (actionCentralizer N U).Normal :=
  normal_subgroupOf_of_le_normalizer (hNU.trans (normalizer_le_normalizer_centralizer _))

/-- The quotient denominator is normal in `N`, not necessarily in `G`. -/
theorem pairKernel_normal {N U V : Subgroup G}
    (hNU : N ≤ normalizer (U : Set G)) (hNV : N ≤ normalizer (V : Set G)) :
    (pairKernel N U V).Normal :=
  actionCentralizer_normal ((le_inf hNU hNV).trans
    (normalizer_inf_normalizer_le_normalizer_sup U V))

/-- The actual common action quotient, equal to `XS/C_S(W)` when the
centralizer in `XS` lies in `S`. -/
abbrev PairPlus (N U V : Subgroup G) [(pairKernel N U V).Normal] :=
  N ⧸ pairKernel N U V

/-- The quotient homomorphism retains the indicated denominator. -/
def pairPlusMap (N U V : Subgroup G) [(pairKernel N U V).Normal] :
    N →* PairPlus N U V := QuotientGroup.mk' (pairKernel N U V)

/-- The ambient image of the common denominator is precisely `C_S(W)`
when one of the individual centralizers in `N` is contained in `S`. -/
theorem pairKernel_map_eq_sylow_centralizer
    {N S U V : Subgroup G} (hSN : S ≤ N)
    (hCS : N ⊓ centralizer (U : Set G) ≤ S) :
    (pairKernel N U V).map N.subtype = S ⊓ centralizer ((U ⊔ V : Subgroup G) : Set G) := by
  change ((centralizer ((U ⊔ V : Subgroup G) : Set G)).subgroupOf N).map N.subtype = _
  rw [subgroupOf_map_subtype]
  apply le_antisymm
  · rintro x ⟨hxW, hxN⟩
    exact ⟨hCS ⟨hxN, centralizer_le (show U ≤ U ⊔ V from le_sup_left) hxW⟩, hxW⟩
  · rintro x ⟨hxS, hxW⟩
    exact ⟨hxW, hSN hxS⟩

/-- The action centralizer becomes `C_S(U)` as an intrinsic subgroup of `N`. -/
theorem actionCentralizer_eq_sylow_centralizer
    {N S U : Subgroup G} (hCS : N ⊓ centralizer (U : Set G) ≤ S) :
    actionCentralizer N U = (S ⊓ centralizer (U : Set G)).subgroupOf N := by
  ext n
  exact ⟨fun hn => ⟨hCS ⟨n.property, hn⟩, hn⟩, fun hn => hn.2⟩

/-- Source 15.3.32(6), conditional on the core-generation calculation.
Both factors are the actual images of `C_S(U)` and `C_S(V)`, and the
quotient denominator is proved to be `C_S(U ⊔ V)`. -/
theorem lemma_15_3_32_6_of_core_generation
    (N S U V : Subgroup G) (hSN : S ≤ N)
    (hNU : N ≤ normalizer (U : Set G)) (hNV : N ≤ normalizer (V : Set G))
    (hCUS : N ⊓ centralizer (U : Set G) ≤ S)
    (hCVS : N ⊓ centralizer (V : Set G) ≤ S)
    (hcore : pCore 2 N = actionCentralizer N U ⊔ actionCentralizer N V) :
    letI := pairKernel_normal hNU hNV
    let q := pairPlusMap N U V
    let A := ((S ⊓ centralizer (U : Set G)).subgroupOf N).map q
    let B := ((S ⊓ centralizer (V : Set G)).subgroupOf N).map q
    (pairKernel N U V).map N.subtype = S ⊓ centralizer ((U ⊔ V : Subgroup G) : Set G) ∧
      (pCore 2 N).map q = A ⊔ B ∧ Disjoint A B ∧
      ∃ e : A × B ≃* (pCore 2 N).map q,
        ∀ a b, (e (a, b) : PairPlus N U V) = (a : PairPlus N U V) * b := by
  let := pairKernel_normal hNU hNV
  let q := pairPlusMap N U V
  let := actionCentralizer_normal hNU
  let := actionCentralizer_normal hNV
  have hk : q.ker = actionCentralizer N U ⊓ actionCentralizer N V :=
    (QuotientGroup.ker_mk' _).trans (pairKernel_eq_inf N U V)
  have hprod := normal_join_image_direct_product q (actionCentralizer N U)
    (actionCentralizer N V) hk
  have hCU := actionCentralizer_eq_sylow_centralizer hCUS
  have hCV := actionCentralizer_eq_sylow_centralizer hCVS
  dsimp only
  refine ⟨pairKernel_map_eq_sylow_centralizer hSN hCUS, ?_, ?_⟩
  · rw [hcore, Subgroup.map_sup, hCU, hCV]
  · rw [← hCU, ← hCV, hcore]
    exact hprod

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration

end
