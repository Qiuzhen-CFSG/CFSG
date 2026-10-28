module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationDefs
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Normalizers
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The first centralizer splitting in 12.2.25

For the actual cyclic pair I=PUV, first show C_{PU}(U)=U: the prime-order
actor P is faithful on the nonzero U. Thus [C_T(U),P]=U, and coprime
action gives C_T(U)=U C_T(PU). The no-escape condition makes C_V(P)=1;
relative normality of PU in H then shows C_T(PU)=C_T(I). The two factors
are disjoint and commute, giving the literal multiplication isomorphism.

The last application records the uniqueness argument that kills a subgroup
normal in LT and normalized by the escaping pair. No global normality of
the local cores or residuals is used. The later splitting with C_T(L),
its elimination, and the dimension branches remain separate obligations.

Source: Aschbacher--Smith, 12.2.25, printed p.805, first three paragraphs.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {d : ℕ} {H P U : Subgroup G}
namespace CyclicLocalAnalysis
variable (C : CyclicLocalAnalysis T L V d H P U)
include C

omit [Finite G] in
theorem sylow_le_overgroup : (T : Subgroup G) ≤ H := by
  rw [C.overgroup]
  exact le_sup_right

omit [Finite G] in
theorem core_le_sylow : U ≤ (T : Subgroup G) :=
  C.in_core.trans (by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le C.sylow_le_overgroup] using
      pCoreIn_le_sylow H (T.subtype C.sylow_le_overgroup))

omit [Finite G] in
theorem overgroup_normalizes_core : H ≤ normalizer (U : Set G) := by
  rw [← C.core]
  exact C.pair_normal.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

omit [Finite G] in
theorem sylow_normalizes_core : (T : Subgroup G) ≤ normalizer (U : Set G) :=
  C.sylow_le_overgroup.trans C.overgroup_normalizes_core

omit [Finite G] in
theorem overgroup_normalizes_residual : H ≤ normalizer ((P ⊔ U : Subgroup G) : Set G) := by
  rw [← C.residual]
  exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))

omit [Finite G] in
theorem chosen_fixed_odd_eq_bot (hnone : NoEscape L V) :
    V ⊓ centralizer (P : Set G) = ⊥ := by
  apply bot_unique
  intro v hv
  apply mem_bot.mpr
  by_contra hv1
  apply C.escapes
  apply le_trans _ (hnone v hv.1 hv1)
  intro p hp
  rw [mem_centralizer_singleton_iff]
  exact hv.2 p hp

omit [Finite G] in
theorem sylow_centralizer_residual_eq_pair (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hVT : V ≤ (T : Subgroup G)) (hnone : NoEscape L V) :
    (T : Subgroup G) ⊓ centralizer ((P ⊔ U : Subgroup G) : Set G) =
      (T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G) := by
  let B := (T : Subgroup G) ⊓ centralizer ((P ⊔ U : Subgroup G) : Set G)
  have hBC : B ≤ centralizer (V : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    rw [← C.chosen_fixed_odd_eq_bot hnone]
    refine le_inf (le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans hTV)) ?_
    have hVN : V ≤ normalizer (centralizer ((P ⊔ U : Subgroup G) : Set G) : Set G) :=
      (hVT.trans C.sylow_le_overgroup).trans
        (C.overgroup_normalizes_residual.trans (normalizer_le_normalizer_centralizer _))
    exact ((commutator_mono inf_le_right le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hVN)).trans (centralizer_le (show P ≤ P ⊔ U from le_sup_left))
  apply le_antisymm
  · exact le_inf inf_le_left (le_centralizer_iff.mp
      (sup_le (le_centralizer_iff.mp inf_le_right) (le_centralizer_iff.mp hBC)))
  · exact inf_le_inf_left _ (centralizer_le (show P ⊔ U ≤ cyclicPairJoin P U V from le_sup_left))

omit [Finite G] in
theorem core_ne_bot (hd : 2 ≤ d) : U ≠ ⊥ := by
  intro he
  have hc := C.dimension
  rw [he, card_bot] at hc
  have hp : 1 < 2 ^ (2 * (d - 1)) := one_lt_pow₀ (by decide) (by omega)
  omega

theorem odd_centralizer_core_eq_bot (hd : 2 ≤ d) :
    P ⊓ centralizer (U : Set G) = ⊥ := by
  rcases (Nat.dvd_prime C.prime_order).mp
    (card_dvd_of_le (inf_le_left : P ⊓ centralizer (U : Set G) ≤ P)) with hc | hc
  · exact eq_bot_of_card_eq _ hc
  · have he : P ⊓ centralizer (U : Set G) = P :=
      eq_of_le_of_card_ge inf_le_left hc.ge
    have hPU : P ≤ centralizer (U : Set G) := he ▸ inf_le_right
    have hU : U = ⊥ := by
      apply bot_unique
      rw [← C.fixed]
      exact le_inf le_rfl (le_centralizer_iff.mp hPU)
    exact False.elim (C.core_ne_bot hd hU)

theorem residual_centralizer_core (hd : 2 ≤ d) :
    (P ⊔ U) ⊓ centralizer (U : Set G) = U := by
  let := C.elementary
  have hPU : P ≤ normalizer (U : Set G) :=
    (show P ≤ H by rw [C.overgroup]; exact le_sup_left).trans C.overgroup_normalizes_core
  apply le_antisymm
  · intro x hx
    have hxprod : x ∈ (U : Set G) * (P : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left U P hPU]
      change x ∈ U ⊔ P
      rw [sup_comm]
      exact hx.1
    obtain ⟨u, hu, p, hp, rfl⟩ := hxprod
    have hpc : p ∈ centralizer (U : Set G) := by
      have hh := (centralizer (U : Set G)).mul_mem
        ((centralizer _).inv_mem (le_centralizer U hu)) hx.2
      simpa only [inv_mul_cancel_left] using hh
    have hp1 : p = 1 := mem_bot.mp (C.odd_centralizer_core_eq_bot hd ▸
      (show p ∈ P ⊓ centralizer (U : Set G) from ⟨hp, hpc⟩))
    change u * p ∈ U
    rw [hp1, mul_one]
    exact hu
  · exact le_inf le_sup_right (le_centralizer U)

theorem sylow_centralizer_core_commutator (hd : 2 ≤ d) :
    ⁅(T : Subgroup G) ⊓ centralizer (U : Set G), P⁆ = U := by
  let := C.elementary
  have hPH : P ≤ H := by rw [C.overgroup]; exact le_sup_left
  have hPC : P ≤ normalizer (centralizer (U : Set G) : Set G) :=
    (hPH.trans C.overgroup_normalizes_core).trans (normalizer_le_normalizer_centralizer _)
  apply le_antisymm
  · conv_rhs => rw [← C.residual_centralizer_core hd]
    refine le_inf ?_ ((commutator_mono inf_le_right le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hPC))
    rw [commutator_comm]
    exact (commutator_mono le_sup_left (inf_le_left.trans C.sylow_le_overgroup)).trans
      (le_normalizer_iff_commutator_le_left.mp C.overgroup_normalizes_residual)
  · conv_lhs => rw [← C.moved]
    exact commutator_mono (le_inf C.core_le_sylow (le_centralizer U)) le_rfl

theorem sylow_centralizer_core_decomposition (hd : 2 ≤ d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hVT : V ≤ (T : Subgroup G)) (hnone : NoEscape L V) :
    (T : Subgroup G) ⊓ centralizer (U : Set G) =
      U ⊔ ((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) := by
  let := C.elementary
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  have hU : U ≤ R := le_inf C.core_le_sylow (le_centralizer U)
  have hnorm : P ≤ normalizer (R : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr ((C.sylow_centralizer_core_commutator hd).le.trans hU)
  have hpR : IsPGroup 2 R := T.isPGroup'.of_injective
    (inclusion (show R ≤ (T : Subgroup G) from inf_le_left)) (inclusion_injective _)
  have hcop : (Nat.card P).Coprime (Nat.card R) := by
    obtain ⟨n, hn⟩ := hpR.exists_card_eq
    rw [hn]
    exact C.odd_order.coprime_two_right.pow_right n
  have he := eq_commutator_sup_centralizer_of_solvable_coprime R P hnorm
    (@IsNilpotent.to_isSolvable R _ hpR.isNilpotent) hcop
  rw [C.sylow_centralizer_core_commutator hd] at he
  have hc : R ⊓ centralizer (P : Set G) =
      (T : Subgroup G) ⊓ centralizer ((P ⊔ U : Subgroup G) : Set G) := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left) (le_centralizer_iff.mp
        (sup_le (le_centralizer_iff.mp inf_le_right)
          (le_centralizer_iff.mp (inf_le_left.trans inf_le_right))))
    · exact le_inf (le_inf inf_le_left (inf_le_right.trans
        (centralizer_le (show U ≤ P ⊔ U from le_sup_right))))
        (inf_le_right.trans (centralizer_le (show P ≤ P ⊔ U from le_sup_left)))
  rwa [hc, C.sylow_centralizer_residual_eq_pair hTV hVT hnone] at he

omit [Finite G] in
theorem core_disjoint_sylow_pair_centralizer :
    Disjoint U ((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) := by
  apply disjoint_def.mpr
  intro x hxU hxC
  apply mem_bot.mp
  rw [← C.fixed]
  exact ⟨hxU, centralizer_le
    (show P ≤ cyclicPairJoin P U V from le_sup_left.trans le_sup_left) hxC.2⟩

theorem sylow_centralizer_core_directProduct (hd : 2 ≤ d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hVT : V ≤ (T : Subgroup G)) (hnone : NoEscape L V) :
    ∃ e : U × ↥((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) ≃*
      ↥((T : Subgroup G) ⊓ centralizer (U : Set G)),
      ∀ u c, (e (u, c) : G) = (u : G) * (c : G) := by
  have hc : U ≤ centralizer
      (((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G) : Subgroup G) : Set G) :=
    le_centralizer_iff.mp (inf_le_right.trans (centralizer_le
      (show U ≤ cyclicPairJoin P U V from le_sup_right.trans le_sup_left)))
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting U
    ((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G))
    C.core_disjoint_sylow_pair_centralizer hc
  exact ⟨e.trans (MulEquiv.subgroupCongr
    (C.sylow_centralizer_core_decomposition hd hTV hVT hnone).symm), he⟩

end CyclicLocalAnalysis

/-- Application to the original source choice: the first direct product
in the displayed equality (*) on printed p.805. -/
theorem chosen_centralizer_core_directProduct
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (C : CyclicLocalAnalysis T L V d H P U)
    (hnone : NoEscape L V) :
    ∃ e : U × ↥((T : Subgroup G) ⊓ centralizer (cyclicPairJoin P U V : Set G)) ≃*
      ↥((T : Subgroup G) ⊓ centralizer (U : Set G)),
      ∀ u c, (e (u, c) : G) = (u : G) * (c : G) :=
  C.sylow_centralizer_core_directProduct (by have := A.dimension.1; omega)
    (((structural G T L h).2.2 V D).1) D.le_sylow hnone

/-- The original uniqueness theorem kills any subgroup normal in LT and
normalized by the escaping cyclic pair. This is used twice in12.2.25. -/
theorem chosen_common_normal_subgroup_eq_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (C : CyclicLocalAnalysis T L V d H P U)
    {B : Subgroup G} (hB : B ≤ L ⊔ (T : Subgroup G))
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer (B : Set G))
    (hI : cyclicPairJoin P U V ≤ normalizer (B : Set G)) : B = ⊥ := by
  by_contra hne
  exact C.escapes ((le_sup_left.trans le_sup_left : P ≤ cyclicPairJoin P U V).trans
    (hI.trans (D.normal_subgroup_normalizer_le h.toHypothesis1221 hB hne hn)))

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
