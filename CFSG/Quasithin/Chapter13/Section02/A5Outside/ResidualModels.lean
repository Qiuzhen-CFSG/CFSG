module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.KernelComplete
public import Theory.GroupTheory.WreathTwoResidual
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Theory.Quasithin.CoprimeRank
public import Theory.Alternating.PrimeRank
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The exact cubic residual models in the original A₅ outside analysis

The proved omega-action kernel equality identifies H/O₂(H) with the same
natural S₃ or S₃≀C₂ actor. Transport through that quotient identifies the
intrinsic O²(H)/O₂(O²(H)) with C₃ or E₉, respectively. No quotient is
silently substituted for the source residual.

In the wreath case the residual has three-rank at least two. Every faithful
local component in the original A₅ context has three-rank one, so none can
contain that residual. This is the component exclusion used in 13.2.10.
The earlier Baumann bound and solvability remain the inputs of 13.2.9.

Source: Aschbacher–Smith, Lemmas 13.2.9–10, printed pp.880–881.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside

private theorem residual_three_card : Nat.card (pResidual 2 (Equiv.Perm (Fin 3))) = 3 := by
  have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup,Nat.card_fin]
    rfl
  have he : pResidual 2 (Equiv.Perm (Fin 3)) = alternatingGroup (Fin 3) := by
    apply le_antisymm
    · apply sInf_le
      refine ⟨inferInstance,IsPGroup.of_card (n := 1) ?_⟩
      change (alternatingGroup (Fin 3)).index = 2^1
      simp
    · intro x hx
      have hpow : x^3=1 := congrArg Subtype.val (hc ▸ pow_card_eq_one' (x := (⟨x,hx⟩ : alternatingGroup (Fin 3))))
      exact mem_pResidual_of_orderOf_coprime
        ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hpow))
  rw [he,hc]

private noncomputable def odd_core_quotient_equiv {X : Type*} [Group X] [Finite X]
    (hX : Odd (Nat.card X)) : (X ⧸ pCore 2 X) ≃* X := by
  have hz : pCore 2 X = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rcases (pCore_isPGroup (p := 2) (G := X)).card_eq_or_dvd with h | h
    · exact h
    · exact False.elim (Nat.not_even_iff_odd.mpr hX
        (even_iff_two_dvd.mpr (h.trans (pCore 2 X).card_subgroup_dvd_card)))
  exact (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot

private noncomputable def residual_equiv {X Y : Type*} [Group X] [Finite X]
    [Group Y] (e : X ≃* Y) : pResidual 2 X ≃* pResidual 2 Y :=
  ((pResidual 2 X).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (map_pResidual_of_surjective 2 e.toMonoidHom e.surjective))

private theorem residual_core_three_model {X : Type*} [Group X] [Finite X]
    (e : X ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
    Nonempty ((pResidual 2 X ⧸ pCore 2 (pResidual 2 X)) ≃* Multiplicative (ZMod 3)) := by
  obtain ⟨eS⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  let eR := residual_equiv (e.trans eS)
  have hc : Nat.card (pResidual 2 X) = 3 :=
    (Nat.card_congr eR.toEquiv).trans residual_three_card
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact ⟨(odd_core_quotient_equiv (hc ▸ (by decide : Odd 3))).trans
    (mulEquivOfPrimeCardEq hc (by simp [Nat.card_eq_fintype_card]))⟩

private theorem residual_core_nine_model {X : Type*} [Group X] [Finite X]
    (e : X ≃* WreathTwoResidual.Actor) :
    Nonempty ((pResidual 2 X ⧸ pCore 2 (pResidual 2 X)) ≃*
      Multiplicative (Fin 2 → ZMod 3)) := by
  obtain ⟨e9⟩ := WreathTwoResidual.residual_equiv_elementaryNine
  let eR := (residual_equiv e).trans e9
  have hc : Nat.card (pResidual 2 X) = 9 := by
    rw [Nat.card_congr eR.toEquiv]
    simp [Nat.card_eq_fintype_card]
  exact ⟨(odd_core_quotient_equiv (hc ▸ (by decide : Odd 9))).trans eR⟩

variable {G : Type*} [Group G] [Finite G]

/-- The exact whole quotient and the intrinsic residual quotient in both
original source cases. -/
theorem source_residual_core_quotient_models
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hB : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ normalizer (L : Set G))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : Group.IsSolvable H) :
    (Nonempty ((H ⧸ pCore 2 H) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) ∧
      Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Multiplicative (ZMod 3))) ∨
    (Nonempty ((H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor) ∧
      Nonempty ((pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃*
        Multiplicative (Fin 2 → ZMod 3))) := by
  let hU := omegaOrbit_reduced d.hypothesis.qtke T hH
  let := hU.normal
  let := hU.elementary
  let C := centralizer ((omegaOrbit T H).subgroupOf H : Set H)
  let q := QuotientGroup.mk' C
  have hC : C = pCore 2 H := source_omega_centralizer_eq_twoCore d hH hB hZ hs
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    rw [hC]
    exact pCore_isPGroup
  let eR := q.pResidualCoreQuotientEquiv (QuotientGroup.mk'_surjective C) hk
  let eQ := QuotientGroup.quotientMulEquivOfEq hC.symm
  rcases source_solvable_wreath_omega_action d hH hB hZ hs with ⟨_,e,_⟩ | ⟨e,_,_⟩
  · obtain ⟨e3⟩ := residual_core_three_model e
    exact Or.inl ⟨⟨eQ.trans e⟩,⟨eR.trans e3⟩⟩
  · obtain ⟨e9⟩ := residual_core_nine_model e
    exact Or.inr ⟨⟨eQ.trans e⟩,⟨eR.trans e9⟩⟩

/-- In the two-factor case, the original residual cannot lie in any faithful
local component: its three-rank is at least two, whereas every such A₅
component has three-rank one. This is the component exclusion in 13.2.10. -/
theorem source_wreath_residual_not_le_faithful_component
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H K : Subgroup G}
    (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
    (e : (H ⧸ pCore 2 H) ≃* WreathTwoResidual.Actor)
    (hK : K ∈ MainForward.faithfulLocalComponents T) :
    ¬ (pResidual 2 H).map H.subtype ≤ K := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨e9⟩ := residual_core_nine_model e
  let f := (q.pResidualCoreQuotientEquiv (QuotientGroup.mk'_surjective _) hk).trans e9
  let E := pResidual 2 H ⧸ pCore 2 (pResidual 2 H)
  let : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) := {
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      exact (by decide +kernel : ∀ x : Multiplicative (Fin 2 → ZMod 3),x^3=1) }
  let : IsElementaryAbelian 3 E := IsElementaryAbelian.of_injective f.toMonoidHom f.injective
  let : IsElementaryAbelian 3 (⊤ : Subgroup E) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup E).subtype (⊤ : Subgroup E).subtype_injective
  have hsize : Nat.card (⊤ : Subgroup E) = 3^2 := by
    rw [card_top,Nat.card_congr f.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hlo : 2 ≤ primeRank 3 (pResidual 2 H) := by
    have hh := IsElementaryAbelian.primeRank_ge_of_card (⊤ : Subgroup E) hsize
    change 2 ≤ primeRank 3 (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) at hh
    rwa [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup] at hh
  obtain ⟨eK⟩ := d.uniform_A5 K hK
  have hrK : primeRank 3 K = 1 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup,
      primeRank_congr 3 eK,
      GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 5 3 (by decide) (by decide)]
  intro hle
  have hup := primeRank_mono 3 hle
  rw [←primeRank_congr 3 ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective),hrK] at hup
  omega

end CFSG.Quasithin.Chapter13.Section02.A5Outside
