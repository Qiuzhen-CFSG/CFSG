module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.OtherRows.Marking

/-!
# Central marks from the quotient model fixed-group index

For an actor of projected order two, the two-central mark in L* is equivalent
to innerness of its actual action on the specified model and odd fixed-group
index. The proof transports the Sylow-center witness along L/Z(L) ≃ L*
and the model equivalence; an inner actor need not itself belong to L.

This supplies the marks on the literal rows used in Aschbacher–Smith
16.5.6(4), printed p.1197, without adding marks as table hypotheses.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.JankoTwoHigmanSims
open Subgroup Theory.GroupTheory Theory.GroupTheory.DoubleCoverCentralizer

private theorem twoCentral_of_odd_index {S : Type*} [Group S] [Finite S]
    (x : S) (hx : orderOf x = 2) (hi : Odd (centralizer ({x} : Set S)).index) :
    TwoCentral x := by
  have ht : IsTwoCentralIn (⊤ : Subgroup S) x := by
    apply twoCentral_iff_odd_index.mpr
    refine ⟨hx, trivial, ?_⟩
    change Odd ((centralizer ({x} : Set S)).comap (⊤ : Subgroup S).subtype).index
    rw [index_comap_of_surjective _ (show Function.Surjective (⊤ : Subgroup S).subtype from
      fun y => ⟨⟨y, trivial⟩, rfl⟩)]
    exact hi
  exact ((twoCentralIn_coe_iff (⟨x, trivial⟩ : (⊤ : Subgroup S))).mp ht).2.map topEquiv

/-- The two-central mark is innerness together with odd index of the actual model fixed subgroup. -/
theorem action_twoCentral_iff_model_index {G S : Type*} [Group G] [Finite G]
    [Group S] [Finite S] {L : Subgroup G} [IsQuasisimple L]
    (e : (L ⧸ center L) ≃* S) (u : normalizer (L : Set G))
    (hu2 : orderOf (actionMap (L := L) le_rfl u) = 2) :
    IsTwoCentralIn (componentImage L) (actionMap (L := L) le_rfl u) ↔
      (∃ x, MulAut.centralQuotientAction e (L.normalizerMonoidHom u) = MulAut.conj x) ∧
      Odd (MulAut.centralQuotientAction e (L.normalizerMonoidHom u)).fixedSubgroup.index := by
  constructor
  · intro hu
    obtain ⟨_, k, hk, hkc⟩ := (action_twoCentral_iff u).mp hu
    have hmodel := MulAut.centralQuotientAction_conj e k
    rw [hk, hmodel]
    refine ⟨⟨_, rfl⟩, ?_⟩
    rw [MulAut.fixedSubgroup_conj]
    exact Nat.not_even_iff_odd.mp (fun he =>
      (hkc.map e).not_dvd_centralizer_index (even_iff_two_dvd.mp he))
  · rintro ⟨hi, ho⟩
    obtain ⟨k, hk⟩ := (MulAut.centralQuotientAction_inner_iff e _).mp hi
    apply (action_twoCentral_iff u).mpr
    refine ⟨hu2, k, hk, ?_⟩
    let q := QuotientGroup.mk' (center L) k
    have hrep : (componentImageEquiv L q : ActionQuotient L) =
        actionMap (L := L) le_rfl u := by
      rw [componentImageEquiv_mk]
      apply actionHom_injective
      rw [actionHom_component, actionHom_actionMap, hk]
    have hq2 : orderOf q = 2 := by
      rw [← (componentImageEquiv L).orderOf_eq q,
        ← orderOf_submonoid (componentImageEquiv L q), hrep]
      exact hu2
    rw [hk, MulAut.centralQuotientAction_conj, MulAut.fixedSubgroup_conj] at ho
    have hc := twoCentral_of_odd_index (e q) ((e.orderOf_eq q).trans hq2) ho
    simpa only [MulEquiv.symm_apply_apply] using hc.map e.symm

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.OtherRows.JankoTwoHigmanSims
