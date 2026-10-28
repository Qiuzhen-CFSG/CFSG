module
public import Theory.GroupTheory.WreathTwoResidual
public import Theory.GroupTheory.WreathTwoSylowMaximal
public import Theory.GroupTheory.PResidual.PCoreQuotient

/-!
# Groups with the binary wreath group as their two-core quotient

The actual quotient map carries a Sylow two-subgroup onto a maximal,
nonnormal Sylow subgroup of the wreath group. Its kernel lies in the
original Sylow subgroup, so maximality lifts. Restriction of the same
quotient map to the two-residual identifies the quotients by their own
two-cores; the target residual is the elementary group of order nine.
No containment of the whole ambient two-core in the residual is assumed.

This extracts the intrinsic quotient argument used in the Chapter 13
outside-wreath calculation, without its later source hypotheses.
Source applications: Aschbacher--Smith 10.2.4 and 13.2.10, pp.747 and 881.
-/

open Subgroup
namespace Theory.GroupTheory.WreathTwoResidual
variable {K : Type*} [Group K] [Finite K]
/-- Sylow maximality lifts through the intrinsic two-core quotient. -/
public theorem sylow_isCoatom_of_core_quotient (S : Sylow 2 K) (e : (K ⧸ pCore 2 K) ≃* Actor) :
    IsCoatom (S : Subgroup K) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hker : f.ker ≤ (S : Subgroup K) := hk ▸ pCore_isPGroup.le_sylow_of_normal S
  have hmax := isCoatom_comap_of_surjective hf (wreath_two_sylow_isCoatom (S.mapSurjective hf))
  change IsCoatom (((S : Subgroup K).map f).comap f) at hmax
  rwa [comap_map_eq_self hker] at hmax

/-- A Sylow subgroup with this core quotient is not normal. -/
public theorem sylow_not_normal_of_core_quotient (S : Sylow 2 K) (e : (K ⧸ pCore 2 K) ≃* Actor) :
    ¬ (S : Subgroup K).Normal := by
  intro hn
  let _ := hn
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let R := S.mapSurjective hf
  have hrn : (R : Subgroup Actor).Normal := Subgroup.Normal.map hn f hf
  have hr : (R : Subgroup Actor) = ⊥ := by
    apply bot_unique
    rw [← twoCore_eq_bot]
    exact le_sSup ⟨hrn,R.isPGroup'⟩
  obtain ⟨r⟩ := wreath_two_sylow_mulEquiv_dihedral_four R
  have hc : Nat.card (R : Subgroup Actor) = 8 := by
    rw [Nat.card_congr r.toEquiv,DihedralGroup.nat_card]
  rw [hr,Nat.card_unique] at hc
  norm_num at hc

/-- The residual modulo its own two-core is the actual elementary nine-group. -/
public theorem residual_core_quotient_equiv_elementaryNine (e : (K ⧸ pCore 2 K) ≃* Actor) :
    Nonempty ((pResidual 2 K ⧸ pCore 2 (pResidual 2 K)) ≃*
      Multiplicative (Fin 2 → ZMod 3)) := by
  let q := QuotientGroup.mk' (pCore 2 K)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  obtain ⟨e9⟩ := residual_equiv_elementaryNine
  let r := (((pResidual 2 (K ⧸ pCore 2 K)).equivMapOfInjective e.toMonoidHom
    e.injective).trans (MulEquiv.subgroupCongr
      (map_pResidual_of_surjective 2 e.toMonoidHom e.surjective))).trans e9
  have hc : Nat.card (pResidual 2 (K ⧸ pCore 2 K)) = 9 := by
    rw [Nat.card_congr r.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hz : pCore 2 (pResidual 2 (K ⧸ pCore 2 K)) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rcases (pCore_isPGroup (p := 2) (G := pResidual 2 (K ⧸ pCore 2 K))).card_eq_or_dvd with h | h
    · exact h
    · have hd := h.trans (pCore 2 (pResidual 2 (K ⧸ pCore 2 K))).card_subgroup_dvd_card
      rw [hc] at hd
      norm_num at hd
  exact ⟨(q.pResidualCoreQuotientEquiv (QuotientGroup.mk'_surjective _) hk).trans
    (((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans r)⟩
end Theory.GroupTheory.WreathTwoResidual

