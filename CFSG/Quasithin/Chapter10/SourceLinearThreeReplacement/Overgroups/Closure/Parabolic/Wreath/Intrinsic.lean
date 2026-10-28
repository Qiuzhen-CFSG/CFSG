module
public import CFSG.Quasithin.Chapter1.Section03.Basic.MinimalParabolic
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.MaximalSylow
public import Theory.GroupTheory.WreathTwoCoreQuotient

/-!
# Xi for the intrinsic residual of a wreath-quotient group

The Sylow two-subgroup is maximal and nonnormal, and the minimal-parabolic
core is the intrinsic two-core. The residual quotient is the elementary
nine-group. An invariant subgroup of its Frattini quotient therefore lifts
to a normal subgroup contained in the two-core or containing the whole
residual. The existing minimal-parabolic criterion proves this dichotomy
for the literal `xiFrattiniAction`, without an independent action assumption.

Source: Aschbacher--Smith Definition 1.3.1 and the proof of 10.2.4,
printed pp.508 and 747.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Wreath
private theorem elementaryNine : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) where
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
    change (3 : ℕ) • Multiplicative.toAdd x = 0
    exact ZModModule.char_nsmul_eq_zero 3 (Multiplicative.toAdd x))

open Chapter1
variable {K : Type*} [Group K] [Finite K]

/-- The intrinsic wreath quotient gives all Xi clauses, including the actual
Sylow action on the iterated two-core and Frattini quotient. -/
public theorem residual_mem_Xi (S : Sylow 2 K)
    (hH : (⊤ : Subgroup K) ∈ H K)
    (e : (K ⧸ pCore 2 K) ≃* WreathTwoResidual.Actor) :
    pResidual 2 K ∈ Xi K (S : Subgroup K) ∧
      XiOddQuotient 3 (XiQuotient (pResidual 2 K)) := by
  have hmax := WreathTwoResidual.sylow_isCoatom_of_core_quotient S e
  have hP := ChapterB.isMinimalParabolicOver_of_sylow_isCoatom S hmax
    (WreathTwoResidual.sylow_not_normal_of_core_quotient S e)
  have hcore := ChapterB.minimalParabolicCore_eq_twoCore_of_sylow_isCoatom S hP hmax
  obtain ⟨r⟩ := WreathTwoResidual.residual_core_quotient_equiv_elementaryNine e
  let : IsElementaryAbelian 3 (Multiplicative (Fin 2 → ZMod 3)) := elementaryNine
  let he : IsElementaryAbelian 3 (XiQuotient (pResidual 2 K)) :=
    IsElementaryAbelian.of_surjective r.symm.toMonoidHom r.symm.surjective
  have hc : Nat.card (XiQuotient (pResidual 2 K)) = 3^2 := by
    rw [Nat.card_congr r.toEquiv]
    simp [Nat.card_eq_fintype_card]
  exact ⟨residual_mem_Xi_of_minimalParabolic_core_eq S hP hcore hH
    (by decide : Nat.Prime 3) (by decide : Odd 3) hc, Or.inl ⟨he,hc⟩⟩
end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Wreath

