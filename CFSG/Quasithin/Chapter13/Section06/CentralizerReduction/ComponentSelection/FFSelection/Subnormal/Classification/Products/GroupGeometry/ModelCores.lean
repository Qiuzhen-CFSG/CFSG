module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.ProductComponents.FactorModels
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCore
/-!
# Three-cores of the B.5.6 factors

Only the degree-one SL₂ factor can have a nontrivial three-core. Higher
SL₂ and odd-degree SL₃ are quasisimple with trivial center; the normal
subgroup theorem for S₅ excludes a three-core there. The degree-one
identification uses the actual field and matrix group equivalences.

Source: Aschbacher–Smith, B.5.6(3),(5), printed p.105, used in 13.6.10,
p.928. The matrix simplicity results use the attributed ATLAS ports
imported by FactorModels.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification.Products.GroupGeometry
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ComponentExistence.ProductComponents
variable {D E : Type*} [Group D] [Group E]

private theorem transfer_core (e : D ≃* E) (h : pCore 3 E = ⊥) : pCore 3 D = ⊥ := by
  apply (map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp
  rw [pCore_map_iso, h]

private theorem sl2_threeCore (F : BinaryField) (hn : 2 ≤ F.degree) :
    pCore 3 SL(2, F.Carrier) = ⊥ := by
  have hcard : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hn
  have hfield : ∃ a : F.Carrier, a ≠ 0 ∧ a ^ 2 ≠ 1 := by
    obtain ⟨x, hx⟩ : IsCyclic F.Carrierˣ := inferInstance
    refine ⟨x, Units.ne_zero x, fun h ↦ ?_⟩
    grw [Nat.card_eq_card_units_add_one F.Carrier,
      ← orderOf_eq_card_of_forall_mem_zpowers hx,
      orderOf_le_of_pow_eq_one zero_lt_two (Units.ext <| by simpa using h)] at hcard
    omega
  let : IsQuasisimple SL(2, F.Carrier) :=
    { toIsPerfect := ⟨Matrix.SL2.commutator_eq_top hfield.choose_spec.1 hfield.choose_spec.2⟩
      simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard }
  exact le_bot_iff.mp ((IsQuasisimple.pCore_le_center 3).trans
    (Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot (F := F.Carrier)).le)

private theorem sl3_threeCore (F : BinaryField) (ho : Odd F.degree) :
    pCore 3 SL(3, F.Carrier) = ⊥ := by
  let : IsQuasisimple SL(3, F.Carrier) :=
    { toIsPerfect := Atlas.sl_perfect 3 (by decide)
      simple := Atlas.psl_simple_high_rank 3 (by decide) }
  have hz : center SL(3, F.Carrier) = ⊥ := by
    apply (Matrix.SL3.center_eq_bot_iff_card_mod_three F.Carrier).mpr
    obtain ⟨k, hk⟩ := ho
    rw [F.card_eq, hk, pow_add, pow_mul]
    norm_num [Nat.mul_mod, Nat.pow_mod]
  exact le_bot_iff.mp ((IsQuasisimple.pCore_le_center 3).trans hz.le)

private theorem s5_threeCore : pCore 3 (Equiv.Perm (Fin 5)) = ⊥ := by
  by_contra hb
  have hp : IsPGroup 3 (alternatingGroup (Fin 5)) :=
    pCore_isPGroup.to_le (Equiv.Perm.alternatingGroup_le_of_normal (by simp)
      ((nontrivial_iff_ne_bot _).mpr hb))
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  have hd : 2 ∣ Nat.card (alternatingGroup (Fin 5)) := by
    rw [nat_card_alternatingGroup]
    norm_num
  rw [hk] at hd
  have := Nat.prime_two.dvd_of_dvd_pow hd
  norm_num at this

/-- Among the actual B.5.6 factors, only S₃ has a nontrivial three-core. -/
theorem factor_threeCore [Finite D] (h : FactorModel D) :
    Nonempty (D ≃* Equiv.Perm (Fin 3)) ∨ pCore 3 D = ⊥ := by
  cases h with
  | linearTwo F e =>
    by_cases hn : F.degree = 1
    · left
      have hc : Nat.card F.Carrier = 2 := by rw [F.card_eq, hn]; rfl
      let := Fintype.ofFinite F.Carrier
      let f : F.Carrier ≃+* ZMod 2 :=
        (ZMod.ringEquivOfPrime F.Carrier (by decide)
          (by simpa only [← Nat.card_eq_fintype_card] using hc)).symm
      obtain ⟨g⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
      exact ⟨e.trans ((Atlas.fieldEquivSL 2 f).trans g)⟩
    · exact Or.inr (transfer_core e (sl2_threeCore F (by have := F.degree_pos; omega)))
  | symmetricFive e => exact Or.inr (transfer_core e s5_threeCore)
  | linearThree F ho e => exact Or.inr (transfer_core e (sl3_threeCore F ho))

/-- The first hyperplane factor has trivial three-core. -/
theorem binary_sl3_threeCore : pCore 3 SL(3, ZMod 2) = ⊥ :=
  sl3_threeCore BinaryField.two (by decide)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification.Products.GroupGeometry
