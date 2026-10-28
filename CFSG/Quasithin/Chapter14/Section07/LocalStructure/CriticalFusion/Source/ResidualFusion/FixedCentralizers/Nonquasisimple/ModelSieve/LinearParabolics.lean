module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.QuotientInputs
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.StarResidualContract

/-!
# Residual consequences for the C.2.7 parabolic comparisons

The source alternatives in C.2.7 describe the stabilizer geometrically, while
the local construction supplies a normal perfect subgroup with an A₅ section
and a two-group quotient. This file records the residual consequences of
that *literal* hypothesis which are independent of a choice of model:

* five divides the order of the actual stabilizer;
* its perfect normal subgroup is the literal two-residual;
* its order is 60 times a power of two, so seven does not divide it;
* every solvable quotient is a two-group.

The descendants `Coordinates`, `Applications` and `Transport` connect the
existential `LinearFlag` and `IsLinearMaximalParabolic` witnesses to the
concrete coordinate parabolics. `Transport` completes all three comparisons
on the literal fixed-centralizer groups, with only the permitted local
`HasA5TwoResidual` input. The parent model sieve owns its discharge.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), A.3.14,
pp.49–50, C.2.7, pp.145–147, and 14.7.68(2), pp.1071–1072.
-/

@[expose] public section
noncomputable section

open Subgroup Representation Theory.GroupTheory

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
namespace Nonquasisimple

private theorem perfect_isPPerfect {M : Type*} [Group M] [Finite M]
    [Group.IsPerfect M] (p : ℕ) [Fact p.Prime] : IsPPerfect p M := by
  intro N hN hq
  let _ := hN
  by_contra hne
  let _ : Nontrivial (M ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let _ : Group.IsPerfect (M ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let _ : Group.IsNilpotent (M ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isNilpotent (M ⧸ N) inferInstance

/-- The literal A₅ quotient forces a factor five in the order of its carrier.

The quotient is taken by the actual two-core of the witness `B`; no quotient
of an ambient model is substituted. -/
theorem hasA5TwoResidual_dvd_card {M : Type*} [Group M] [Finite M]
    (h : HasA5TwoResidual M) : 5 ∣ Nat.card M := by
  obtain ⟨B, hBN, hperfect, ⟨e⟩, _⟩ := h
  let _ := hBN
  have hq : Nat.card (B ⧸ pCore 2 B) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hB : 5 ∣ Nat.card B := by
    exact (by decide : 5 ∣ 60).trans
      (hq ▸ card_quotient_dvd_card (pCore 2 B))
  rcases hB with ⟨b, hb⟩
  rcases card_dvd_of_le (show B ≤ (⊤ : Subgroup M) from le_top) with ⟨c, hc⟩
  refine ⟨b * c, ?_⟩
  rw [← Nat.card_congr Subgroup.topEquiv.toEquiv, hc, hb, Nat.mul_assoc]

/-- The normal perfect A₅-by-two-core subgroup is the literal two-residual. -/
theorem hasA5TwoResidual_pResidual_eq {M : Type*} [Group M] [Finite M]
    (h : HasA5TwoResidual M) :
    ∃ B : Subgroup M, ∃ _hBN : B.Normal,
      B = pResidual 2 M ∧ Group.IsPerfect B ∧
        Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨B, hBN, hperfect, hA, hq⟩ := h
  let _ := hBN
  have hpp : IsPPerfect 2 B := perfect_isPPerfect 2
  have hres : pResidual 2 M = B :=
    pResidual_eq_of_isPPerfect B hpp hq
  exact ⟨B, hBN, hres.symm, hperfect, hA⟩

/-- The two-core and outer two-group contribute only powers of two to the order. -/
theorem hasA5TwoResidual_card {M : Type*} [Group M] [Finite M]
    (h : HasA5TwoResidual M) : ∃ a : ℕ, Nat.card M = 60 * 2 ^ a := by
  obtain ⟨B, hBN, hperfect, ⟨e⟩, hq⟩ := h
  let _ := hBN
  obtain ⟨a, ha⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_eq
  obtain ⟨b, hb⟩ := hq.exists_card_eq
  have hA : Nat.card (B ⧸ pCore 2 B) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hB := (pCore 2 B).card_mul_index
  rw [index_eq_card, hA, ha] at hB
  have hM := B.card_mul_index
  rw [index_eq_card, hb, ← hB] at hM
  refine ⟨a + b, ?_⟩
  rw [← hM, pow_add]
  ring

/-- Seven cannot divide the order of the actual local stabilizer. -/
theorem hasA5TwoResidual_not_seven_dvd {M : Type*} [Group M] [Finite M]
    (h : HasA5TwoResidual M) : ¬ 7 ∣ Nat.card M := by
  obtain ⟨a, ha⟩ := hasA5TwoResidual_card h
  rw [ha]
  intro hd
  rcases (by decide : Nat.Prime 7).dvd_mul.mp hd with hd | hd
  · norm_num at hd
  · have := (by decide : Nat.Prime 7).dvd_of_dvd_pow hd
    norm_num at this

/-- Every solvable quotient of the stabilizer is a two-group. -/
theorem hasA5TwoResidual_solvable_image {M D : Type*} [Group M] [Finite M]
    [Group D] [Group.IsSolvable D] (h : HasA5TwoResidual M)
    (f : M →* D) (hf : Function.Surjective f) : IsPGroup 2 D := by
  obtain ⟨B, hBN, hperfect, _, hq⟩ := h
  let _ := hBN
  let _ := hperfect
  have hker : B ≤ f.ker := by
    have hmap : B.map f = ⊥ := by
      let : Group.IsPerfect (B.map f) := Group.IsPerfect.map f
      by_contra hn
      let : Nontrivial (B.map f) := (Subgroup.nontrivial_iff_ne_bot _).mpr hn
      exact Group.IsPerfect.not_isSolvable (B.map f) inferInstance
    exact (map_eq_bot_iff B).mp hmap
  exact hq.of_surjective (QuotientGroup.lift B f hker)
    (QuotientGroup.lift_surjective_of_surjective B f hf hker)

end Nonquasisimple
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

end
