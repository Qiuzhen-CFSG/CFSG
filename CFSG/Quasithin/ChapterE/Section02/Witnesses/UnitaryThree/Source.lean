module

public import Theory.SpecificGroups.SU3.TwoConjugateWitness.Witness
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.LinearTwo.Source
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# The original unitary-three E.2.7 branch

The actual unitary model's central elementary subgroup gives the linear
E.2.4 alternative. The source witness retains the original ambient Sylow,
its exact normalizer intersection and trivial core, and one SL₂ isomorphism
identifying both the generated subgroup and its Borel. Its `pair` is directly
consumable by the original E.2.9 quotient-lift theorem.

Source: Aschbacher--Smith E.2.7, printed p.218, Bender-group paragraph.
The rank-one subgroup is constructed inside PSU₃; no recognition or
subgroup-witness premise is assumed.
-/

public section
noncomputable section
open Subgroup Matrix BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.Witnesses.UnitaryThree
private instance {E : Type*} [Field E] [Finite E] : Finite (ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective

/-- The unitary Bender branch on the literal original Sylow and central
noncyclic elementary subgroup, with the full marked linear model. -/
theorem source_witness {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (V : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) [IsElementaryAbelian 2 V]
    (hVZ : V ≤ (center S).map (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype)
    (hrank : 1 < primeRank 2 V) :
    Nonempty (LinearTwo.Witness S (normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J))) V n) := by
  have hcardV : 4 ≤ Nat.card V := by
    by_contra hn
    obtain ⟨a, ha⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
    have hle : Nat.card V ≤ 2 := by
      have hp : 2 ^ a < 4 := ha ▸ Nat.lt_of_not_ge hn
      have : a ≤ 1 := by
        by_contra h
        have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 2 ≤ a)
        norm_num at hh
        omega
      rw [ha]
      exact (Nat.pow_le_pow_right (by decide : 0 < 2) this).trans_eq (by norm_num)
    have hr := IsElementaryAbelian.primeRank_le_of_card_le (p := 2) (n := 1) V
      (by simpa only [pow_one] using hle)
    omega
  obtain ⟨w⟩ := HermitianForm.TwoConjugateWitness.exists_unitary_witness
    J hJ hn hcard hfixed S V hVZ hcardV
  exact ⟨LinearTwo.of_model_witness w⟩

end CFSG.Quasithin.ChapterE.Witnesses.UnitaryThree
end
