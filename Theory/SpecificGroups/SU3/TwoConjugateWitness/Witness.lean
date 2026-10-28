module
public import Theory.SpecificGroups.SU3.TwoConjugateWitness.MarkedBlock
public import Theory.SpecificGroups.SL2.TwoConjugateWitness.Transport

/-!
# The unitary central-root two-conjugate witness

Construct the marked SL₂ block through the original unitary Sylow center,
then apply the proved linear witness inside this same block. Its injective
inclusion preserves the original Sylow and Borel exactly by the marked-block
identities. This transports the internal conjugator, its actual generated
subgroup, the subfield parameter and the core-free Borel simultaneously.

Source: Aschbacher--Smith E.2.7, printed p.218, Bender-group paragraph.
No block, recognition, Sylow conclusion or pair is an additional premise.
-/

public section
noncomputable section
open Subgroup Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.TwoConjugateWitness
private instance {E : Type*} [Field E] [Finite E] : Finite (ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective

/-- The full linear E.2.4 model arising from the original central unitary
subgroup, with every marking transported through its actual inclusion. -/
theorem exists_unitary_witness {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (V : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hVZ : V ≤ (center S).map (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype)
    (hVc : 4 ≤ Nat.card V) :
    Nonempty (Matrix.SpecialLinearGroup.TwoConjugateWitness.Witness
      (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
      (normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J))) V n) := by
  let := Fintype.ofFinite E
  let : CharP E 2 := by
    apply charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
    simpa only [Nat.card_eq_fintype_card, pow_mul] using hcard
  have hVne : V ≠ ⊥ := by intro he; rw [he, card_bot] at hVc; omega
  have hZne : (center S).map (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).subtype ≠ ⊥ := by
    intro he
    exact hVne (bot_unique (he ▸ hVZ))
  obtain ⟨b⟩ := exists_marked_block J hJ hn hcard hfixed S hZne
  have hVL : V ≤ b.subgroup := by
    rw [← b.center_eq] at hVZ
    exact hVZ.trans (map_subtype_le _)
  let U := V.subgroupOf b.subgroup
  have hUP : U ≤ b.sylow := by
    rw [b.sylow_eq]
    exact comap_mono (hVZ.trans (map_subtype_le _))
  have hUc : 4 ≤ Nat.card U := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv]
    exact hVc
  obtain ⟨w⟩ := Matrix.SpecialLinearGroup.TwoConjugateWitness.exists_of_equiv
    (GaloisField.card 2 n (by omega)) b.equiv b.sylow U hUP hUc
  have hh := w.map b.subgroup.subtype b.subgroup.subtype_injective
    (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (normalizer (S : Set (ProjectiveSpecialUnitaryMatrixGroup J)))
    b.sylow_eq.symm b.normalizer_eq.symm
  have hU : U.map b.subgroup.subtype = V := map_subgroupOf_eq_of_le hVL
  exact hU ▸ ⟨hh⟩
end BenderSuzuki.MatrixGroups.HermitianForm.TwoConjugateWitness
end
