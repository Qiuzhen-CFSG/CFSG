module

public import Theory.SpecificGroups.SL2.TwoConjugateWitness.Transport
public import CFSG.Quasithin.ChapterE.Section02.Witnesses.QuotientLift

/-!
# The genuine linear-two E.2.7 witness

The actual binary SL₂ model constructs two conjugates of the original
noncyclic elementary subgroup, with an internal conjugator, the original
Sylow intersection and the original Borel intersection. Its Borel core is
trivial. This module applies that construction to the geometric `Pair`
consumed by the maximal-core quotient lift, retaining the full field model
and the exact Borel image for the E.2.4 linear alternative.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.2.7,
printed p.218, the linear Bender branch. No recognition or generation output
is a premise. The general E.2.2 model selection belongs to the assembly.
-/

@[expose] public section
noncomputable section
open Subgroup Matrix
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Witnesses.LinearTwo
open Matrix.SpecialLinearGroup.TwoConjugateWitness
variable {G : Type*} [Group G] [Finite G]

/-- Retain the selected linear model and its exact source pair together. -/
structure Witness (S : Sylow 2 G) (M V : Subgroup G) (n : ℕ) where
  pair : QuotientLift.Pair S M V
  degree : ℕ
  degree_gt_one : 1 < degree
  degree_dvd : degree ∣ n
  model : pair.subgroup ≃* SL(2,GaloisField 2 degree)
  sylow_model : (pair.sylow : Subgroup pair.subgroup).map model.toMonoidHom =
    SpecialLinearGroup.upperUnipotent (GaloisField 2 degree)
  borel_model : (M.subgroupOf pair.subgroup).map model.toMonoidHom =
    SpecialLinearGroup.rankOneBorel (GaloisField 2 degree)
  corefree : (M.subgroupOf pair.subgroup).normalCore = ⊥

def of_model_witness {S : Sylow 2 G} {M V : Subgroup G} {n : ℕ}
    (w : Matrix.SpecialLinearGroup.TwoConjugateWitness.Witness
      (S : Subgroup G) M V n) : Witness S M V n := by
  have hclosed : ∃P : Sylow 2 (M.subgroupOf w.subgroup).normalCore,
      (P : Subgroup (M.subgroupOf w.subgroup).normalCore).Normal := by
    rw [w.corefree]
    exact ⟨default,inferInstance⟩
  let q : QuotientLift.Pair S M V :=
    ⟨w.subgroup,w.le,w.conjugator,w.generate,w.sylow,by
      rw [w.sylow_eq,subgroupOf_map_subtype],hclosed⟩
  exact ⟨q,w.degree,w.degree_gt_one,w.degree_dvd,w.model,w.sylow_model,w.borel_model,w.corefree⟩

/-- E.2.7's linear Bender branch on the original Sylow and original V. -/
theorem exists_witness {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (e : G ≃* SL(2,F))
    (S : Sylow 2 G) (V : Subgroup G) (hVS : V ≤ S) (hVc : 4 ≤ Nat.card V) :
    Nonempty (Witness S (normalizer (S : Set G)) V n) := by
  obtain ⟨w⟩ := exists_of_equiv hF e S V hVS hVc
  exact ⟨of_model_witness w⟩

/-- The field degree dominates the binary rank of the original generator. -/
theorem Witness.rank_le_degree {S : Sylow 2 G} {M V : Subgroup G} {n : ℕ}
    [IsElementaryAbelian 2 V] (w : Witness S M V n)
    (hVS : V ≤ S) : Module.finrank (ZMod 2) (Additive V) ≤ w.degree := by
  have hP : (w.pair.sylow : Subgroup w.pair.subgroup) =
      (S : Subgroup G).subgroupOf w.pair.subgroup := by
    apply Subgroup.map_injective w.pair.subgroup.subtype_injective
    rw [w.pair.sylow_eq,subgroupOf_map_subtype]
  have hVP : V.subgroupOf w.pair.subgroup ≤ (w.pair.sylow : Subgroup w.pair.subgroup) := by
    rw [hP]
    exact comap_mono hVS
  have hcV : Nat.card V = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
    rw [Nat.card_congr Additive.ofMul]
    simpa only [Nat.card_zmod] using
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
  have hcP : Nat.card w.pair.sylow = 2^w.degree := by
    have hm : Nat.card (w.pair.sylow : Subgroup w.pair.subgroup) =
        Nat.card (SpecialLinearGroup.upperUnipotent (GaloisField 2 w.degree)) := by
      rw [← w.sylow_model,Subgroup.card_map_of_injective w.model.injective]
    exact hm.trans ((SpecialLinearGroup.card_upperUnipotent _).trans
      (GaloisField.card 2 w.degree (by have := w.degree_gt_one; omega)))
  have hv : Nat.card V ≤ Nat.card w.pair.sylow := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe w.pair.le).toEquiv]
    exact card_le_of_le hVP
  rw [hcV,hcP] at hv
  exact (Nat.pow_le_pow_iff_right (by decide)).mp hv

/-- The source binary-rank formulation of the linear Bender branch. -/
theorem exists_witness_of_rank {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2^n) (e : G ≃* SL(2,F))
    (S : Sylow 2 G) (V : Subgroup G) [IsElementaryAbelian 2 V]
    (hVS : V ≤ S) (hVr : 2 ≤ Module.finrank (ZMod 2) (Additive V)) :
    ∃ w : Witness S (normalizer (S : Set G)) V n,
      Module.finrank (ZMod 2) (Additive V) ≤ w.degree := by
  have hc : 4 ≤ Nat.card V := by
    have he : Nat.card V = 2 ^ Module.finrank (ZMod 2) (Additive V) := by
      rw [Nat.card_congr Additive.ofMul]
      simpa only [Nat.card_zmod] using
        Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [he]
    exact (show 2^2 ≤ 2^Module.finrank (ZMod 2) (Additive V) from
      Nat.pow_le_pow_right (by decide) hVr)
  obtain ⟨w⟩ := exists_witness hF e S V hVS hc
  exact ⟨w,w.rank_le_degree hVS⟩

end CFSG.Quasithin.ChapterE.Witnesses.LinearTwo
