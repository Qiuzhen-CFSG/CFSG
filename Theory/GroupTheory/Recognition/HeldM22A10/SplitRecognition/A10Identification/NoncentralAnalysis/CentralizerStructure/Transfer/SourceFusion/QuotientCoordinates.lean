module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Transfer.SourceFusion.LocalCoordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Core

/-!
# Embedding the finite model in the actual central quotient

The local representatives give an injective homomorphism into C_G(mu)/<mu>.
The centralizer order makes its image exactly C_Q(p), and therefore Sylow.
No ambient fusion or choice of lambda and xi is asserted here.

Source: Held, Illinois J. Math. 13 (1969), p.233.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.SourceFusion
open TransferModel (Model)
noncomputable section
universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

@[expose] public def lift (x : Model) : C D e :=
  ⟨D.a10ModelEmbedding e (Local.liftWord x), mem_centralizer_singleton_iff.mpr (by
    change D.a10ModelEmbedding e (Local.liftWord x) * D.a10ModelEmbedding e Coordinates.mu = _
    simpa only [map_mul, LocalData.a10NoncentralInvolution, Coordinates.mu] using
      congrArg (D.a10ModelEmbedding e) (Local.liftWord_commutes x))⟩

public theorem q_eq_of_eq_or_mu_mul (x y : C D e) (h : x = y ∨ x = mu D e * y) :
    q D e x = q D e y := by
  rcases h with rfl | rfl
  · rfl
  · rw [map_mul]
    have hmu : q D e (mu D e) = 1 := (QuotientGroup.eq_one_iff _).mpr (mem_zpowers _)
    rw [hmu, one_mul]

@[expose] public def into : Model →* Q D e where
  toFun x := q D e (lift D e x)
  map_one' := by
    have h : Local.liftWord 1 = 1 := by decide +kernel
    have hl : lift D e 1 = 1 := Subtype.ext (by change D.a10ModelEmbedding e _ = 1; rw [h, map_one])
    rw [hl, map_one]
  map_mul' x y := by
    rw [← map_mul]
    apply Eq.symm
    apply q_eq_of_eq_or_mu_mul
    rcases Local.liftWord_mul x y with h | h
    · left
      apply Subtype.ext
      simpa only [lift, Subgroup.coe_mul, ← map_mul] using congrArg (D.a10ModelEmbedding e) h
    · right
      apply Subtype.ext
      simpa only [lift, mu, LocalData.a10NoncentralInvolution, Subgroup.coe_mul, ← map_mul] using
        congrArg (D.a10ModelEmbedding e) h

public theorem eq_or_mu_mul_of_q_eq [Finite G] (x y : C D e) (h : q D e x = q D e y) :
    x = y ∨ x = mu D e * y := by
  classical
  have hz : x * y⁻¹ ∈ Z D e := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q D e (x * y⁻¹) = 1
    rw [map_mul, map_inv, h, mul_inv_cancel]
  rw [Z, mem_zpowers_iff_mem_range_orderOf, mu_order] at hz
  simp only [Finset.mem_image, Finset.mem_range] at hz
  obtain ⟨k, hk, heq⟩ := hz
  interval_cases k
  · left
    exact mul_inv_eq_one.mp (by simpa using heq.symm)
  · right
    exact eq_mul_of_mul_inv_eq (by simpa using heq.symm)

public theorem into_injective [Finite G] : Function.Injective (into D e) := by
  intro x y h
  apply Local.liftWord_injective_mod_mu
  rcases eq_or_mu_mul_of_q_eq D e (lift D e x) (lift D e y) h with h | h
  · left
    apply D.a10ModelEmbedding_injective e
    exact congrArg (fun v : C D e => (v : G)) h
  · right
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul, lift, mu, LocalData.a10NoncentralInvolution, Subgroup.coe_mul, Coordinates.mu] using congrArg Subtype.val h

public theorem into_p [Finite G] : into D e TransferModel.p = p D e := by
  change q D e (lift D e TransferModel.p) = q D e (pi D e)
  congr 1
  apply Subtype.ext
  change D.a10ModelEmbedding e (Local.liftWord TransferModel.p) = D.z
  rw [Local.liftWord_p, LocalData.a10ModelEmbedding_central]

public theorem into_mem_centralizer [Finite G] (x : Model) :
    into D e x ∈ centralizer ({p D e} : Set (Q D e)) := by
  apply mem_centralizer_singleton_iff.mpr
  rw [← into_p D e, ← map_mul, ← map_mul]
  congr 1
  have h : ∀ x : Model, x * TransferModel.p = TransferModel.p * x := by decide +kernel
  exact h x

public theorem into_range [Finite G] (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) :
    (into D e).range = centralizer ({p D e} : Set (Q D e)) := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x, rfl⟩
    exact into_mem_centralizer D e x
  · rw [centralizer_p_card D e hfusion, ← Nat.card_congr (MonoidHom.ofInjective (into_injective D e)).toEquiv]
    rw [Nat.card_eq_fintype_card]
    decide +kernel

/-- The concrete quotient words identify the actual centralizer of p. -/
public def centralizerCoordinates [Finite G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) :
    Model ≃* centralizer ({p D e} : Set (Q D e)) :=
  (MonoidHom.ofInjective (into_injective D e)).trans
    (MulEquiv.subgroupCongr (into_range D e hfusion))

public theorem centralizerCoordinates_apply [Finite G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e)) (x : Model) :
    (centralizerCoordinates D e hfusion x : Q D e) = into D e x := by
  rfl

end
end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.SourceFusion
