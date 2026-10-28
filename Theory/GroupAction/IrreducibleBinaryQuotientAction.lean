module

public import Theory.GroupAction.IrreducibleBinaryInvolution
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# Involutions detected by an irreducible binary action

Suppose K acts irreducibly on an elementary abelian two-group V and its
action factors through a characteristic quotient K/W. Compatible actions
on K and V send an involution trivial on K/W to an automorphism centralizing
the K-action. The irreducible binary fixed-point argument makes it trivial
on V. All actions and the quotient projection remain explicit.

This is the faithfulness transfer in the hyperplane TI-pair argument of
Aschbacher--Smith13.1.14, printed p.876.
-/

public section
open Subgroup

/-- An involution trivial on a detecting characteristic quotient fixes an
irreducible binary module. -/
theorem action_eq_one_of_quotient_eq_one_of_irreducible_binary
    {K E V : Type*} [Group K] [Group E] [Group V] [IsElementaryAbelian 2 V]
    (W : Subgroup K) [W.Characteristic]
    (τ : K →* MulAut V) (hW : W ≤ τ.ker)
    (hirr : ∀ D : Subgroup V,
      (∀ k v, v ∈ D → τ k v ∈ D) → D = ⊥ ∨ D = ⊤)
    (ρ : E →* MulAut K) (σ : E →* MulAut V)
    (he : ∀ a k v, σ a (τ k v) = τ (ρ a k) (σ a v))
    (a : E) (ha : a ^ 2 = 1) (hq : quotientAut W (ρ a) = 1) : σ a = 1 := by
  let φ := QuotientGroup.lift W τ hW
  have hs (k : K) : τ (ρ a k) = τ k := by
    have h := DFunLike.congr_fun hq (QuotientGroup.mk' W k)
    rw [quotientAut_apply_mk] at h
    exact congrArg φ h
  let : MulDistribMulAction K V := MulDistribMulAction.compHom V τ
  have hfix := fixes_of_sq_eq_one_of_commuting_irreducible_binary
    (A := K) (T := MulAut V) (W := V) (σ a)
    (by rw [← map_pow,ha,map_one])
    (fun k v => by change τ k (σ a v) = σ a (τ k v); rw [he,hs])
    (fun D hD => hirr D (fun k v hv => hD.invariant k v |>.mp hv))
  exact MulEquiv.ext hfix
