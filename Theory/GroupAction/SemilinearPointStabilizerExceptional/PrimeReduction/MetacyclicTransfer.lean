module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.Normalizers
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.ScalarQuotients
public import Theory.GroupTheory.FocalTransfer
public import Theory.GroupTheory.WeakClosureFusion

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.MetacyclicTransfer.Stabilizer
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.MetacyclicTransfer.ScalarPrime
public import Theory.GroupAction.SemilinearPointStabilizerExceptional.PrimeReduction.MetacyclicTransfer.Supplement

/-!
# Coprimality from scalar transfer

Let B be the zero stabilizer, K its scalar subgroup, and Γ the literal
two-point stabilizer. For an odd prime p dividing |Γ|, choose a Sylow
p-subgroup R inside B. If p also divides |K|, the imported construction
supplies Z = Ω₁(R ∩ K), of order p, central in R and weakly closed in R.
Its unique fixed point puts its ambient normalizer inside B.

Weak-closure fusion and the focal subgroup theorem prove the actual
transfer-control equality R ∩ [X,X] = R ∩ [B,B]. The latter lies in K.
The finite supplement argument then contradicts [X,X]K = X, which follows
from scalar normal generation. Thus p is coprime to the scalar order.

Weak closure is proved directly using the unique fixed point of every
nonidentity scalar and invariance of scalar pth roots under B. This
replaces the printed conjugacy calculation for the other order-p subgroups;
the omega subgroup and transfer conclusion are the same. No field-degree,
transfer-control or coprimality premise is added. The larger source setup's
two-core and lower degree assumptions are unnecessary for this branch.

Source: GLS, Volume 4, Chapter 1, Lemma 3.9, first paragraph and the
Q < R branch, `refs/KGroup/GLS4/Chapter1.tex`, lines 433–443; fusion and
transfer are GLS2, Chapter D, Lemmas 16.9, 15.7 and 15.10.
-/

open scoped Pointwise commutatorElement

namespace MulAction.SemilinearPointStabilizer

open Coordinates

variable {X F : Type*} [Group X] [Finite X] [Field F]
  [MulAction X F] [FaithfulSMul X F]

namespace Coordinates

variable (c : Coordinates X F)

/-!
The displayed hypotheses use literal ambient subgroups.  In particular,
`hcomm` is the element form of `[X₀,X₀] ≤ K`; it is convenient here because
the focal generators are written as `x⁻¹ * n * x * n⁻¹`.
-/

/-- Weak closure of the scalar order-(p) subgroup forces focal transfer into
the scalar subgroup. -/
public theorem commutator_inf_sylow_le_scalar_of_weakly_closed
    {p : ℕ} [Fact p.Prime]
    (R : Sylow p X) (Z : Subgroup X)
    (hRB : (R : Subgroup X) ≤ stabilizer X (0 : F))
    (hZR : Z ≤ (R : Subgroup X))
    (hZcentral : (R : Subgroup X) ≤ Subgroup.centralizer (Z : Set X))
    (hweak : ∀ g : X,
      Z.map (MulAut.conj g).toMonoidHom ≤ (R : Subgroup X) →
        g ∈ Subgroup.normalizer (Z : Set X))
    (hnormalizer : Subgroup.normalizer (Z : Set X) ≤
      stabilizer X (0 : F))
    (hcomm : ∀ x : X, x ∈ stabilizer X (0 : F) →
      ∀ y : X, y ∈ stabilizer X (0 : F) →
        x⁻¹ * y * x * y⁻¹ ∈ c.scalarSubgroup) :
    commutator X ⊓ (R : Subgroup X) ≤ c.scalarSubgroup := by
  have hfocal : (R : Subgroup X).focalSubgroup ≤ c.scalarSubgroup := by
    rw [Subgroup.focalSubgroup_def]
    rw [Subgroup.closure_le]
    rintro z ⟨x, hx, y, hy, hxy, rfl⟩
    obtain ⟨n, hn, hconj⟩ :=
      Sylow.weakly_closed_normalizer_controls_fusion R Z hZR hZcentral hweak hx hy hxy
    have hn0 : n ∈ stabilizer X (0 : F) := hnormalizer hn
    have hx0 : x ∈ stabilizer X (0 : F) := hRB hx
    have hxy0 := hcomm x hx0 n hn0
    rw [← hconj]
    change x⁻¹ * (n * x * n⁻¹) ∈ c.scalarSubgroup
    simpa only [mul_assoc] using hxy0
  rw [Subgroup.commutator_inf_eq_focalSubgroup R]
  exact hfocal

end Coordinates

end MulAction.SemilinearPointStabilizer

namespace MulAction.SemilinearPointStabilizer.Coordinates
open scoped commutatorElement
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
variable [MulAction X F] [FaithfulSMul X F] (c : Coordinates X F)

include c in
/-- The zero stabilizer controls p-transfer when p divides the scalar order.
Both commutator intersections are literal subgroups of the original actor. -/
public theorem stabilizer_controls_transfer_of_scalar_divisor
    {p : ℕ} [Fact p.Prime] (hpK : p ∣ Nat.card F - 1)
    (R : Sylow p X) (hRB : (R : Subgroup X) ≤ stabilizer X (0 : F)) :
    commutator X ⊓ (R : Subgroup X) =
      ⁅stabilizer X (0 : F), stabilizer X (0 : F)⁆ ⊓ (R : Subgroup X) := by
  obtain ⟨Z, hcard, hZK, hZR, _, hcentral, hweak⟩ :=
    c.exists_central_weakly_closed_scalar hpK R hRB
  have hne : Z ≠ ⊥ := by
    intro h
    have h1 : Nat.card Z = 1 := by rw [h]; exact Subgroup.card_bot
    exact (Fact.out : p.Prime).ne_one (hcard.symm.trans h1)
  have hn := c.scalar_normalizer_le_stabilizer hZK hne
  apply le_antisymm
  · refine le_inf ?_ inf_le_right
    rw [Subgroup.commutator_inf_eq_focalSubgroup R, Subgroup.focalSubgroup_def,
      Subgroup.closure_le]
    rintro z ⟨x, hx, y, hy, hxy, rfl⟩
    obtain ⟨n, hnZ, hconj⟩ :=
      Sylow.weakly_closed_normalizer_controls_fusion R Z hZR hcentral hweak hx hy hxy
    have hmem := Subgroup.commutator_mem_commutator
      ((stabilizer X (0 : F)).inv_mem (hRB hx)) (hn hnZ)
    rw [← hconj]
    change x⁻¹ * (n * x * n⁻¹) ∈ ⁅stabilizer X (0 : F), stabilizer X (0 : F)⁆
    simpa only [commutatorElement_def, inv_inv, mul_assoc] using hmem
  · exact inf_le_inf_right _ (Subgroup.commutator_mono le_top le_top)
end MulAction.SemilinearPointStabilizer.Coordinates

namespace MulAction.SemilinearPointStabilizer.Coordinates
variable {X F : Type*} [Group X] [Finite X] [Field F] [Finite F]
variable [MulAction X F] [FaithfulSMul X F] (c : Coordinates X F)

/-- The scalar-divisibility branch of GLS4 Lemma 3.9: every odd coefficient
prime is coprime to the scalar order. All transfer and omega premises are discharged. -/
public theorem coprime_scalar_order_of_odd_coefficient_prime {n p : ℕ}
    (hp : p.Prime) (hodd : Odd p)
    (htwo : IsMultiplyPretransitive X F 2) (hF : Nat.card F = 2 ^ n)
    (hgen : c.scalarClosure = ⊤)
    (hpΓ : p ∣ Nat.card (twoPoint (X := X) (F := F))) :
    p.Coprime (Nat.card F - 1) := by
  let : Fact p.Prime := ⟨hp⟩
  apply hp.coprime_iff_not_dvd.mpr
  intro hpK
  obtain ⟨R, hRB⟩ := exists_sylow_le_stabilizer hp hodd htwo hF
  have hfocal : commutator X ⊓ (R : Subgroup X) ≤ c.scalarSubgroup := by
    rw [c.stabilizer_controls_transfer_of_scalar_divisor hpK R hRB]
    exact inf_le_left.trans c.ambient_stabilizer_commutator_le_scalar
  exact c.scalarClosure_ne_top_of_focal_containment R hpΓ hfocal hgen

end MulAction.SemilinearPointStabilizer.Coordinates
