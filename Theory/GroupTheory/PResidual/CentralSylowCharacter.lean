module

public import Theory.GroupTheory.PResidual.Defs
public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Sylow

/-!
# Central elements of the prime residual under Sylow characters

A homomorphism from a Sylow p-subgroup to an abelian p-group vanishes on
central elements of Oᵖ(G). Transfer extends the character to G, and its
kernel contains the residual. On a central element transfer is the
Sylow-index power; that power is injective in a p-group.

This is the transfer step for the central factor E in Aschbacher–Smith,
proof of 13.9.1, printed pp.973–974. Centrality is in C_G(E), not in its
two-residual; the application proves that their intersection is trivial.
-/

public section

namespace Sylow

open Subgroup

variable {G A : Type*} [Group G] [Finite G] [CommGroup A]
  {p : ℕ} [Fact p.Prime]

/-- A Sylow character kills every central element in the ambient p-residual. -/
theorem character_eq_one_of_central_mem_pResidual
    (S : Sylow p G) (f : S →* A) (hA : IsPGroup p A) (x : S)
    (hc : (x : G) ∈ center G) (hr : (x : G) ∈ pResidual p G) : f x = 1 := by
  have hq : IsPGroup p (G ⧸ f.transfer.ker) :=
    (hA.of_injective f.transfer.range.subtype f.transfer.range.subtype_injective).of_equiv
      (QuotientGroup.quotientKerEquivRange f.transfer).symm
  have hk : pResidual p G ≤ f.transfer.ker := sInf_le ⟨inferInstance, hq⟩
  have ht : f.transfer (x : G) = 1 := hk hr
  have he : f.transfer (x : G) = f (x ^ S.index) :=
    MonoidHom.transfer_eq_pow f (x : G) (fun k g _ => by
      rw [mem_center_iff.mp ((center G).pow_mem hc k) g⁻¹,
        mul_assoc, inv_mul_cancel, mul_one])
  rw [he, map_pow] at ht
  exact (hA.powEquiv' S.not_dvd_index).injective (by simpa using ht)

end Sylow
