module
public import Theory.SpecificGroups.PSL3.OrdinaryCenterRecognition
/-!
# No defining-prime kernel over odd PSL₃

The proved Steinberg lift maps the actual SL₃ scalar cover onto every
perfect central cover of PSL₃ over an odd field. Its kernel order therefore
divides gcd(3,q−1), which is prime to the defining prime. This retains the
original covering homomorphism, rather than only its central quotient.

Source: Aschbacher–Smith I.1.3, used in the source reduction A.2.12,
printed pp.407 and35–36.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace Matrix.PSL3
variable {F : Type*} [Field F] [Finite F]
variable {L : Type*} [Group L] [Finite L]

omit [Finite L] in
theorem not_defining_prime_dvd_cover_kernel {p e : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : 0 < e) (hcard : Nat.card F = p ^ e) (c : Cover L PSL(3,F)) :
    ¬ p ∣ Nat.card c.toMonoidHom.ker := by
  let := c.isPerfect
  have hodd : Odd (Nat.card F) := hcard ▸ ho.pow
  have h2 : Nat.card F ≠ 2 := by intro hh; rw [hh] at hodd; norm_num at hodd
  have h4 : Nat.card F ≠ 4 := by intro hh; rw [hh] at hodd; norm_num at hodd
  obtain ⟨k, hk, _⟩ := UniversalProjection.existsUnique_lift_of_faithful
    c.toMonoidHom c.surjective c.ker_le_center h2 h4
    (UniversalProjection.matrixMap_injective h2 h4)
  have hks := projection_lift_surjective F c.toMonoidHom c.ker_le_center k hk
  have hd := kernel_card_dvd_of_surjective_factor (projection F) c.toMonoidHom k hks hk
  rw [card_projectionKernel] at hd
  intro hpk
  have hm : p ∣ Nat.card F - 1 := (hpk.trans hd).trans (Nat.gcd_dvd_right 3 _)
  have hc : p ∣ Nat.card F := hcard ▸ dvd_pow_self p (Nat.ne_of_gt he)
  have hpos : 1 ≤ Nat.card F := Nat.card_pos
  rw [← Nat.sub_add_cancel hpos] at hc
  exact hp.not_dvd_one ((Nat.dvd_add_iff_right hm).mpr hc)

end Matrix.PSL3
