module

public import Theory.SpecificGroups.AlternatingSix.TwoCoverInvolutions
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.CentralExtensionCommutingPair

/-!
# Two-primary involution data for A₆

The center bound dividing six reduces a perfect central two-cover of A₆ to
its trivial or double-cover case. The existing Schur-lift square calculation
then puts every square-one element of the double cover in its central kernel.
This packages the universal finite-cover input to the native M₂₂ hexad lift.

Source: GLS3 5.2.3–4 and Aschbacher–Smith I.2.2(6), printed p.412.
-/

public section
namespace AlternatingSix
open PerfectCentralCovering Subgroup Theory.GroupTheory GLS3.Chapter5
universe u

/-- Every finite perfect central two-cover of A₆ has trivial kernel, or kernel
of order two containing every square-one element. -/
theorem twoPrimaryInvolutionData :
    CentralExtension.TwoPrimaryInvolutionData.{u} (alternatingGroup (Fin 6)) := by
  intro D _ _ c hp
  let : IsQuasisimple (alternatingGroup (Fin 6)) := SchurPresentation.alternatingGroup_isQuasisimple 1
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple D := c.isQuasisimple
  let f := c.toCovering
  have hk : c.toMonoidHom.ker = center D := f.ker_eq_center_of_isSimple
  let e : D ⧸ center D ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective c.toMonoidHom c.surjective)
  have hd : Nat.card c.toMonoidHom.ker ∣ 6 := by
    rw [hk]
    exact exceptional_alternating_center_card_dvd_six 6 e (Or.inl rfl)
  obtain ⟨k, he⟩ := hp.exists_card_eq
  have hcop : (Nat.card c.toMonoidHom.ker).Coprime 3 := by
    rw [he]
    exact (by decide : Nat.Coprime 2 3).pow_left k
  have htwo : Nat.card c.toMonoidHom.ker ∣ 2 := hcop.dvd_mul_right.mp hd
  rcases (Nat.dvd_prime Nat.prime_two).mp htwo with h1 | h2
  · exact Or.inl (Subgroup.card_eq_one.mp h1)
  · exact Or.inr ⟨h2, fun x hx =>
      AlternatingSix.TwoCoverInvolutions.involution_mem_ker_of_double_cover f h2 x hx⟩

end AlternatingSix
