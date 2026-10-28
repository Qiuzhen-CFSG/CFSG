module

public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Prime-kernel dichotomy for compatible central-cover lifts

Suppose `L → B` is surjective with kernel of order dividing a prime. A
compatible map from `L` to a perfect central extension `M → B` is surjective:
its image supplements the central kernel, and perfectness removes that
kernel from the abelian quotient. Its own kernel is either trivial or the
whole kernel of `L → B`. The first isomorphism theorem therefore identifies
`M` with `L` or with `B`.

This is the elementary assembly step after the universal-cover calculation
in GLS, Volume 4, Chapter 4, Lemma 2.8(a). The existence of the compatible
lift is a separate input; this theorem asserts no multiplier calculation.
-/

namespace PerfectCentralCovering
open Subgroup

/-- A compatible lift from a cover of prime or trivial degree has only the
base and the source as possible perfect central images. -/
public theorem nonempty_mulEquiv_or_of_prime_kernel_lift
    {L M B : Type*} [Group L] [Finite L] [Group M] [Group B]
    [Group.IsPerfect M]
    (f : L →* B) (hf : Function.Surjective f)
    (g : M →* B) (hg : g.ker ≤ center M)
    (h : L →* M) (hh : g.comp h = f)
    {p : ℕ} (hp : p.Prime) (hcard : Nat.card f.ker ∣ p) :
    Nonempty (M ≃* B) ∨ Nonempty (M ≃* L) := by
  have hs : Function.Surjective h :=
    surjective_of_comp_surjective_of_ker_le_center_of_isPerfect g h (hh ▸ hf) hg
  have hle : h.ker ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, ← hh]
    simp only [MonoidHom.comp_apply, MonoidHom.mem_ker.mp hx, map_one]
  rcases (Nat.dvd_prime hp).mp ((card_dvd_of_le hle).trans hcard) with hc | hc
  · exact Or.inr ⟨(MulEquiv.ofBijective h
      ⟨h.ker_eq_bot_iff.mp ((eq_bot_iff_card h.ker).mpr hc), hs⟩).symm⟩
  · have hk : h.ker = f.ker := eq_of_le_of_card_ge hle (by
      rw [hc]
      exact Nat.le_of_dvd hp.pos hcard)
    exact Or.inl ⟨(QuotientGroup.quotientKerEquivOfSurjective h hs).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hk).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hf))⟩

end PerfectCentralCovering
