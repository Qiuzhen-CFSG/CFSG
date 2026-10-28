module
public import Theory.GroupTheory.SylowNormalIntersection


/-!
# Kernels detected on one Sylow subgroup

The intersection of a normal kernel with a Sylow subgroup is Sylow in the
kernel. Triviality of that intersection proves coprimality of the kernel's
order. This retains the entire kernel: it need not be trivial.
-/

public section
open Subgroup
namespace MonoidHom
variable {G H : Type*} [Group G] [Finite G] [Group H]

/-- Faithfulness on a Sylow p-subgroup gives a kernel of order prime to p. -/
theorem coprime_card_ker_of_sylow {p : ℕ} [hp : Fact p.Prime]
    (f : G →* H) (S : Sylow p G)
    (hS : ∀ s ∈ (S : Subgroup G), f s = 1 → s = 1) :
    Nat.Coprime p (Nat.card f.ker) := by
  apply hp.out.coprime_iff_not_dvd.mpr
  intro hdvd
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal f.ker
  apply T.ne_bot_of_dvd_card hdvd
  rw [hT]
  apply bot_unique
  intro x hx
  exact Subtype.ext (hS x hx x.property)

end MonoidHom
