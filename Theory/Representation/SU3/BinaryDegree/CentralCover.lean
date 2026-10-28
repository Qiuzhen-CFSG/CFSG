module

public import Theory.Representation.BinaryPrimeDegree
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Prime divisors in nontrivial actions of perfect central covers

Let a perfect finite group cover a simple group with central kernel. The
kernel of any nontrivial representation is contained in the covering kernel:
its image in the simple quotient is either trivial or the whole quotient,
and the latter would make the representation image abelian. Consequently the
faithful action quotient still maps onto the simple group. Every odd prime
dividing that group's order gives the usual binary multiplicative-order bound.

This is the group-theoretic reduction for the SU₃ degree minimum used on
printed p.356 of Aschbacher--Smith, *The Classification of Quasithin Groups*.
It includes representations factoring through the projective group and does
not require irreducibility. Perfectness is an explicit input here; it must be
established for the concrete special unitary group in the final application.
-/

public section

open Subgroup

namespace Representation.SU3.BinaryDegree

/-- A nontrivial homomorphism from a perfect central cover of a simple group
has kernel contained in the covering kernel. -/
theorem ker_le_of_perfect_central_cover
    {G S M : Type*} [Group G] [Group S] [Monoid M]
    [Group.IsPerfect G] [IsSimpleGroup S]
    (π : G →* S) (hπ : Function.Surjective π)
    (hcentral : π.ker ≤ center G)
    (f : G →* M) (hf : ∃ g, f g ≠ 1) : f.ker ≤ π.ker := by
  let : (f.ker.map π).Normal := (inferInstance : f.ker.Normal).map π hπ
  rcases (inferInstance : (f.ker.map π).Normal).eq_bot_or_eq_top with hb | ht
  · intro x hx
    have hx' : π x ∈ f.ker.map π := mem_map_of_mem π hx
    simpa only [hb, mem_bot, MonoidHom.mem_ker] using hx'
  · have hcomap := congrArg (Subgroup.comap π) ht
    have hs : f.ker ⊔ π.ker = ⊤ := by
      simpa only [comap_map_eq, comap_top, sup_comm] using hcomap
    have hs' : f.ker ⊔ center G = ⊤ :=
      top_unique (hs ▸ sup_le_sup_left hcentral f.ker)
    have hc := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
      hs' (inferInstance : IsMulCommutative (center G))
    have hfker : f.ker = ⊤ := top_unique (by simpa using hc)
    obtain ⟨g, hg⟩ := hf
    exact (hg (MonoidHom.mem_ker.mp (hfker ▸ mem_top g))).elim

/-- Every odd prime in the simple quotient bounds the dimension of every
nontrivial binary action of its perfect central cover. -/
theorem orderOf_le_finrank_of_perfect_central_cover
    {G S V : Type*} [Group G] [Finite G] [Group S] [Finite S]
    [Group.IsPerfect G] [IsSimpleGroup S]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (π : G →* S) (hπ : Function.Surjective π) (hcentral : π.ker ≤ center G)
    (ρ : Representation (ZMod 2) G V) (hρ : ∃ g, ρ g ≠ 1)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hdiv : p ∣ Nat.card S) :
    orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V := by
  have hker := ker_le_of_perfect_central_cover π hπ hcentral ρ hρ
  let π' : G ⧸ ρ.ker →* S := QuotientGroup.lift ρ.ker π hker
  have hπ' : Function.Surjective π' := by
    intro s
    obtain ⟨g, rfl⟩ := hπ s
    exact ⟨QuotientGroup.mk' ρ.ker g, rfl⟩
  exact Representation.BinaryPrimeDegree.orderOf_le_finrank
    (QuotientGroup.lift ρ.ker ρ le_rfl)
    ((QuotientGroup.injective_lift_iff ρ.ker ρ le_rfl).mpr rfl) hp hp2
    (hdiv.trans (Subgroup.card_dvd_of_surjective π' hπ'))

end Representation.SU3.BinaryDegree
