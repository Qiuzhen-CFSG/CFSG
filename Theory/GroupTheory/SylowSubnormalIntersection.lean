module

public import Theory.GroupTheory.SylowNormalIntersection
public import Mathlib.GroupTheory.IsSubnormal

/-!
# Sylow restriction to subnormal subgroups

Intersect a Sylow subgroup successively with the normal inclusions in a
subnormal chain. Transport across the subgroup inclusion equivalence gives
an intrinsic Sylow subgroup of the original subnormal subgroup.

This is the standard Sylow restriction used in GLS, Volume 1, (4.6), and
Volume 4, Chapter 2, Lemma 4.9.
-/

open Subgroup

/-- A supplied Sylow subgroup meets a subnormal subgroup in a Sylow subgroup. -/
public theorem Sylow.exists_subgroupOf_eq_of_subnormal
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (N : Subgroup G) (hN : N.IsSubnormal) :
    ∃ T : Sylow p N, (T : Subgroup N) = (S : Subgroup G).subgroupOf N := by
  induction hN with
  | top =>
    exact ⟨S.subtype le_top, rfl⟩
  | step N K hNK hK hn ih =>
    obtain ⟨T, hT⟩ := ih
    let := hn
    obtain ⟨Q, hQ⟩ := T.exists_subgroupOf_eq_of_normal (N.subgroupOf K)
    let e := Subgroup.subgroupOfEquivOfLe hNK
    refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
    change (Q : Subgroup _).map e.toMonoidHom = _
    rw [hQ, hT]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨⟨x, hNK x.property⟩, x.property⟩, hx, rfl⟩
