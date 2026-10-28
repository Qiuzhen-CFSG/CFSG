module

public import Theory.GroupAction.AutomorphismFixedTransport
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Solvable

/-!
# Outer automorphisms and self-centralizing normal subgroups

For a normal subgroup `N` of `G`, conjugation has kernel `C_G(N)`, and
its preimage of `Inn(N)` is `N C_G(N)`. Consequently `G/N` embeds in
`Aut(N)/Inn(N)` when `C_G(N) = 1`. Solvability of this actual outer
quotient therefore implies solvability of `G/N`.

The construction uses the normal subgroup inside `G` and its actual quotient;
it requires neither a splitting nor any simplicity or finiteness hypothesis.
An actual multiplicative equivalence also transports outer automorphism groups.

This is the elementary automorphism reduction used in the final extension
argument of GLS3, Theorem 6.5.3 (`refs/KGroup/GLS3/chapter6.tex`). No
classification or model-specific automorphism theorem is assumed here.
-/

namespace MulAut

variable (G : Type*) [Group G]

/-- Inner automorphisms, as the range of the actual conjugation homomorphism. -/
public abbrev innerSubgroup : Subgroup (MulAut G) := (MulAut.conj : G →* MulAut G).range

/-- Inner automorphisms form a normal subgroup of the full automorphism group. -/
public instance innerSubgroup_normal : (innerSubgroup G).Normal where
  conj_mem := by
    rintro a ⟨g, rfl⟩ b
    refine ⟨b g, ?_⟩
    ext x
    simp

/-- The actual outer automorphism group `Aut(G)/Inn(G)`. -/
public abbrev Outer := MulAut G ⧸ innerSubgroup G

variable {G} {H : Type*} [Group H]

/-- Transport by a group isomorphism takes inner automorphisms onto inner automorphisms. -/
public theorem map_innerSubgroup_congr (e : G ≃* H) :
    (innerSubgroup G).map (MulAut.congr e).toMonoidHom = innerSubgroup H := by
  ext a
  constructor
  · rintro ⟨b, ⟨g, rfl⟩, rfl⟩
    exact ⟨e g, (congr_conj e g).symm⟩
  · rintro ⟨h, rfl⟩
    refine ⟨MulAut.conj (e.symm h), ⟨_, rfl⟩, ?_⟩
    exact (congr_conj e (e.symm h)).trans (congrArg MulAut.conj (e.apply_symm_apply h))

/-- A group isomorphism induces an isomorphism of outer automorphism groups. -/
public def outerCongr (e : G ≃* H) : Outer G ≃* Outer H :=
  QuotientGroup.congr _ _ (MulAut.congr e) (map_innerSubgroup_congr e)

/-- Solvability of the outer group transports across an actual group isomorphism. -/
public theorem isSolvable_outer_of_mulEquiv (e : G ≃* H) [Group.IsSolvable (Outer H)] :
    Group.IsSolvable (Outer G) :=
  Group.isSolvable_of_isSolvable_injective (outerCongr e).injective

/-- The kernel of conjugation on a normal subgroup is its relative centralizer. -/
public theorem conjNormal_ker_eq_centralizer (N : Subgroup G) [N.Normal] :
    (MulAut.conjNormal : G →* MulAut N).ker = Subgroup.centralizer (N : Set G) := by
  ext g
  constructor
  · intro hg n hn
    have hh := congrArg (fun e : MulAut N => (e ⟨n, hn⟩ : G)) hg
    change g * n * g⁻¹ = n at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hg
    apply MulEquiv.ext
    intro n
    apply Subtype.ext
    change g * (n : G) * g⁻¹ = n
    rw [← hg n n.property, mul_inv_cancel_right]

/-- A normal subgroup with trivial centralizer has a faithful conjugation action. -/
public theorem conjNormal_injective_of_centralizer_eq_bot (N : Subgroup G) [N.Normal]
    (hc : Subgroup.centralizer (N : Set G) = ⊥) :
    Function.Injective (MulAut.conjNormal : G →* MulAut N) := by
  rw [← MonoidHom.ker_eq_bot_iff, conjNormal_ker_eq_centralizer, hc]

/-- The elements acting by inner automorphisms are exactly `N C_G(N)`. -/
public theorem conjNormal_comap_innerSubgroup (N : Subgroup G) [N.Normal] :
    (innerSubgroup N).comap (MulAut.conjNormal : G →* MulAut N) =
      N ⊔ Subgroup.centralizer (N : Set G) := by
  have hmap : N.map (MulAut.conjNormal : G →* MulAut N) = innerSubgroup N := by
    ext a
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, MulAut.conjNormal_val.symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, MulAut.conjNormal_val⟩
  rw [← hmap, Subgroup.comap_map_eq, conjNormal_ker_eq_centralizer]

/-- Conjugation induces a homomorphism from `G/N` into the outer group of `N`. -/
@[expose] public def outerAction (N : Subgroup G) [N.Normal] : G ⧸ N →* Outer N :=
  QuotientGroup.map N (innerSubgroup N) MulAut.conjNormal (by
    intro x hx
    exact ⟨⟨x, hx⟩, MulAut.conjNormal_val.symm⟩)

/-- The induced homomorphism sends a coset to the class of its conjugation action. -/
public theorem outerAction_mk (N : Subgroup G) [N.Normal] (g : G) :
    outerAction N (QuotientGroup.mk g) =
      QuotientGroup.mk (MulAut.conjNormal g) := rfl

/-- Trivial centralizer makes the induced map on the actual quotient injective. -/
public theorem outerAction_injective (N : Subgroup G) [N.Normal]
    (hc : Subgroup.centralizer (N : Set G) = ⊥) :
    Function.Injective (outerAction N) := by
  apply (MonoidHom.ker_eq_bot_iff (outerAction N)).mp
  calc
    (outerAction N).ker = Subgroup.map (QuotientGroup.mk' N)
        ((innerSubgroup N).comap MulAut.conjNormal) :=
      QuotientGroup.ker_map N (innerSubgroup N) MulAut.conjNormal _
    _ = ⊥ := by
      rw [conjNormal_comap_innerSubgroup, hc, sup_bot_eq, QuotientGroup.map_mk'_self]

end MulAut

namespace Subgroup

/-- A self-centralizing normal subgroup with solvable outer group has solvable quotient. -/
public theorem quotient_isSolvable_of_centralizer_eq_bot
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hc : centralizer (N : Set G) = ⊥) [Group.IsSolvable (MulAut.Outer N)] :
    Group.IsSolvable (G ⧸ N) :=
  Group.isSolvable_of_isSolvable_injective (MulAut.outerAction_injective N hc)

end Subgroup
