module

public import Mathlib.GroupTheory.Sylow

/-!
# Sylow intersections from centralizer containment

Suppose the centralizer of every nonidentity element of a Sylow subgroup `P`
is contained in `P`. Then every other Sylow subgroup meets `P` trivially.
Indeed, if `1 ≠ x ∈ P ∩ Q`, choose `1 ≠ z ∈ Z(Q)`. Centralizer containment
first puts `z` in `P`, and then puts `Q` in `C(z) ≤ P`.

This is the final group-theoretic step of Glauberman,
*A Characterization of the Suzuki Groups* (1968), Theorem 4.1(vi), p. 92.
The argument only needs centralizer containment, with no fusion hypothesis.
-/

namespace Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Centralizer containment makes a Sylow subgroup the unique Sylow subgroup
meeting it nontrivially. -/
public theorem eq_of_inf_ne_bot_of_centralizer_le (P Q : Sylow p G)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ (P : Subgroup G))
    (hinf : (P : Subgroup G) ⊓ (Q : Subgroup G) ≠ ⊥) : Q = P := by
  have : Nontrivial ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) :=
    ((P : Subgroup G) ⊓ (Q : Subgroup G)).nontrivial_iff_ne_bot.mpr hinf
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥((P : Subgroup G) ⊓ (Q : Subgroup G)))
  have hxne : (x : G) ≠ 1 := fun h => hx (Subtype.ext h)
  have : Nontrivial Q := ⟨⟨⟨x, x.property.2⟩, 1,
    fun h => hxne (congrArg Subtype.val h)⟩⟩
  have := Q.isPGroup'.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center Q)
  have hzne : ((z : Q) : G) ≠ 1 := fun h => hz (Subtype.ext (Subtype.ext h))
  have hcomm (q : Q) : (q : G) * ((z : Q) : G) = ((z : Q) : G) * (q : G) :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp z.property q)
  have hzP : ((z : Q) : G) ∈ (P : Subgroup G) :=
    hcent x x.property.1 hxne
      (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm ⟨x, x.property.2⟩).symm)
  apply Sylow.ext
  exact (Q.is_maximal' P.isPGroup' (fun q hq =>
    hcent z hzP hzne (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm ⟨q, hq⟩)))).symm

/-- Distinct Sylow subgroups have trivial intersection with a Sylow subgroup
containing the centralizers of all its nonidentity elements. -/
public theorem inf_eq_bot_of_ne_of_centralizer_le (P Q : Sylow p G)
    (hcent : ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ (P : Subgroup G))
    (hne : Q ≠ P) : (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ := by
  by_contra hinf
  exact hne (P.eq_of_inf_ne_bot_of_centralizer_le Q hcent hinf)

end Sylow
