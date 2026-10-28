module

public import Theory.GroupTheory.InvolutionPairCentralInvolution
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Exhausting a simple group using involution centralizers

Suppose Q contains the full ambient centralizer of each of its involutions.
If an involution outside Q were not conjugate to one in Q, the elementary
dihedral argument would produce an involution commuting with both. Applying
the centralizer condition twice puts the outside involution in Q. Hence an
outside involution makes all involutions of Q conjugate in the ambient group.

In a simple group, a proper subgroup cannot contain every conjugate of a
nonidentity element. Consequently two ambient nonconjugate involutions in Q
force Q to be the whole group. This proves the exhaustion step without a
strong embedding classification or an assumed recognition theorem.

Source: the final step of D. Held, "A Characterization of some multiply
transitive permutation groups, I", Illinois J. Math. 13 (1969),
DOI 10.1215/ijm/1256053756, Lemma 5.12, p.239.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10
universe u

namespace A10Identification
variable {G : Type u} [Group G] [Finite G]

public theorem isConj_of_mem_of_not_mem (Q : Subgroup G)
    (hC : ∀ t ∈ Q, orderOf t = 2 → centralizer ({t} : Set G) ≤ Q)
    {s t : G} (hsQ : s ∈ Q) (hs : orderOf s = 2)
    (htQ : t ∉ Q) (ht : orderOf t = 2) : IsConj s t := by
  by_contra hn
  obtain ⟨w, _, hw, hws, hwt⟩ :=
    Theory.GroupTheory.exists_central_involution_of_not_isConj s t hs ht hn
  have hwQ : w ∈ Q := hC s hsQ hs (mem_centralizer_singleton_iff.mpr hws.eq)
  exact htQ (hC w hwQ hw (mem_centralizer_singleton_iff.mpr hwt.eq.symm))

public theorem eq_top_of_centralizers_of_not_isConj [IsSimpleGroup G]
    (Q : Subgroup G)
    (hC : ∀ t ∈ Q, orderOf t = 2 → centralizer ({t} : Set G) ≤ Q)
    {a b : G} (haQ : a ∈ Q) (ha : orderOf a = 2)
    (hbQ : b ∈ Q) (hb : orderOf b = 2) (hab : ¬ IsConj a b) : Q = ⊤ := by
  by_contra hQ
  have hcore : Q.normalCore = ⊥ := by
    rcases (inferInstance : Q.normalCore.Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact False.elim (hQ (top_unique (h ▸ Q.normalCore_le)))
  have hncore : a ∉ Q.normalCore := by
    rw [hcore, mem_bot]
    intro ha1
    simp [ha1] at ha
  change ¬ ∀ g : G, g * a * g⁻¹ ∈ Q at hncore
  push Not at hncore
  obtain ⟨g, hg⟩ := hncore
  have hga : orderOf (g * a * g⁻¹) = 2 := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ha]
  have hac := isConj_of_mem_of_not_mem Q hC haQ ha hg hga
  have hbc := isConj_of_mem_of_not_mem Q hC hbQ hb hg hga
  exact hab (hac.trans hbc.symm)

end A10Identification
end Theory.GroupTheory.HeldM22A10
