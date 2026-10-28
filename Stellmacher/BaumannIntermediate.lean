module

public import Stellmacher.ElementaryAbelianMaxOrder

/-!
# Heredity of the Baumann subgroup

If the Baumann subgroup `B(Q) = Q ∩ C_G(Ω₁(Z(J(Q))))` lies in an
intermediate subgroup `K ≤ Q`, then `B(K)=B(Q)`. This supplies the core
transfer implicit before the application of (3.4) in Stellmacher (4.6).

The elementary Thompson subgroup `J(Q)` centralizes its own center, so
`J(Q) ≤ B(Q) ≤ K`. The maximum elementary-abelian orders of `K` and `Q`
therefore agree. The two proved Thompson-subgroup comparisons give
`J(K)=J(Q)`, after which the centralizer intersections agree by containment.

Source: `refs/latex/stellmacher-n-group.tex`, proof of (4.6), with the
maximum-order comparison formalized in `Stellmacher.ElementaryAbelianMaxOrder`.
-/

namespace Stellmacher

universe u

/-- An intermediate subgroup containing the Baumann subgroup has the same
Baumann subgroup. -/
public theorem baumann_eq_of_intermediate
    {G : Type u} [Group G] [Finite G] (Q K : Subgroup G)
    (hBK : Q ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G) ≤ K)
    (hKQ : K ≤ Q) :
    K ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ K) : Set G) =
    Q ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G) := by
  have hJQ : elementaryAbelianMaxJ Q ≤ Q := sSup_le fun _ hA ↦ hA.1
  have hJcent : elementaryAbelianMaxJ Q ≤ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G) := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨wJ, hwJ, rfl⟩ := hw
    obtain ⟨wZ, _, rfl⟩ := hwJ
    exact congrArg Subtype.val
      ((Subgroup.mem_center_iff.mp wZ.property) ⟨j, hj⟩).symm
  have hJK : elementaryAbelianMaxJ Q ≤ K := (le_inf hJQ hJcent).trans hBK
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq K Q hKQ
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le Q K hJK
  have horder : elementaryAbelianMaxOrder K = elementaryAbelianMaxOrder Q :=
    le_antisymm hsmall.1 hlarge.1
  have hJeq : elementaryAbelianMaxJ K = elementaryAbelianMaxJ Q :=
    le_antisymm (hsmall.2 horder) (hlarge.2 horder.symm)
  rw [hJeq]
  exact le_antisymm (inf_le_inf_right _ hKQ) (le_inf hBK inf_le_right)

end Stellmacher
