module
public import ABG.ChapterII.Section1.WreathedNonabelianCenter
public import ABG.ChapterII.Section1.WreathedCentralQuotient
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Central quotients of centric nonabelian wreathed subgroups

For a subgroup `X` of the chosen wreathed group, assume its ambient centralizer
lies in `X` and `X` is nonabelian. Its center maps exactly onto the ambient
center, so is cyclic of order `2^n`. Its quotient by its own center is
isomorphic to a subgroup of `DihedralGroup (2^n)`. These reductions prepare
the automorphism analysis in ABG Chapter II §1 Lemma 3, article p.10.

Centricity places the ambient center in `X`; Lemma 2(xii) gives the reverse
containment between centers. The subtype map consequently induces the stated
center equivalence. Compose the subgroup inclusion with the ambient central
quotient and the dihedral equivalence from Lemma 2(vii). Its kernel is exactly
`center X`, and the first isomorphism theorem identifies the quotient with
the actual range subgroup. No automorphism hypothesis is needed for this
preliminary reduction.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private theorem ambient_center_le_of_centric (X : Subgroup S)
    (hc : Subgroup.centralizer (X : Set S) ≤ X) : Subgroup.center S ≤ X :=
  (Subgroup.center_le_centralizer (X : Set S)).trans hc

include P in
public theorem centric_center_map_eq (X : Subgroup S)
    (hc : Subgroup.centralizer (X : Set S) ≤ X) (hna : ¬ IsMulCommutative X) :
    (Subgroup.center X).map X.subtype = Subgroup.center S := by
  apply le_antisymm (P.nonabelian_center_le X hna)
  intro a ha
  refine ⟨⟨a, ambient_center_le_of_centric X hc ha⟩, ?_, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro b
  exact Subtype.ext ((Subgroup.mem_center_iff.mp ha) b)

public noncomputable def centricCenterEquiv (X : Subgroup S)
    (hc : Subgroup.centralizer (X : Set S) ≤ X) (hna : ¬ IsMulCommutative X) :
    Subgroup.center X ≃* Subgroup.center S :=
  ((Subgroup.center X).equivMapOfInjective X.subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr (P.centric_center_map_eq X hc hna))

include P in
public theorem centric_center_structure (X : Subgroup S)
    (hc : Subgroup.centralizer (X : Set S) ≤ X) (hna : ¬ IsMulCommutative X) :
    IsCyclic (Subgroup.center X) ∧ Nat.card (Subgroup.center X) = 2 ^ n := by
  let e := P.centricCenterEquiv X hc hna
  let := P.center_cyclic
  refine ⟨isCyclic_of_injective e.toMonoidHom e.injective, ?_⟩
  rw [Nat.card_congr e.toEquiv, P.card_center]

include P in
public theorem centric_quotient_embedding (X : Subgroup S)
    (hc : Subgroup.centralizer (X : Set S) ≤ X) (hna : ¬ IsMulCommutative X) :
    ∃ D : Subgroup (DihedralGroup (2 ^ n)),
      Nonempty ((X ⧸ Subgroup.center X) ≃* D) := by
  obtain ⟨e⟩ := P.central_quotient_equiv
  let q := QuotientGroup.mk' (Subgroup.center S)
  let f : X →* DihedralGroup (2 ^ n) := e.toMonoidHom.comp (q.comp X.subtype)
  have hk : f.ker = Subgroup.center X := by
    ext a
    change e (q (a : S)) = 1 ↔ a ∈ Subgroup.center X
    rw [← e.map_one, e.injective.eq_iff]
    change (QuotientGroup.mk (a : S) : S ⧸ Subgroup.center S) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro ha
      rw [Subgroup.mem_center_iff]
      intro b
      exact Subtype.ext ((Subgroup.mem_center_iff.mp ha) b)
    · intro ha
      rw [← P.centric_center_map_eq X hc hna]
      exact ⟨a,ha,rfl⟩
  refine ⟨f.range, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
end ABG.Wreathed.Presentation
