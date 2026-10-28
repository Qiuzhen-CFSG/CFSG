module

public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.Jordan.Morphism

universe u

/-! Jordan type in closed subgroups. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- GLS Proposition 1.2.2(b): semisimplicity is independent of whether an
element is regarded in a closed subgroup or in the ambient group. -/
public lemma closedSubgroup_semisimpleElement_iff
    {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) {g : Variety.Point G}
    (hg : g ∈ (H : Set (Variety.Point G))) :
    IsSemisimpleElement G g ↔
      IsSemisimpleElement H.carrierVariety
        (H.pointEquiv.symm ⟨g, hg⟩) := by
  let gh : Variety.Point H.carrierVariety := H.pointEquiv.symm ⟨g, hg⟩
  have hinc : H.inclusion.onPoints gh = g := by
    change (H.pointEquiv gh).val = g
    rw [H.pointEquiv.apply_symm_apply]
  constructor
  · intro hG
    let dH := jordanDecomposition gh
    let dG := jordanDecomposition (H.inclusion.onPoints gh)
    let trivial : JordanDecomposition (H.inclusion.onPoints gh) :=
      { semisimplePart := H.inclusion.onPoints gh
        unipotentPart := 1
        eq_mul := by simp
        commute := Commute.one_right _
        semisimple := by simpa [hinc] using hG
        unipotent := one_isUnipotentElement G }
    have hdG : dG = trivial := dG.unique trivial
    have hsG : dG.semisimplePart = H.inclusion.onPoints gh :=
      congrArg JordanDecomposition.semisimplePart hdG
    have hcomp := H.inclusion.maps_jordanComponents gh dH dG
    have hhs : H.inclusion.onPoints dH.semisimplePart =
        H.inclusion.onPoints gh := by
      rw [← hcomp.1, hsG]
    have hs_eq : dH.semisimplePart = gh := H.inclusion_injective hhs
    have hsemiH := dH.semisimple
    rw [hs_eq] at hsemiH
    exact hsemiH
  · intro hH
    have h := morphism_preserves_semisimpleElement H.inclusion gh hH
    rw [hinc] at h
    exact h

/-- GLS Proposition 1.2.2(b): unipotence is independent of whether an element
is regarded in a closed subgroup or in the ambient group. -/
public lemma closedSubgroup_unipotentElement_iff
    {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) {g : Variety.Point G}
    (hg : g ∈ (H : Set (Variety.Point G))) :
    IsUnipotentElement G g ↔
      IsUnipotentElement H.carrierVariety
        (H.pointEquiv.symm ⟨g, hg⟩) := by
  let gh : Variety.Point H.carrierVariety := H.pointEquiv.symm ⟨g, hg⟩
  have hinc : H.inclusion.onPoints gh = g := by
    change (H.pointEquiv gh).val = g
    rw [H.pointEquiv.apply_symm_apply]
  constructor
  · intro hG
    let dH := jordanDecomposition gh
    let dG := jordanDecomposition (H.inclusion.onPoints gh)
    let trivial : JordanDecomposition (H.inclusion.onPoints gh) :=
      { semisimplePart := 1
        unipotentPart := H.inclusion.onPoints gh
        eq_mul := by simp
        commute := Commute.one_left _
        semisimple := one_isSemisimpleElement G
        unipotent := by simpa [hinc] using hG }
    have hdG : dG = trivial := dG.unique trivial
    have huG : dG.unipotentPart = H.inclusion.onPoints gh :=
      congrArg JordanDecomposition.unipotentPart hdG
    have hcomp := H.inclusion.maps_jordanComponents gh dH dG
    have hhu : H.inclusion.onPoints dH.unipotentPart =
        H.inclusion.onPoints gh := by
      rw [← hcomp.2, huG]
    have hu_eq : dH.unipotentPart = gh := H.inclusion_injective hhu
    have huniH := dH.unipotent
    rw [hu_eq] at huniH
    exact huniH
  · intro hH
    have h := morphism_preserves_unipotentElement H.inclusion gh hH
    rw [hinc] at h
    exact h

/-- The ambient-to-subgroup direction of GLS Proposition 1.2.2(b). -/
public lemma closedSubgroup_unipotent_of_ambient
    {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) {g : Variety.Point G}
    (hg : g ∈ (H : Set (Variety.Point G)))
    (huni : IsUnipotentElement G g) :
    IsUnipotentElement H.carrierVariety
      (H.pointEquiv.symm ⟨g, hg⟩) :=
  (closedSubgroup_unipotentElement_iff H hg).mp huni

omit [IsAlgClosed k] in
/-- Powers in a closed subgroup correspond to powers of the ambient element. -/
public lemma ClosedSubgroup.pointEquiv_symm_pow
    {G : Variety k} [AlgebraicGroup G]
    (H : ClosedSubgroup G) (g : Variety.Point G)
    (hg : g ∈ (H : Set (Variety.Point G))) (m : ℕ) :
    (H.pointEquiv.symm ⟨g, hg⟩) ^ m =
      H.pointEquiv.symm ⟨g ^ m, H.toSubgroup.pow_mem hg m⟩ := by
  apply H.pointEquiv.injective
  have htrans : ∀ m : ℕ,
      H.pointEquiv ((H.pointEquiv.symm ⟨g, hg⟩) ^ m) =
        (⟨g, hg⟩ : H.toSubgroup) ^ m := by
    intro n
    induction n with
    | zero =>
        rw [pow_zero, pow_zero]
        change H.pointEquiv 1 = (1 : H.toSubgroup)
        exact H.pointEquiv.apply_symm_apply (1 : H.toSubgroup)
    | succ n ih =>
        rw [pow_succ, pow_succ]
        rw [show H.pointEquiv
              ((H.pointEquiv.symm ⟨g, hg⟩) ^ n *
                H.pointEquiv.symm ⟨g, hg⟩) =
              H.pointEquiv ((H.pointEquiv.symm ⟨g, hg⟩) ^ n) *
                H.pointEquiv (H.pointEquiv.symm ⟨g, hg⟩) by rfl]
        rw [ih, H.pointEquiv.apply_symm_apply]
  calc
    H.pointEquiv ((H.pointEquiv.symm ⟨g, hg⟩) ^ m) =
        (⟨g, hg⟩ : H.toSubgroup) ^ m := htrans m
    _ = H.pointEquiv
        (H.pointEquiv.symm ⟨g ^ m, H.toSubgroup.pow_mem hg m⟩) := by
      rw [H.pointEquiv.apply_symm_apply]
      ext
      rw [Subgroup.coe_pow]

end Theory.AlgebraicGroup
