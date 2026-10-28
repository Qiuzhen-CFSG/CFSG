module
public import Theory.GroupAction.SymplecticRankThree.AffineLines

/-!
# Perspectivities in the reconstructed projective three-space

Projection from a point outside two polar blocks is a bijection between
those planes and preserves all lines. The inverse is projection back from
the same center. Composing projections from two centers moves each point
along the line to the intersection of the line of centers with the original
plane. These statements use only the proved incidence geometry and include
q=2. Parallel planes will therefore construct translations, without assuming
field arithmetic or an action by a coordinate group.

Source: the coordinatization step in Higman (1964), Lemma 10, pp.153–154,
expanded using central projection in the reconstructed three-space.
-/

public noncomputable section
namespace Theory.GroupAction.SymplecticRankThree.PolarityDesign
variable {Ω : Type*} [Finite Ω] {q : ℕ} (D : PolarityDesign Ω q)
variable (hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)

/-- Central projection between two planes from a center outside both. -/
@[expose] def perspectivity (p r c : Ω) (hcp : c ∉ D.block p) (hcr : c ∉ D.block r) :
    ↥(D.block p) ≃ ↥(D.block r) where
  toFun x := ⟨D.project hl hq r c hcr x (fun he => hcp (he.symm ▸ x.property)),
    D.project_mem_block hl hq r c hcr x _⟩
  invFun y := ⟨D.project hl hq p c hcp y (fun he => hcr (he.symm ▸ y.property)),
    D.project_mem_block hl hq p c hcp y _⟩
  left_inv x := by
    apply Subtype.ext
    apply D.project_eq hl hq p c hcp _ (D.project_ne_center hl hq r c hcr x
      (fun he => hcp (he.symm ▸ x.property)))
    · rw [D.project_line_eq hl hq]
      exact D.right_mem_line _ _
    · exact x.property
  right_inv y := by
    apply Subtype.ext
    apply D.project_eq hl hq r c hcr _ (D.project_ne_center hl hq p c hcp y
      (fun he => hcr (he.symm ▸ y.property)))
    · rw [D.project_line_eq hl hq]
      exact D.right_mem_line _ _
    · exact y.property

theorem perspectivity_mem_line (p r c : Ω) (hcp : c ∉ D.block p) (hcr : c ∉ D.block r)
    (x : ↥(D.block p)) :
    (D.perspectivity hl hq p r c hcp hcr x : Ω) ∈ D.line c x :=
  D.project_mem_line hl hq r c hcr x (fun he => hcp (he.symm ▸ x.property))

theorem perspectivity_eq (p r c : Ω) (hcp : c ∉ D.block p) (hcr : c ∉ D.block r)
    (x : ↥(D.block p)) (y : ↥(D.block r)) (hy : (y : Ω) ∈ D.line c x) :
    D.perspectivity hl hq p r c hcp hcr x = y :=
  Subtype.ext (D.project_eq hl hq r c hcr x (fun he => hcp (he.symm ▸ x.property)) hy y.property)

theorem perspectivity_fixed (p r c : Ω) (hcp : c ∉ D.block p) (hcr : c ∉ D.block r)
    (x : ↥(D.block p)) (hx : (x : Ω) ∈ D.block r) :
    (D.perspectivity hl hq p r c hcp hcr x : Ω) = x :=
  congrArg Subtype.val (D.perspectivity_eq hl hq p r c hcp hcr x ⟨x,hx⟩
    (D.right_mem_line _ _))

private theorem perspectivity_line_forward (p r c : Ω)
    (hcp : c ∉ D.block p) (hcr : c ∉ D.block r)
    (x y z : ↥(D.block p)) (hz : (z : Ω) ∈ D.line x y) :
    (D.perspectivity hl hq p r c hcp hcr z : Ω) ∈
      D.line (D.perspectivity hl hq p r c hcp hcr x) (D.perspectivity hl hq p r c hcp hcr y) := by
  let E := D.perspectivity hl hq p r c hcp hcr
  by_cases hxy : x = y
  · subst y
    have hz' : z = x := Subtype.ext (by simpa only [D.line_eq_singleton hq, Set.mem_singleton_iff] using hz)
    subst z
    exact D.left_mem_line _ _
  obtain ⟨s,hxs,hys,hcs⟩ := D.exists_block_of_three hl (by omega) x y c
  have hsr : s ≠ r := fun he => hcr (he ▸ hcs)
  have hEs (t : ↥(D.block p)) (ht : (t : Ω) ∈ D.block s) : (E t : Ω) ∈ D.block s :=
    D.line_subset_block hcs ht (D.perspectivity_mem_line hl hq p r c hcp hcr t)
  have hExy : (E x : Ω) ≠ E y := fun he => hxy (E.injective (Subtype.ext he))
  have hint := D.intersection_eq_line hl hsr ⟨hEs x hxs,(E x).property⟩
    ⟨hEs y hys,(E y).property⟩ hExy
  exact hint ▸ ⟨hEs z (D.line_subset_block hxs hys hz),(E z).property⟩

/-- Projection preserves every line, in both directions. -/
theorem perspectivity_collinear (p r c : Ω) (hcp : c ∉ D.block p) (hcr : c ∉ D.block r)
    (x y z : ↥(D.block p)) :
    (D.perspectivity hl hq p r c hcp hcr z : Ω) ∈
      D.line (D.perspectivity hl hq p r c hcp hcr x) (D.perspectivity hl hq p r c hcp hcr y) ↔
        (z : Ω) ∈ D.line x y := by
  constructor
  · intro hz
    have hh := D.perspectivity_line_forward hl hq r p c hcr hcp _ _ _ hz
    change ((D.perspectivity hl hq p r c hcp hcr).symm
      (D.perspectivity hl hq p r c hcp hcr z) : Ω) ∈
      D.line ((D.perspectivity hl hq p r c hcp hcr).symm
        (D.perspectivity hl hq p r c hcp hcr x))
        ((D.perspectivity hl hq p r c hcp hcr).symm
          (D.perspectivity hl hq p r c hcp hcr y)) at hh
    simpa only [Equiv.symm_apply_apply] using hh
  · exact D.perspectivity_line_forward hl hq p r c hcp hcr x y z

/-- The composition of two projections moves each point on the line to
where the line of centers meets the original plane. -/
theorem double_perspectivity_center (p r c d a : Ω)
    (hcp : c ∉ D.block p) (hcr : c ∉ D.block r)
    (hdp : d ∉ D.block p) (hdr : d ∉ D.block r)
    (ha : a ∈ D.line c d) (hap : a ∈ D.block p)
    (x : ↥(D.block p)) (hax : a ≠ (x : Ω)) :
    (D.perspectivity hl hq r p d hdr hdp
      (D.perspectivity hl hq p r c hcp hcr x) : Ω) ∈ D.line a x := by
  obtain ⟨s,hcs,hds,hxs⟩ := D.exists_block_of_three hl (by omega) c d x
  have has : a ∈ D.block s := D.line_subset_block hcs hds ha
  have hsp : s ≠ p := fun he => hcp (he ▸ hcs)
  have h₁ := D.line_subset_block hcs hxs (D.perspectivity_mem_line hl hq p r c hcp hcr x)
  have h₂ := D.line_subset_block hds h₁ (D.perspectivity_mem_line hl hq r p d hdr hdp
    (D.perspectivity hl hq p r c hcp hcr x))
  have he := D.intersection_eq_line hl hsp ⟨has,hap⟩ ⟨hxs,x.property⟩ hax
  exact he ▸ ⟨h₂,(D.perspectivity hl hq r p d hdr hdp
      (D.perspectivity hl hq p r c hcp hcr x)).property⟩

end Theory.GroupAction.SymplecticRankThree.PolarityDesign
