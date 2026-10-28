module
public import Theory.GroupAction.SymplecticRankThree.Perspectivity

/-!
# Geometric translations of the reconstructed affine plane

The parallel planes of an affine frame meet infinity in the same line.
There is a point on the third axis outside the base plane, including when
q=2. Projection to its parallel plane, followed by projection back from a
suitable second point at infinity, sends the origin to any prescribed
affine point. The resulting collineation fixes infinity pointwise and moves
all points along lines of one direction. Thus translations are constructed
from incidence, without assuming an elation action or field coordinates.

Source: Higman (1964), Lemma 10, pp.153–154, expanded coordinatization
argument. This supplies translations for the arithmetic of the affine chart;
field operations and projective field coordinates are not asserted here.
-/

public noncomputable section
namespace Theory.GroupAction.SymplecticRankThree.AffineFrame
variable {Ω : Type*} [Finite Ω] {q : ℕ} {D : PolarityDesign Ω q}
variable (f : AffineFrame D)
variable (hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)

abbrev Plane := ↥(D.block (f.level hl hq f.originPoint))

@[expose] def planeOrigin : f.Plane hl hq :=
  ⟨f.origin,(f.level_spec hl hq f.originPoint).2.2⟩

theorem level_inter_infinity (x : f.Affine) :
    D.block (f.level hl hq x) ∩ D.block f.infinity = D.line f.i f.j := by
  apply D.intersection_eq_line hl (a := f.level hl hq x) (b := f.infinity)
  · intro he
    have hx := (f.level_spec hl hq x).2.2
    rw [he] at hx
    exact x.property hx
  · exact ⟨(f.level_spec hl hq x).1,f.i_mem⟩
  · exact ⟨(f.level_spec hl hq x).2.1,f.j_mem⟩
  · exact f.ij_ne

theorem level_inter_level (x y : f.Affine) (hxy : f.level hl hq x ≠ f.level hl hq y) :
    D.block (f.level hl hq x) ∩ D.block (f.level hl hq y) = D.line f.i f.j :=
  D.intersection_eq_line hl hxy
    ⟨(f.level_spec hl hq x).1,(f.level_spec hl hq y).1⟩
    ⟨(f.level_spec hl hq x).2.1,(f.level_spec hl hq y).2.1⟩ f.ij_ne

/-- The third affine axis has a point outside the base plane, also for q=2. -/
theorem exists_axis_off_base : ∃ z : f.Axis,
    (z : Ω) ∉ D.block (f.level hl hq f.originPoint) := by
  have hc : 1 < Nat.card f.Axis := by rw [(f.axes_card hl hq).2.2]; omega
  let : Fintype f.Axis := Fintype.ofFinite _
  let : Nontrivial f.Axis := Fintype.one_lt_card_iff_nontrivial.mp
    (by simpa only [Nat.card_eq_fintype_card] using hc)
  let o : f.Axis := ⟨f.originPoint,D.right_mem_line _ _⟩
  obtain ⟨z,hz⟩ := exists_ne o
  refine ⟨z,?_⟩
  intro hp
  have he : (z : Ω) = f.origin := D.line_block_unique (f.k_ne_affine f.originPoint)
    (f.k_not_level hl hq f.originPoint) z.property (D.right_mem_line _ _) hp
    (f.level_spec hl hq f.originPoint).2.2
  exact hz (Subtype.ext (Subtype.ext he))

/-- Two spatial projections construct every translation of the base plane.
The map fixes its line at infinity and all lines through its translation
center. No coordinate operations or plane automorphisms are assumed. -/
theorem plane_translation_exists (b : f.Base hl hq) :
    ∃ E : Equiv.Perm (f.Plane hl hq),
      (∀ x y z : f.Plane hl hq,
        (E z : Ω) ∈ D.line (E x) (E y) ↔ (z : Ω) ∈ D.line x y) ∧
      (∀ x : f.Plane hl hq, (x : Ω) ∈ D.block f.infinity → E x = x) ∧
      (E (f.planeOrigin hl hq) : Ω) = b ∧
      ∃ d : f.Direction hl hq, ∀ x : f.Plane hl hq, (E x : Ω) ∈ D.line d x := by
  let p := f.level hl hq f.originPoint
  by_cases hbo : (b : Ω) = f.origin
  · refine ⟨Equiv.refl _,fun _ _ _ => Iff.rfl,fun _ _ => rfl,hbo.symm,
      f.directionI hl hq,fun x => D.right_mem_line _ _⟩
  obtain ⟨z,hzp⟩ := f.exists_axis_off_base hl hq
  let r := f.level hl hq z.val
  have hpr : p ≠ r := by
    intro he
    apply hzp
    change (z : Ω) ∈ D.block p
    rw [he]
    exact (f.level_spec hl hq z.val).2.2
  have hbr : (b : Ω) ∉ D.block r := by
    intro hb
    exact b.val.property (D.line_subset_block f.i_mem f.j_mem
      (f.level_inter_level hl hq f.originPoint z.val hpr ▸ ⟨b.property,hb⟩))
  have hzb : (z : Ω) ≠ b := fun he => hzp (he.symm ▸ b.property)
  obtain ⟨c,⟨hczb,hcInf⟩,_⟩ := D.existsUnique_line_block hl hq z.val.property hzb
  have hcp : c ∉ D.block p := by
    intro hcp
    have hcb : c ≠ (b : Ω) := fun he => b.val.property (he ▸ hcInf)
    have he := D.line_eq_of_mem_of_mem hzb hczb (D.right_mem_line _ _) hcb
    exact hzp (D.line_subset_block hcp b.property (he.symm ▸ D.left_mem_line _ _))
  have hcr : c ∉ D.block r := by
    intro hcr
    have hzc : (z : Ω) ≠ c := fun he => z.val.property (he.symm ▸ hcInf)
    have he := D.line_eq_of_mem hzb hczb hzc
    exact hbr (D.line_subset_block (f.level_spec hl hq z.val).2.2 hcr
      (he.symm ▸ D.right_mem_line _ _))
  have hk : f.k ≠ c := by
    intro he
    have hkc : f.k ∈ D.line (z : Ω) (b : Ω) := he.symm ▸ hczb
    have hkz := f.k_ne_affine z.val
    have hko := f.k_ne_affine f.originPoint
    have h₁ := D.line_eq_of_mem hko z.property hkz
    have h₂ := D.line_eq_of_mem_of_mem hzb hkc (D.left_mem_line _ _) hkz
    have hbko : (b : Ω) ∈ D.line f.k f.origin :=
      h₁ ▸ h₂.symm ▸ D.right_mem_line (z : Ω) (b : Ω)
    exact hbo (D.line_block_unique hko (f.k_not_level hl hq f.originPoint)
      hbko (D.right_mem_line _ _) b.property (f.level_spec hl hq f.originPoint).2.2)
  let E₁ := D.perspectivity hl hq p r f.k
    (f.k_not_level hl hq f.originPoint) (f.k_not_level hl hq z.val)
  let E₂ := D.perspectivity hl hq r p c hcr hcp
  let E := E₁.trans E₂
  have hfix (x : f.Plane hl hq) (hx : (x : Ω) ∈ D.block f.infinity) : E x = x := by
    have hxr : (x : Ω) ∈ D.block r := D.line_subset_block
      (f.level_spec hl hq z.val).1 (f.level_spec hl hq z.val).2.1
      (f.level_inter_infinity hl hq f.originPoint ▸ ⟨x.property,hx⟩)
    have h₁ : E₁ x = ⟨x,hxr⟩ := Subtype.ext
      (D.perspectivity_fixed hl hq p r f.k _ _ x hxr)
    change E₂ (E₁ x) = x
    rw [h₁]
    exact Subtype.ext (D.perspectivity_fixed hl hq r p c _ _ ⟨x,hxr⟩ x.property)
  refine ⟨E,?_,hfix,?_,?_⟩
  · intro x y w
    exact (D.perspectivity_collinear hl hq r p c hcr hcp (E₁ x) (E₁ y) (E₁ w)).trans
      (D.perspectivity_collinear hl hq p r f.k _ _ x y w)
  · have h₁ : E₁ (f.planeOrigin hl hq) = ⟨z,(f.level_spec hl hq z.val).2.2⟩ :=
      D.perspectivity_eq hl hq p r f.k _ _ _ _ z.property
    change (E₂ (E₁ (f.planeOrigin hl hq)) : Ω) = b
    rw [h₁]
    apply congrArg Subtype.val (D.perspectivity_eq hl hq r p c hcr hcp _ ⟨b,b.property⟩ ?_)
    have hcz : c ≠ (z : Ω) := fun he => z.val.property (he ▸ hcInf)
    have he := D.line_eq_of_mem_of_mem hzb hczb (D.left_mem_line _ _) hcz
    exact he.symm ▸ D.right_mem_line _ _
  · let d := D.project hl hq p f.k (f.k_not_level hl hq f.originPoint) c hk
    have hdl : d ∈ D.line f.k c := D.project_mem_line hl hq p f.k _ c hk
    have hdp : d ∈ D.block p := D.project_mem_block hl hq p f.k _ c hk
    have hdInf : d ∈ D.block f.infinity := D.line_subset_block f.k_mem hcInf hdl
    refine ⟨⟨d,hdInf,hdp⟩,?_⟩
    intro x
    by_cases hdx : d = (x : Ω)
    · rw [hfix x (hdx ▸ hdInf)]
      exact D.right_mem_line _ _
    · exact D.double_perspectivity_center hl hq p r f.k c d _ _ hcp hcr hdl hdp x hdx

end Theory.GroupAction.SymplecticRankThree.AffineFrame
