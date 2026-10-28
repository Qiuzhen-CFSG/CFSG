module
public import Theory.GroupAction.SymplecticRankThree.AdditiveLines
import all Theory.GroupAction.SymplecticRankThree.TranslationGroup

/-!
# Geometric homotheties of the reconstructed affine plane

Two spatial projections between parallel planes give a direction-fixing
collineation fixing the origin and carrying any nonzero point of an axis
to any other. The center of the second projection is obtained by intersecting
two lines in a spatial plane. This includes q=2 without an inequality q>2.
Conjugation preserves the actual translations and every direction subgroup;
for an origin-fixing motion its action agrees with evaluation on translations.

The private import of TranslationGroup is an intentional implementation split:
it supplies the body of HasDirection only to prove its public characterization.
The original predicate and all existing public boundaries remain unchanged.

Source: Higman (1964), Lemma 10, pp.153–154, expanded coordinatization
by spatial perspectivities. ScalarField uses these maps to prove field order.
-/

public noncomputable section
namespace Theory.GroupAction.SymplecticRankThree.AffineFrame
variable {Ω : Type*} [Finite Ω] {q : ℕ} {D : PolarityDesign Ω q}
variable (f : AffineFrame D)
variable (hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)

/-- Spatial projections produce every nonzero scaling on an affine axis. -/
theorem exists_homothety (a b : f.Base hl hq)
    (ha : (a : Ω) ≠ f.origin) (hb : (b : Ω) ≠ f.origin)
    (hab : (b : Ω) ∈ D.line f.origin a) :
    ∃ E : f.Motion hl hq, E.affineEquiv (f.baseOrigin hl hq) = f.baseOrigin hl hq ∧
      E.affineEquiv a = b := by
  let p := f.level hl hq f.originPoint
  obtain ⟨z,hzp⟩ := f.exists_axis_off_base hl hq
  let r := f.level hl hq z.val
  have hpr : p ≠ r := by
    intro he
    apply hzp
    change (z : Ω) ∈ D.block p
    rw [he]
    exact (f.level_spec hl hq z.val).2.2
  have off_r (x : f.Base hl hq) : (x : Ω) ∉ D.block r := by
    intro hx
    exact x.val.property (D.line_subset_block f.i_mem f.j_mem
      (f.level_inter_level hl hq f.originPoint z.val hpr ▸ ⟨x.property,hx⟩))
  let E₁ := D.perspectivity hl hq p r f.k
    (f.k_not_level hl hq f.originPoint) (f.k_not_level hl hq z.val)
  let A := E₁ ⟨a,a.property⟩
  have hAInf : (A : Ω) ∉ D.block f.infinity :=
    D.project_not_mem_infinity hl hq (f.k_not_level hl hq z.val) f.k_mem a.val.property
  have hAp : (A : Ω) ∉ D.block p := by
    intro hh
    exact hAInf (D.line_subset_block f.i_mem f.j_mem
      (f.level_inter_level hl hq f.originPoint z.val hpr ▸ ⟨hh,A.property⟩))
  have hAb : (A : Ω) ≠ b := fun he => hAp (he.symm ▸ b.property)
  have h₁ : E₁ (f.planeOrigin hl hq) = ⟨z,(f.level_spec hl hq z.val).2.2⟩ :=
    D.perspectivity_eq hl hq p r f.k _ _ _ _ z.property
  have hAz : (A : Ω) ≠ z := by
    intro hh
    have he : E₁ ⟨a,a.property⟩ = E₁ (f.planeOrigin hl hq) := (Subtype.ext hh).trans h₁.symm
    exact ha (congrArg Subtype.val (E₁.injective he))
  obtain ⟨s,hks,hos,has⟩ := D.exists_block_of_three hl (by omega) f.k f.origin a
  have hbs : (b : Ω) ∈ D.block s := D.line_subset_block hos has hab
  have hAs : (A : Ω) ∈ D.block s := D.line_subset_block hks has
    (D.perspectivity_mem_line hl hq p r f.k _ _ ⟨a,a.property⟩)
  obtain ⟨c,hcko,hcAb⟩ := D.coplanar_lines_meet hl (f.k_ne_affine f.originPoint) hAb hks hos hAs hbs
  have hcp : c ∉ D.block p := by
    intro hcp
    have hco : c = f.origin := D.line_block_unique (f.k_ne_affine f.originPoint)
      (f.k_not_level hl hq f.originPoint) hcko (D.right_mem_line _ _) hcp
      (f.level_spec hl hq f.originPoint).2.2
    have he := D.line_eq_of_mem_of_mem hAb (hco ▸ hcAb) (D.right_mem_line _ _) hb.symm
    exact hAp (D.line_subset_block (f.level_spec hl hq f.originPoint).2.2 b.property
      (he.symm ▸ D.left_mem_line _ _))
  have hcr : c ∉ D.block r := by
    intro hcr
    have hcz : c = (z : Ω) := D.line_block_unique (f.k_ne_affine f.originPoint)
      (f.k_not_level hl hq z.val) hcko z.property hcr (f.level_spec hl hq z.val).2.2
    have he := D.line_eq_of_mem hAb (hcz ▸ hcAb) hAz
    exact off_r b (D.line_subset_block A.property (f.level_spec hl hq z.val).2.2
      (he.symm ▸ D.right_mem_line _ _))
  let E₂ := D.perspectivity hl hq r p c hcr hcp
  let E : f.Motion hl hq := ⟨E₁.trans E₂, by
    constructor
    · intro x y w
      exact (D.perspectivity_collinear hl hq r p c hcr hcp (E₁ x) (E₁ y) (E₁ w)).trans
        (D.perspectivity_collinear hl hq p r f.k _ _ x y w)
    · intro x hx
      have hxr : (x : Ω) ∈ D.block r := D.line_subset_block
        (f.level_spec hl hq z.val).1 (f.level_spec hl hq z.val).2.1
        (f.level_inter_infinity hl hq f.originPoint ▸ ⟨x.property,hx⟩)
      have hh : E₁ x = ⟨x,hxr⟩ := Subtype.ext (D.perspectivity_fixed hl hq p r f.k _ _ x hxr)
      change E₂ (E₁ x) = x
      rw [hh]
      exact Subtype.ext (D.perspectivity_fixed hl hq r p c _ _ ⟨x,hxr⟩ x.property)⟩
  refine ⟨E,?_,?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    change (E₂ (E₁ (f.planeOrigin hl hq)) : Ω) = f.origin
    rw [h₁]
    have hcz : c ≠ (z : Ω) := fun he => hcr (he.symm ▸ (f.level_spec hl hq z.val).2.2)
    have he := D.line_eq_of_mem_of_mem (f.k_ne_affine f.originPoint) hcko z.property hcz
    exact congrArg Subtype.val (D.perspectivity_eq hl hq r p c hcr hcp _
      (f.planeOrigin hl hq) (he.symm ▸ D.right_mem_line _ _))
  · apply Subtype.ext
    apply Subtype.ext
    change (E₂ A : Ω) = b
    have hcA : c ≠ (A : Ω) := fun he => hcr (he.symm ▸ A.property)
    have he := D.line_eq_of_mem_of_mem hAb hcAb (D.left_mem_line _ _) hcA
    exact congrArg Subtype.val (D.perspectivity_eq hl hq r p c hcr hcp A ⟨b,b.property⟩
      (he.symm ▸ D.right_mem_line _ _))

namespace Motion
variable {f hl hq} (E : f.Motion hl hq)

theorem hasDirection_iff (d : f.Direction hl hq) : E.HasDirection d ↔
    ∀ x : f.Plane hl hq, (E.val x : Ω) ∈ D.line d x := Iff.rfl

theorem conjugate_direction {T : f.Motion hl hq} {d : f.Direction hl hq}
    (hT : T.HasDirection d) : (E*T*E⁻¹).HasDirection d := by
  apply (hasDirection_iff _ _).mpr
  intro x
  have hh := (E.parallel d ((E⁻¹).val x) (T.val ((E⁻¹).val x))).mpr (hT ((E⁻¹).val x))
  change (E.val (T.val (E.val⁻¹ x)) : Ω) ∈ D.line d x
  simpa only [Subgroup.coe_inv,Equiv.Perm.inv_def,Equiv.apply_symm_apply] using hh

/-- Conjugation by a direction-fixing collineation preserves translations
and each of their direction subgroups. -/
@[expose] def conjugateTranslations : f.translations hl hq ≃* f.translations hl hq where
  toFun T := ⟨E*T.val*E⁻¹,by
    obtain ⟨d,hd⟩ := T.val.translation_spec.mp T.property
    exact (E*T.val*E⁻¹).translation_spec.mpr ⟨d,E.conjugate_direction hd⟩⟩
  invFun T := ⟨E⁻¹*T.val*E,by
    obtain ⟨d,hd⟩ := T.val.translation_spec.mp T.property
    exact (E⁻¹*T.val*E).translation_spec.mpr
      ⟨d,by simpa only [inv_inv] using (E⁻¹).conjugate_direction hd⟩⟩
  left_inv T := Subtype.ext (by simp only [mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one])
  right_inv T := Subtype.ext (by simp only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,mul_one])
  map_mul' T U := Subtype.ext (by
    change E*(T.val*U.val)*E⁻¹ = (E*T.val*E⁻¹)*(E*U.val*E⁻¹)
    simp only [mul_assoc,inv_mul_cancel_left])

theorem conjugateTranslations_direction (T : f.translations hl hq) (d : f.Direction hl hq)
    (hT : T ∈ f.directionTranslations hl hq d) :
    E.conjugateTranslations T ∈ f.directionTranslations hl hq d := E.conjugate_direction hT

/-- Fixing the affine origin identifies conjugation on translations with
the actual geometric action. -/
theorem conjugateTranslations_evaluation
    (hE : E.affineEquiv (f.baseOrigin hl hq) = f.baseOrigin hl hq)
    (T : f.translations hl hq) :
    f.translationEquiv hl hq (E.conjugateTranslations T) =
      E.affineEquiv (f.translationEquiv hl hq T) := by
  have ho : E.val (f.planeOrigin hl hq) = f.planeOrigin hl hq :=
    Subtype.ext (congrArg (fun x : f.Base hl hq => (x : Ω)) hE)
  have hoi : E.val⁻¹ (f.planeOrigin hl hq) = f.planeOrigin hl hq := by
    apply E.val.injective
    rw [Equiv.Perm.inv_def,Equiv.apply_symm_apply,ho]
  apply Subtype.ext
  apply Subtype.ext
  change (E.val (T.val.val (E.val⁻¹ (f.planeOrigin hl hq))) : Ω) =
    (E.val (T.val.val (f.planeOrigin hl hq)) : Ω)
  rw [hoi]

end Motion
end Theory.GroupAction.SymplecticRankThree.AffineFrame
