module
public import Theory.GroupAction.SymplecticRankThree.FieldPlane

/-!
# Compatible field parameters for spatial projections

Parallel projection between the affine levels of a reconstructed projective
three-space gives a translation of the constructed field plane. Its displacement
depends only on height. Two independent projection directions identify the
transverse axis with the same scalar field: their difference has the fixed
direction where the line of projection centers meets the base plane. Comparing
its two coordinates proves equality of the scalar parameters, including q=2.

FieldSpace uses these actual geometric projections to coordinatize every spatial
affine line. No compatibility of plane charts or field parameters is an input.

Source: the expanded coordinatization step in Higman (1964), Lemma 10,
pp.153–154, using spatial perspectivities in the reconstructed incidence geometry.
-/

public noncomputable section
namespace Theory.GroupAction.SymplecticRankThree.AffineFrame
variable {Ω : Type*} [Finite Ω] {q : ℕ} {D : PolarityDesign Ω q}
variable (f : AffineFrame D)
variable (hl : ∀ a b, a ≠ b → (D.line a b).ncard = q+1) (hq : 2 ≤ q)
local instance : AddCommGroup (f.Base hl hq) := f.affineAddCommGroup hl hq
local instance : Field (f.scalarRing hl hq) := f.scalarField hl hq
local instance : Module (f.scalarRing hl hq) (f.Base hl hq) := f.scalarModule hl hq

/-- A direction transverse to the parallel planes of this affine frame. -/
abbrev Transverse := {c : Ω // c ∈ D.block f.infinity ∧
  c ∉ D.block (f.level hl hq f.originPoint)}

@[expose] def transverseK : f.Transverse hl hq :=
  ⟨f.k,f.k_mem,f.k_not_level hl hq f.originPoint⟩

theorem transverse_not_level (c : f.Transverse hl hq) (x : f.Affine) :
    (c : Ω) ∉ D.block (f.level hl hq x) := by
  intro hc
  have hcL : (c : Ω) ∈ D.line f.i f.j :=
    f.level_inter_infinity hl hq x ▸ ⟨hc,c.property.1⟩
  exact c.property.2 (D.line_subset_block (f.level_spec hl hq f.originPoint).1
    (f.level_spec hl hq f.originPoint).2.1 hcL)

@[expose] def parallelFoot (c : f.Transverse hl hq) (x : f.Affine) : f.Base hl hq :=
  ⟨⟨D.project hl hq (f.level hl hq f.originPoint) c c.property.2 x
    (fun he => x.property (he ▸ c.property.1)),
    D.project_not_mem_infinity hl hq c.property.2 c.property.1 x.property⟩,
    D.project_mem_block hl hq (f.level hl hq f.originPoint) c c.property.2 x
      (fun he => x.property (he ▸ c.property.1))⟩

theorem parallelFoot_mem_line (c : f.Transverse hl hq) (x : f.Affine) :
    (f.parallelFoot hl hq c x : Ω) ∈ D.line c x := D.project_mem_line hl hq (f.level hl hq f.originPoint) c c.property.2 x
      (fun he => x.property (he ▸ c.property.1))

theorem parallelFoot_fixed (c : f.Transverse hl hq) (x : f.Base hl hq) :
    f.parallelFoot hl hq c x.val = x :=
  Subtype.ext (Subtype.ext (D.project_fixed hl hq _ _ c.property.2 _ x.property))

theorem parallelFoot_k (x : f.Affine) :
    f.parallelFoot hl hq (f.transverseK hl hq) x = f.foot hl hq x := rfl

/-- The projection from any transverse direction between parallel planes,
followed by projection back along k, is a genuine base-plane translation. -/
theorem parallelFoot_assemble_translation (c : f.Transverse hl hq) (z : f.Axis) :
    ∃ T : f.translations hl hq, ∀ a : f.Base hl hq,
      T.val.affineEquiv a = f.parallelFoot hl hq c (f.assemble hl hq a z) := by
  let p := f.level hl hq f.originPoint
  let r := f.level hl hq z.val
  let E₁ := D.perspectivity hl hq p r f.k
    (f.k_not_level hl hq f.originPoint) (f.k_not_level hl hq z.val)
  let E₂ := D.perspectivity hl hq r p c (f.transverse_not_level hl hq c z.val) c.property.2
  let E : f.Motion hl hq := ⟨E₁.trans E₂,by
    constructor
    · intro x y w
      exact (D.perspectivity_collinear hl hq r p c (f.transverse_not_level hl hq c z.val) c.property.2 (E₁ x) (E₁ y) (E₁ w)).trans
        (D.perspectivity_collinear hl hq p r f.k _ _ x y w)
    · intro x hx
      have hxr : (x : Ω) ∈ D.block r := D.line_subset_block
        (f.level_spec hl hq z.val).1 (f.level_spec hl hq z.val).2.1
        (f.level_inter_infinity hl hq f.originPoint ▸ ⟨x.property,hx⟩)
      have hh : E₁ x = ⟨x,hxr⟩ := Subtype.ext
        (D.perspectivity_fixed hl hq p r f.k _ _ x hxr)
      change E₂ (E₁ x) = x
      rw [hh]
      exact Subtype.ext (D.perspectivity_fixed hl hq r p c _ _ ⟨x,hxr⟩ x.property)⟩
  have htrans : E ∈ f.translations hl hq := by
    apply E.translation_spec.mpr
    by_cases hkc : f.k = (c : Ω)
    · refine ⟨f.directionI hl hq,?_⟩
      apply (E.hasDirection_iff _).mpr
      intro x
      have he : E.val x = x := by
        change D.perspectivity hl hq r p c (f.transverse_not_level hl hq c z.val) c.property.2 (E₁ x) = x
        apply D.perspectivity_eq hl hq r p c (f.transverse_not_level hl hq c z.val) c.property.2
        rw [← hkc]
        have hL := D.project_line_eq hl hq r f.k (f.k_not_level hl hq z.val)
          x (fun he => f.k_not_level hl hq f.originPoint (he.symm ▸ x.property))
        change (x : Ω) ∈ D.line f.k (D.project hl hq r f.k (f.k_not_level hl hq z.val) x
          (fun he => f.k_not_level hl hq f.originPoint (he.symm ▸ x.property)))
        rw [hL]
        exact D.right_mem_line _ _
      rw [he]
      exact D.right_mem_line _ _
    · let d := D.project hl hq p f.k (f.k_not_level hl hq f.originPoint) c hkc
      have hdl : d ∈ D.line f.k c := D.project_mem_line hl hq p f.k _ c hkc
      have hdp : d ∈ D.block p := D.project_mem_block hl hq p f.k _ c hkc
      have hdInf : d ∈ D.block f.infinity := D.line_subset_block f.k_mem c.property.1 hdl
      refine ⟨⟨d,hdInf,hdp⟩,?_⟩
      apply (E.hasDirection_iff _).mpr
      intro x
      by_cases hdx : d = (x : Ω)
      · rw [E.infinity_fixed x (hdx ▸ hdInf)]
        exact D.right_mem_line _ _
      · exact D.double_perspectivity_center hl hq p r f.k c d _ _ c.property.2
          (f.transverse_not_level hl hq c z.val) hdl hdp x hdx
  exact ⟨⟨E,htrans⟩,fun _ => rfl⟩

/-- The actual action of a translation is addition in the reconstructed field plane. -/
theorem translation_action_add (T : f.translations hl hq) (a : f.Base hl hq) :
    T.val.affineEquiv a = f.translationEquiv hl hq T + a := by
  let U := (f.translationEquiv hl hq).symm a
  have hh := f.translationEquiv_mul hl hq T U
  rw [Equiv.apply_symm_apply] at hh
  rw [← hh]
  have ha := (f.translationEquiv hl hq).apply_symm_apply a
  change f.translationEquiv hl hq U = a at ha
  rw [← ha]
  rfl

theorem assemble_origin (z : f.Axis) :
    f.assemble hl hq (f.baseOrigin hl hq) z = z.val := by
  apply Subtype.ext
  exact D.project_eq hl hq _ _ (f.k_not_level hl hq z.val) _
    (f.k_ne_affine f.originPoint) z.property (f.level_spec hl hq z.val).2.2

/-- All level charts are aligned by the same translation law. -/
theorem parallelFoot_assemble (c : f.Transverse hl hq) (a : f.Base hl hq) (z : f.Axis) :
    f.parallelFoot hl hq c (f.assemble hl hq a z) =
      a + f.parallelFoot hl hq c z.val := by
  obtain ⟨T,hT⟩ := f.parallelFoot_assemble_translation hl hq c z
  have ho := hT (f.baseOrigin hl hq)
  rw [f.assemble_origin] at ho
  change f.translationEquiv hl hq T = _ at ho
  rw [← hT a,f.translation_action_add,ho,add_comm]

/-- A projection is the base foot plus a displacement depending only on height. -/
theorem parallelFoot_decomposition (c : f.Transverse hl hq) (x : f.Affine) :
    f.parallelFoot hl hq c x = f.foot hl hq x +
      f.parallelFoot hl hq c (f.height hl hq x).val := by
  conv_lhs => rw [← f.assemble_foot_height hl hq x]
  exact f.parallelFoot_assemble hl hq c _ _

/-- Parallel projection carries every spatial affine line into a base-plane
line, including lines which collapse to one point. -/
theorem parallelFoot_collinear (c : f.Transverse hl hq) (a b x : f.Affine)
    (hx : (x : Ω) ∈ D.line a b) :
    (f.parallelFoot hl hq c x : Ω) ∈
      D.line (f.parallelFoot hl hq c a) (f.parallelFoot hl hq c b) := by
  let A := f.parallelFoot hl hq c a
  let B := f.parallelFoot hl hq c b
  let X := f.parallelFoot hl hq c x
  have hc (y : f.Affine) : (c : Ω) ≠ y := fun he => y.property (he ▸ c.property.1)
  have hL (y : f.Affine) : D.line c (f.parallelFoot hl hq c y : Ω) = D.line c y :=
    D.project_line_eq hl hq _ _ c.property.2 _ (hc y)
  by_cases hab : a = b
  · subst b
    have hxa : x = a := Subtype.ext (by
      simpa only [D.line_eq_singleton hq,Set.mem_singleton_iff] using hx)
    subst x
    exact D.left_mem_line _ _
  have hab' : (a : Ω) ≠ b := fun he => hab (Subtype.ext he)
  by_cases hAB : A = B
  · have he : D.line c a = D.line c b := (hL a).symm.trans ((congrArg (fun u : f.Base hl hq => D.line c (u : Ω)) hAB).trans (hL b))
    have hba : (b : Ω) ∈ D.line c a := he.symm ▸ D.right_mem_line _ _
    have hline : D.line a b = D.line c a :=
      D.line_eq_of_mem_of_mem (hc a) (D.right_mem_line _ _) hba hab'
    have hcx : D.line c x = D.line c a :=
      D.line_eq_of_mem (hc a) (hline ▸ hx) (hc x)
    have hXA : X = A := by
      apply Subtype.ext
      apply Subtype.ext
      apply D.project_eq hl hq _ _ c.property.2 _ (hc x)
      · exact hcx.symm ▸ f.parallelFoot_mem_line hl hq c a
      · exact A.property
    change (X : Ω) ∈ D.line A B
    rw [hXA,← hAB]
    exact D.left_mem_line _ _
  · obtain ⟨s,has,hbs,hcs⟩ := D.exists_block_of_three hl (by omega) a b c
    have hAs : (A : Ω) ∈ D.block s :=
      D.line_subset_block hcs has (f.parallelFoot_mem_line hl hq c a)
    have hBs : (B : Ω) ∈ D.block s :=
      D.line_subset_block hcs hbs (f.parallelFoot_mem_line hl hq c b)
    have hXs : (X : Ω) ∈ D.block s := D.line_subset_block hcs
      (D.line_subset_block has hbs hx) (f.parallelFoot_mem_line hl hq c x)
    have hsp : s ≠ f.level hl hq f.originPoint := fun he => c.property.2 (he ▸ hcs)
    have hAB' : (A : Ω) ≠ B := fun he => hAB (Subtype.ext (Subtype.ext he))
    exact D.intersection_eq_line hl hsp ⟨hAs,A.property⟩ ⟨hBs,B.property⟩ hAB' ▸ ⟨hXs,X.property⟩

/-- A chosen point off the base plane projects to any prescribed base point
from a direction at infinity. -/
theorem exists_transverse_projection (z : f.Axis)
    (hz : (z : Ω) ∉ D.block (f.level hl hq f.originPoint)) (a : f.Base hl hq) :
    ∃ c : f.Transverse hl hq, f.parallelFoot hl hq c z.val = a := by
  have hza : (z : Ω) ≠ a := fun he => hz (he.symm ▸ a.property)
  obtain ⟨c,⟨hcl,hcI⟩,_⟩ := D.existsUnique_line_block hl hq z.val.property hza
  have hca : c ≠ (a : Ω) := fun he => a.val.property (he ▸ hcI)
  have hL : D.line c a = D.line (z : Ω) a :=
    D.line_eq_of_mem_of_mem hza hcl (D.right_mem_line _ _) hca
  have hcp : c ∉ D.block (f.level hl hq f.originPoint) := by
    intro hh
    exact hz (D.line_subset_block hh a.property (hL.symm ▸ D.left_mem_line _ _))
  refine ⟨⟨c,hcI,hcp⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply D.project_eq hl hq (f.level hl hq f.originPoint) c hcp (z : Ω) (fun he => z.val.property (he ▸ hcI))
  · have hcz : c ≠ (z : Ω) := fun he => z.val.property (he ▸ hcI)
    have hh := D.line_eq_of_mem_of_mem hza hcl (D.left_mem_line _ _) hcz
    exact hh.symm ▸ D.right_mem_line _ _
  · exact a.property

theorem parallelFoot_axis_injective (c : f.Transverse hl hq) (hck : (c : Ω) ≠ f.k) :
    Function.Injective (fun z : f.Axis => f.parallelFoot hl hq c z.val) := by
  intro z w he
  by_contra hzw
  have hzw' : (z : Ω) ≠ w := fun hh => hzw (Subtype.ext (Subtype.ext hh))
  have hc (y : f.Affine) : (c : Ω) ≠ y := fun hh => y.property (hh ▸ c.property.1)
  have hL (y : f.Affine) : D.line c (f.parallelFoot hl hq c y : Ω) = D.line c y :=
    D.project_line_eq hl hq _ _ c.property.2 _ (hc y)
  have heL : D.line c (z : Ω) = D.line c (w : Ω) := (hL z.val).symm.trans ((congrArg (fun u : f.Base hl hq => D.line c (u : Ω)) he).trans (hL w.val))
  have hzwL : D.line (z : Ω) w = D.line c (z : Ω) :=
    D.line_eq_of_mem_of_mem (hc z.val) (D.right_mem_line _ _)
      (heL.symm ▸ D.right_mem_line _ _) hzw'
  have haxis : D.line (z : Ω) w = D.line f.k f.origin :=
    D.line_eq_of_mem_of_mem (f.k_ne_affine f.originPoint) z.property w.property hzw'
  have hca : (c : Ω) ∈ D.line f.k f.origin := haxis ▸ hzwL.symm ▸ D.left_mem_line _ _
  exact hck ((D.infinity_on_line f.k_mem f.origin_not_mem hca).mp c.property.1)

/-- A transverse projection identifies the third axis with an ordinary
one-dimensional vector line in the already constructed field plane. -/
theorem exists_axis_parameter (z₀ : f.Axis)
    (hz₀ : (z₀ : Ω) ∉ D.block (f.level hl hq f.originPoint))
    (a : f.Base hl hq) (ha : a ≠ 0) :
    ∃ (c : f.Transverse hl hq) (t : f.Axis ≃ f.scalarRing hl hq),
      f.parallelFoot hl hq c z₀.val = a ∧
      ∀ z : f.Axis, f.parallelFoot hl hq c z.val = t z • a := by
  obtain ⟨c,hc⟩ := f.exists_transverse_projection hl hq z₀ hz₀ a
  have hz₀o : (z₀ : Ω) ≠ f.origin := fun he => hz₀
    (he.symm ▸ (f.level_spec hl hq f.originPoint).2.2)
  have hbase (z : f.Axis) : ∃ r : f.scalarRing hl hq,
      f.parallelFoot hl hq c z.val = r • a := by
    have hL : D.line f.origin (z₀ : Ω) = D.line f.k f.origin :=
      D.line_eq_of_mem_of_mem (f.k_ne_affine f.originPoint)
        (D.right_mem_line _ _) z₀.property hz₀o.symm
    have hh := f.parallelFoot_collinear hl hq c f.originPoint z₀.val z.val (hL.symm ▸ z.property)
    rw [show f.parallelFoot hl hq c f.originPoint = 0 from
      f.parallelFoot_fixed hl hq c (f.baseOrigin hl hq),hc] at hh
    obtain ⟨r,hr⟩ := (f.affine_line_scalar hl hq 0 a (f.parallelFoot hl hq c z.val)).mp hh
    exact ⟨r,by simpa only [sub_zero,zero_add] using hr⟩
  let t : f.Axis → f.scalarRing hl hq := fun z => (hbase z).choose
  have ht (z : f.Axis) : f.parallelFoot hl hq c z.val = t z • a := (hbase z).choose_spec
  have hck : (c : Ω) ≠ f.k := by
    intro he
    have hc' : c = f.transverseK hl hq := Subtype.ext he
    have hzero : f.parallelFoot hl hq c z₀.val = 0 := by
      rw [hc',f.parallelFoot_k]
      apply Subtype.ext
      apply Subtype.ext
      exact D.project_eq hl hq _ _ (f.k_not_level hl hq f.originPoint) _
        (f.k_ne_affine z₀.val)
        ((D.line_eq_of_mem (f.k_ne_affine f.originPoint) z₀.property (f.k_ne_affine z₀.val)).symm ▸
          D.right_mem_line _ _) (f.level_spec hl hq f.originPoint).2.2
    exact ha (hc.symm.trans hzero)
  have hinj : Function.Injective t := by
    intro z w he
    apply f.parallelFoot_axis_injective hl hq c hck
    change f.parallelFoot hl hq c z.val = f.parallelFoot hl hq c w.val
    rw [ht z,ht w,he]
  let : Fintype f.Axis := Fintype.ofFinite _
  let : Fintype (f.scalarRing hl hq) := Fintype.ofFinite _
  have hbij : Function.Bijective t := (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨hinj,by rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,
      (f.axes_card hl hq).2.2,f.scalarField_card hl hq]⟩
  exact ⟨c,Equiv.ofBijective t hbij,hc,ht⟩

/-- The difference of two transverse projections always has the direction
where their centers' line meets the base plane. -/
theorem parallelFoot_difference_direction (c d : f.Transverse hl hq) (hcd : c ≠ d) :
    ∃ e : f.Direction hl hq, ∀ x : f.Affine,
      f.parallelFoot hl hq c x - f.parallelFoot hl hq d x ∈ f.axisGroup hl hq e := by
  have hcd' : (c : Ω) ≠ d := fun he => hcd (Subtype.ext he)
  let e := D.project hl hq (f.level hl hq f.originPoint) c c.property.2 d hcd'
  have heL : e ∈ D.line c d := D.project_mem_line hl hq _ _ _ _ _
  have hep : e ∈ D.block (f.level hl hq f.originPoint) := D.project_mem_block hl hq _ _ _ _ _
  have heI : e ∈ D.block f.infinity := D.line_subset_block c.property.1 d.property.1 heL
  let e' : f.Direction hl hq := ⟨e,heI,hep⟩
  refine ⟨e',?_⟩
  intro x
  let A := f.parallelFoot hl hq c x
  let B := f.parallelFoot hl hq d x
  by_cases hAB : A = B
  · change A-B ∈ f.axisGroup hl hq e'
    rw [hAB,sub_self]
    exact (f.axisGroup hl hq e').zero_mem
  · have hAB' : (A : Ω) ≠ B := fun hh => hAB (Subtype.ext (Subtype.ext hh))
    obtain ⟨p,hcp,hdp,hxp⟩ := D.exists_block_of_three hl (by omega) c d x
    have hAp : (A : Ω) ∈ D.block p :=
      D.line_subset_block hcp hxp (f.parallelFoot_mem_line hl hq c x)
    have hBp : (B : Ω) ∈ D.block p :=
      D.line_subset_block hdp hxp (f.parallelFoot_mem_line hl hq d x)
    have hep' : e ∈ D.block p := D.line_subset_block hcp hdp heL
    have hpp : p ≠ f.level hl hq f.originPoint := fun hh => c.property.2 (hh ▸ hcp)
    have heAB : e ∈ D.line A B :=
      D.intersection_eq_line hl hpp ⟨hAp,A.property⟩ ⟨hBp,B.property⟩ hAB' ▸ ⟨hep',hep⟩
    have heB : e ≠ (B : Ω) := fun hh => B.val.property (hh ▸ heI)
    have hL : D.line e B = D.line A B :=
      D.line_eq_of_mem_of_mem hAB' heAB (D.right_mem_line _ _) heB
    apply (f.mem_axisGroup hl hq e' (A-B)).mpr
    apply (f.affine_line_add hl hq A B e').mp
    exact hL.symm ▸ D.left_mem_line _ _

private theorem spatial_zero_smul (a : f.Base hl hq) :
    (0 : f.scalarRing hl hq) • a = 0 := rfl

theorem fieldPlaneCoordinates_unitI :
    f.fieldPlaneCoordinates hl hq (f.axisUnit hl hq (f.directionI hl hq)).val = (1,0) := by
  apply (f.fieldPlaneCoordinates hl hq).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change _ = f.planeLinearMap hl hq (1,0)
  simp only [planeLinearMap,LinearMap.coe_mk,AddHom.coe_mk,one_smul,f.spatial_zero_smul,add_zero]

theorem fieldPlaneCoordinates_unitJ :
    f.fieldPlaneCoordinates hl hq (f.axisUnit hl hq (f.directionJ hl hq)).val = (0,1) := by
  apply (f.fieldPlaneCoordinates hl hq).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  change _ = f.planeLinearMap hl hq (0,1)
  simp only [planeLinearMap,LinearMap.coe_mk,AddHom.coe_mk,one_smul,f.spatial_zero_smul,zero_add]

/-- Incidence forces two independent spatial projections to use the same
field parameter on the transverse axis. -/
theorem exists_compatible_axis_parameters :
    ∃ (c d : f.Transverse hl hq) (t : f.Axis ≃ f.scalarRing hl hq),
      (∀ z : f.Axis, f.parallelFoot hl hq c z.val =
        t z • (f.axisUnit hl hq (f.directionI hl hq)).val) ∧
      (∀ z : f.Axis, f.parallelFoot hl hq d z.val =
        t z • (f.axisUnit hl hq (f.directionJ hl hq)).val) := by
  obtain ⟨z₀,hz₀⟩ := f.exists_axis_off_base hl hq
  let a := (f.axisUnit hl hq (f.directionI hl hq)).val
  let b := (f.axisUnit hl hq (f.directionJ hl hq)).val
  obtain ⟨c,t,hc,ht⟩ := f.exists_axis_parameter hl hq z₀ hz₀ a (f.axisUnit_ne_zero hl hq _)
  obtain ⟨d,s,hd,hs⟩ := f.exists_axis_parameter hl hq z₀ hz₀ b (f.axisUnit_ne_zero hl hq _)
  have hab : a ≠ b := by
    intro he
    have hh := congrArg (f.fieldPlaneCoordinates hl hq) he
    rw [f.fieldPlaneCoordinates_unitI,f.fieldPlaneCoordinates_unitJ] at hh
    exact one_ne_zero (congrArg Prod.fst hh)
  have hcd : c ≠ d := by
    intro he
    exact hab (hc.symm.trans (he.symm ▸ hd))
  obtain ⟨e,he⟩ := f.parallelFoot_difference_direction hl hq c d hcd
  have heab : a-b ∈ f.axisGroup hl hq e := by
    have hh := he z₀.val
    rw [hc,hd] at hh
    exact hh
  refine ⟨c,d,t,ht,?_⟩
  intro z
  obtain ⟨r,hr⟩ := (f.mem_axisGroup_iff_smul hl hq e heab (sub_ne_zero.mpr hab) _).mp (he z.val)
  rw [ht z,hs z] at hr
  have hh := congrArg (f.fieldPlaneCoordinates hl hq) hr
  dsimp only [a,b] at hh
  simp only [map_smul,map_sub,f.fieldPlaneCoordinates_unitI,f.fieldPlaneCoordinates_unitJ] at hh
  have h₁ := congrArg Prod.fst hh
  have h₂ := congrArg Prod.snd hh
  change t z * 1 - s z * 0 = r * (1-0) at h₁
  change t z * 0 - s z * 1 = r * (0-1) at h₂
  have ht' : r = t z := by simpa only [sub_zero,mul_one,mul_zero] using h₁.symm
  have hs' : r = s z := by simpa only [zero_sub,mul_neg,mul_one,mul_zero,neg_inj] using h₂.symm
  rw [hs z,← hs',ht']

end Theory.GroupAction.SymplecticRankThree.AffineFrame
