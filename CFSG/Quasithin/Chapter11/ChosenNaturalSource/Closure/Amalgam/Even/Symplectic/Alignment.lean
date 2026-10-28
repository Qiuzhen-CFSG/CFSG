module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Critical
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry

/-!
# Field-line transport for the even symplectic critical pair

Transitivity on nonzero vectors of the actual symplectic matrix group lifts
through the supplied quotient marking. It makes the original component
transitive on the ambient preimages of field lines. A common field line on a
conjugate therefore supplies a right correction into the original G₁, without
changing that conjugate of V. The final application contradicts abelianness
of W once the separate reverse-field-line calculation is supplied.

Source: Aschbacher--Smith, 11.5.8, refs/quasithin.pdf, printed p.784.
This module does not assert the missing quadratic alternatives.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Closure.Geometry D)
variable (m : ActionEquiv D.centralQuotientAction
  (restrictScalars (k := ZMod 2) (symplecticNatural (k := E.input.field.Carrier) 2)))

private theorem line_transitive
    (U W : Submodule E.input.field.Carrier (Coordinates.sp4 m).Space)
    (hU : Module.finrank E.input.field.Carrier U = 1)
    (hW : Module.finrank E.input.field.Carrier W = 1) :
    ∃ s : (Coordinates.sp4 m).ModelGroup,
      ∀ x, (Coordinates.sp4 m).modelAction s x ∈ W ↔ x ∈ U := by
  let F := E.input.field.Carrier
  obtain ⟨u, hu, hspanU⟩ := finrank_eq_one_iff'.mp hU
  obtain ⟨w, hw, hspanW⟩ := finrank_eq_one_iff'.mp hW
  have hu0 : (u.val : Theory.SpecificGroups.SymplecticFour.Vector F) ≠ 0 := by
    intro he
    exact hu (Subtype.ext he)
  have hw0 : (w.val : Theory.SpecificGroups.SymplecticFour.Vector F) ≠ 0 := by
    intro he
    exact hw (Subtype.ext he)
  obtain ⟨s, hs⟩ := Theory.SpecificGroups.SymplecticFour.TwoLocalCover.nonzero_vector_transitive hu0 hw0
  refine ⟨s, fun x => ?_⟩
  have he : (Coordinates.sp4 m).modelAction s u.val = w.val := hs
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := hspanW ⟨_, hx⟩
    have ha' : a • w.val = (Coordinates.sp4 m).modelAction s x := congrArg Subtype.val ha
    have hh : a • u.val = x :=
      ((Coordinates.sp4 m).modelAction.apply_bijective s).1 (by rw [map_smul, he, ha'])
    rw [← hh]
    exact U.smul_mem a u.property
  · intro hx
    obtain ⟨a, ha⟩ := hspanU ⟨x, hx⟩
    have ha' : a • u.val = x := congrArg Subtype.val ha
    rw [← ha', map_smul, he]
    exact W.smul_mem a w.property

/-- The original component is transitive on the actual marked field lines. -/
theorem fieldLine_transitive {A B : Subgroup G}
    (hA : IsFieldLine E (.sp4 m) A) (hB : IsFieldLine E (.sp4 m) B) :
    ∃ l ∈ L, A.map (MulAut.conj l).toMonoidHom = B := by
  obtain ⟨U, hU, rfl⟩ := hA
  obtain ⟨W, hW, rfl⟩ := hB
  obtain ⟨s, hs⟩ := line_transitive E m U W hU hW
  obtain ⟨l, hl⟩ := (Coordinates.sp4 m).quotientMap_surjective s
  let c := Coordinates.sp4 m
  let α := V.normalizerMonoidHom (inclusion D.normalizes l)
  have hmem (v : V) : (α v : G) ∈ c.preimage W ↔ (v : G) ∈ c.preimage U := by
    rw [c.mem_preimage W (α v), c.mem_preimage U v]
    change (c.projection (α v)).toAdd ∈ W ↔ (c.projection v).toAdd ∈ U
    rw [c.projection_component_conjugation l v, hl]
    exact hs _
  refine ⟨l.val, l.property, ?_⟩
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (hmem ⟨x, D.centralQuotientPreimage_le _ hx⟩).mpr hx
  · intro x hx
    let xV : V := ⟨x, D.centralQuotientPreimage_le _ hx⟩
    have hα : α (α.symm xV) = xV := α.apply_symm_apply xV
    refine ⟨(α.symm xV).val, ?_, ?_⟩
    · apply (hmem (α.symm xV)).mp
      rw [hα]
      exact hx
    · exact congrArg Subtype.val hα

omit [Finite G] in
/-- Composition follows left conjugation: first b, then a. -/
theorem map_conj_mul (A : Subgroup G) (a b : G) :
    A.map (MulAut.conj (a*b)).toMonoidHom =
      (A.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, mul_inv_rev, mul_assoc]

omit [Finite G] in
/-- Inverse conjugations cancel on the original ambient subgroup. -/
theorem map_conj_cancel (A : Subgroup G) (g : G) :
    (A.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = A := by
  rw [← map_conj_mul]
  rw [inv_mul_cancel]
  have h : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [h, map_id]

/-- A common field line supplies the exact premise of the amalgam transporter. -/
theorem line_alignment
    (f : InvariantFlag (.sp4 m)) (hm : FlagMatch E f) (g : G)
    (hline : IsFieldLine E (.sp4 m) (E.V₁.map (MulAut.conj g⁻¹).toMonoidHom)) :
    ∃ l ∈ L, (E.V₁.map (MulAut.conj l).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = E.V₁ := by
  obtain ⟨l, hl, he⟩ := fieldLine_transitive E m hm.point_isFieldLine hline
  refine ⟨l, hl, ?_⟩
  rw [he]
  simpa only [inv_inv] using map_conj_cancel E.V₁ g⁻¹

/-- The correction is on the right and preserves the original conjugate module. -/
theorem exists_right_correction
    (f : InvariantFlag (.sp4 m)) (hm : FlagMatch E f) (g : G)
    (hline : IsFieldLine E (.sp4 m) (E.V₁.map (MulAut.conj g⁻¹).toMonoidHom)) :
    ∃ l ∈ L, g*l ∈ E.G₁ ∧
      V.map (MulAut.conj (g*l)).toMonoidHom = V.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨l, hl, he⟩ := line_alignment E m f hm g hline
  refine ⟨l, hl, mem_normalizer_iff_map_conj_eq.mpr ?_, ?_⟩
  · exact (map_conj_mul E.V₁ g l).trans he
  · have hv : V.map (MulAut.conj l).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (D.normalizes hl)
    rw [map_conj_mul, hv]

/-- The common-field-line conclusion contradicts abelianness of the original W. -/
theorem false_of_common_fieldLine
    (f : InvariantFlag (.sp4 m)) (hm : FlagMatch E f)
    (hab : IsMulCommutative E.W) (g : G)
    (hn : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hline : IsFieldLine E (.sp4 m) (E.V₁.map (MulAut.conj g⁻¹).toMonoidHom)) : False :=
  hn (Amalgam.commutes_of_line_alignment E hab g (line_alignment E m f hm g hline))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic
