module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Geometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import Theory.Representation.SpecialLinearThreeTransitivity

/-!
# Actual field-line transitivity for the even SL₃ pair

The full determinant-one group is transitive on nonzero natural vectors.
Lift a matrix through the original L/O₂(L) marking and transport field
subspaces through the original quotient. This gives the right correction
g*l and applies the literal closure commutation theorem. The reciprocal
field-line premise is not discharged by this module.
Source: Aschbacher--Smith, 11.5.8, refs/quasithin.pdf, printed p.784.
-/

public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Linear
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} {E : Closure.Geometry D}
  (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))

private theorem lines_transitive
    (P Q : Submodule E.input.field.Carrier (Coordinates.sl3 m).Space)
    (hP : Module.finrank E.input.field.Carrier P = 1)
    (hQ : Module.finrank E.input.field.Carrier Q = 1) :
    ∃ a : (Coordinates.sl3 m).ModelGroup,
      P.map ((Coordinates.sl3 m).modelAction a) = Q := by
  have hPn : P ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hP
    omega
  have hQn : Q ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hQ
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hPn
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQn
  obtain ⟨a, ha⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three v w hv0 hw0
  refine ⟨a, ?_⟩
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hP hv hv0,
    eq_span_singleton_of_mem_of_finrank_eq_one hQ hw hw0,
    Submodule.map_span]
  simp only [Set.image_singleton]
  exact congrArg (fun x => Submodule.span E.input.field.Carrier {x}) ha

private theorem preimage_map (P : Submodule E.input.field.Carrier (Coordinates.sl3 m).Space)
    (l : L) :
    ((Coordinates.sl3 m).preimage P).map (MulAut.conj (l : G)).toMonoidHom =
      (Coordinates.sl3 m).preimage
        (P.map ((Coordinates.sl3 m).modelAction ((Coordinates.sl3 m).quotientMap l))) := by
  let c := Coordinates.sl3 m
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    let v' : V := ⟨v, D.centralQuotientPreimage_le _ hv⟩
    apply (c.mem_preimage _ (V.normalizerMonoidHom (inclusion D.normalizes l) v')).mpr
    change (c.projection (V.normalizerMonoidHom (inclusion D.normalizes l) v')).toAdd ∈ _
    rw [c.projection_component_conjugation]
    exact ⟨(c.projection v').toAdd, (c.mem_preimage P v').mp hv, rfl⟩
  · intro v hv
    let v' : V := ⟨v, D.centralQuotientPreimage_le _ hv⟩
    let w := V.normalizerMonoidHom (inclusion D.normalizes l⁻¹) v'
    refine ⟨w, ?_, ?_⟩
    · apply (c.mem_preimage P w).mpr
      change (c.projection w).toAdd ∈ P
      dsimp only [w]
      rw [c.projection_component_conjugation]
      obtain ⟨x, hx, he⟩ := (c.mem_preimage _ v').mp hv
      change c.modelAction (c.quotientMap l) x = (c.projection v').toAdd at he
      rw [← he, map_inv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      exact hx
    · change (l : G) * ((l : G)⁻¹ * v * ((l : G)⁻¹)⁻¹) * (l : G)⁻¹ = v
      group

/-- Transitivity on the actual marked field lines, lifted through L/O₂(L). -/
theorem fieldLines_transitive {A B : Subgroup G}
    (hA : IsFieldLine E (.sl3 m) A) (hB : IsFieldLine E (.sl3 m) B) :
    ∃ l ∈ L, A.map (MulAut.conj l).toMonoidHom = B := by
  obtain ⟨P, hP, rfl⟩ := hA
  obtain ⟨Q, hQ, rfl⟩ := hB
  obtain ⟨a, ha⟩ := lines_transitive m P Q hP hQ
  obtain ⟨l, hl⟩ := (Coordinates.sl3 m).quotientMap_surjective a
  refine ⟨l, l.property, ?_⟩
  rw [preimage_map, hl, ha]

/-- A field line on the second module supplies the correct right correction. -/
theorem line_alignment (f : InvariantFlag (.sl3 m)) (hm : FlagMatch E f) (g : G)
    (hline : IsFieldLine E (.sl3 m) (E.V₁.map (MulAut.conj g⁻¹).toMonoidHom)) :
    ∃ l ∈ L, (E.V₁.map (MulAut.conj l).toMonoidHom).map
      (MulAut.conj g).toMonoidHom = E.V₁ := by
  obtain ⟨l, hl, he⟩ := fieldLines_transitive m hm.point_isFieldLine hline
  refine ⟨l, hl, ?_⟩
  rw [he, map_map]
  have hh : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      inv_inv, MonoidHom.id_apply]
    group
  rw [hh, map_id]

/-- Application of actual line transitivity to the original closure contradiction. -/
theorem commutes_of_fieldLine (f : InvariantFlag (.sl3 m)) (hm : FlagMatch E f)
    (hab : IsMulCommutative E.W) (g : G)
    (hline : IsFieldLine E (.sl3 m) (E.V₁.map (MulAut.conj g⁻¹).toMonoidHom)) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ :=
  Amalgam.commutes_of_line_alignment E hab g (line_alignment m f hm g hline)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Linear
