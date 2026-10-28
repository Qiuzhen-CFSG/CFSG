module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Residuals.Index.Cubic
public import Theory.GroupTheory.CubicClosureTwoKernel
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.WreathOuter
public import Theory.Mathieu.M22.TripleCover.CubicGeneration

/-!
# The equality-row Mathieu obstruction without a residual-index identity

When Kc = K, every cubic element of the actual partner belongs to the
solvable wreath residual. Hence the partner's cubic-generated subgroup is
solvable. This property descends to subgroups and through two-group kernels.
The Mathieu triple cover is cubically generated and is not solvable, so
no subgroup of the partner has that two-core quotient.

The application retains the literal subgroup R and its quotient by O₂(R).
It removes the extra placement R ≤ Kc from this terminal obstruction; it
does not assert the earlier plane-uniqueness reductions or the equality
Kc = O^{3′}(Mc).

Source: Aschbacher--Smith 15.2.12(4) and the final argument for 15.2.15,
printed pp.1111 and 1118, refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
open Section01 Section03 ChapterD ChapterD.UniqueFactor
open Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H B : Subgroup G}
variable {h : ChosenSmallSource T M Mc V}

/-- The actual partner has solvable cubic closure in the equality row. -/
theorem ResidualInput.cubic_closure_solvable_of_eq
    (d : ResidualInput h H B) (he : partnerSpan H Mc = residual H) :
    Group.IsSolvable (closure {x : Mc | orderOf x = 3}) := by
  obtain ⟨e⟩ := d.quotient
  let : Group.IsSolvable BinaryFourPlus.Wreath := BinaryFourPlus.wreath_isSolvable
  let : Group.IsSolvable (H ⧸ pCore 2 H) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  let : Group.IsNilpotent (pCore 2 H) := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  let : Group.IsSolvable H := Group.isSolvable_of_ker_le_range
    (pCore 2 H).subtype (QuotientGroup.mk' (pCore 2 H))
    (by rw [QuotientGroup.ker_mk', range_subtype])
  let C := closure {x : Mc | orderOf x = 3}
  have hCH : C ≤ H.subgroupOf Mc := by
    apply (closure_le _).mpr
    intro x hx
    exact (map_subtype_le (pResidual 2 H))
      (d.cubic_mem_residual_of_eq he x (hx ▸ pow_orderOf_eq_one x))
  let f : C →* H := (Mc.subtype.comp C.subtype).codRestrict H (fun x => hCH x.property)
  exact Group.isSolvable_of_isSolvable_injective (f := f)
    (fun x y hxy => Subtype.ext (Subtype.ext (congrArg (fun z : H => (z : G)) hxy)))

/-- The terminal triple-Mathieu section is impossible anywhere in the actual
partner in the equality row; no prime-complement residual equality is required. -/
theorem ResidualInput.no_mathieu_section_in_partner_of_eq
    (d : ResidualInput h H B) (he : partnerSpan H Mc = residual H)
    (R : Subgroup G) (hR : R ≤ Mc)
    (e : (R ⧸ pCore 2 R) ≃* M22TripleCover) : False := by
  have hs := solvable_cubic_closure_of_injective (inclusion hR)
    (inclusion_injective hR) (d.cubic_closure_solvable_of_eq he)
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 R))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
    exact pCore_isPGroup
  exact M22TripleCover.cubic_closure_not_solvable
    (solvable_cubic_closure_of_two_kernel f hf hk hs)

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
