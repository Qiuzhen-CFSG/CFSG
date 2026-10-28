module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.GraphSymplectic
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.GraphFixed
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FiveCensus
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Graph fixed groups inside the same U₅(4) extension

The explicit fixed-group comparison identifies the native graph fixed group
with Sp₄ over the stored four-element fixed field. For any element of the
specified extension, its fixed native group maps by the literal base map
onto the inner part of its centralizer. When that element is the graph
involution this gives order 979200 and Sylow order 256, on the same extension.

These are native inputs to F.4.37--38, printed pp.293--294 of
`refs/quasithin.pdf`. The graph-element equation is an explicit local input;
selection of such an element from S<T, the full fixed local amalgam and
ambient centralizer Sylow placement remain separate source obligations.
No ambient centralizer order or S=T is asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.UnitaryFive.GraphFixed
namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model

/-- The graph-fixed group in the actual projective model, over its stored fixed field. -/
def graph_fixed_symplectic_equiv (U : Model 4) :
    (projectiveAut U.form U.matrix).fixedSubgroup ≃*
      Matrix.PSp4Three.Sp 2 (FixedBy.subfield U.F U.form.conj) :=
  fixedProjectiveSymplecticEquiv U.form U.matrix
    (by simpa using U.card) U.conjugation

/-- The fixed field has four elements; the matrix field still has sixteen. -/
theorem graph_fixed_field_card (U : Model 4) :
    Nat.card (FixedBy.subfield U.F U.form.conj)=4 :=
  FiniteField.card_fixed_of_quadratic_frobenius U.form.conj 2 2
    (by decide) (by simpa using U.card) U.conjugation

/-- Native graph-fixed order for the literal scalar-quotient carrier. -/
theorem graph_fixed_card (U : Model 4) :
    Nat.card (projectiveAut U.form U.matrix).fixedSubgroup=979200 := by
  rw [Nat.card_congr (graph_fixed_symplectic_equiv U).toEquiv]
  change Nat.card (Theory.SpecificGroups.SymplecticFour.Sp
    (FixedBy.subfield U.F U.form.conj))=979200
  rw [Theory.SpecificGroups.SymplecticFour.card_sp,graph_fixed_field_card]
  norm_num

end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model

namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
variable (U : GreenBook.UnitaryFive.Model 4) (E : FiveExtension U)

private theorem inner_mem_centralizer_iff (f : E.carrier) (g : U.Carrier) :
    E.baseHom g ∈ centralizer ({f} : Set E.carrier) ↔ f.val g=g := by
  have ha : f.val * MulAut.conj g * f.val⁻¹ = MulAut.conj (f.val g) := by
    apply MulEquiv.ext
    intro y
    change f.val (g * (f.val.symm y) * g⁻¹)=f.val g*y*(f.val g)⁻¹
    rw [map_mul,map_mul,map_inv,f.val.apply_symm_apply]
  constructor
  · intro hg
    apply five_conj_injective U
    rw [←ha]
    have he := congrArg Subtype.val (mem_centralizer_singleton_iff.mp hg)
    change MulAut.conj g*f.val=f.val*MulAut.conj g at he
    have he := he.symm
    rw [he,mul_inv_cancel_right]
  · intro hg
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    change MulAut.conj g*f.val=f.val*MulAut.conj g
    symm
    exact (mul_inv_eq_iff_eq_mul).mp (ha.trans (congrArg MulAut.conj hg))

/-- The inner part of a specified extension element's centralizer is its
actual fixed subgroup in the native carrier, with the same base map. -/
def innerCentralizerEquiv (f : E.carrier) :
    f.val.fixedSubgroup ≃* (E.baseHom.range ⊓ centralizer ({f} : Set E.carrier) : Subgroup E.carrier) :=
  MulEquiv.ofBijective
    ((E.baseHom.comp f.val.fixedSubgroup.subtype).codRestrict
      (E.baseHom.range ⊓ centralizer ({f} : Set E.carrier)) (fun g =>
      ⟨⟨g.val,rfl⟩,(inner_mem_centralizer_iff U E f g.val).mpr
        ((MulAut.mem_fixedSubgroup _ _).mp g.property)⟩))
    ⟨fun g h he => Subtype.ext ((E.baseHom_injective (five_conj_injective U))
        (congrArg Subtype.val he)),by
      rintro ⟨x,hx⟩
      obtain ⟨g,rfl⟩ := hx.1
      refine ⟨⟨g,(MulAut.mem_fixedSubgroup _ _).mpr
        ((inner_mem_centralizer_iff U E f g).mp hx.2)⟩,?_⟩
      rfl⟩

/-- The equivalence is the literal base map into this same extension. -/
theorem innerCentralizerEquiv_apply (f : E.carrier) (g : f.val.fixedSubgroup) :
    (innerCentralizerEquiv U E f g).val=E.baseHom g.val := by rfl

/-- Sp₄(4) is the exact inner centralizer of the graph element whenever that
element lies in the specified extension. No full centralizer placement is inferred. -/
def graphInnerCentralizerEquiv (f : E.carrier)
    (hf : f.val=projectiveAut U.form U.matrix) :
    (E.baseHom.range ⊓ centralizer ({f} : Set E.carrier) : Subgroup E.carrier) ≃*
      Matrix.PSp4Three.Sp 2 (FixedBy.subfield U.F U.form.conj) :=
  (innerCentralizerEquiv U E f).symm.trans
    ((MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup hf)).trans
      U.graph_fixed_symplectic_equiv)

/-- The actual inner centralizer order in the same specified extension. -/
theorem graph_inner_centralizer_card (f : E.carrier)
    (hf : f.val=projectiveAut U.form U.matrix) :
    Nat.card (E.baseHom.range ⊓ centralizer ({f} : Set E.carrier) : Subgroup E.carrier)=979200 := by
  rw [←Nat.card_congr (innerCentralizerEquiv U E f).toEquiv,hf]
  exact U.graph_fixed_card

/-- Every Sylow subgroup of this inner centralizer has order 4⁴. This is
an inner order calculation, not Sylow placement in the full ambient centralizer. -/
theorem graph_inner_centralizer_sylow_card (f : E.carrier)
    (hf : f.val=projectiveAut U.form U.matrix)
    (P : Sylow 2 (E.baseHom.range ⊓ centralizer ({f} : Set E.carrier) : Subgroup E.carrier)) :
    Nat.card P=256 := by
  rw [P.card_eq_multiplicity,graph_inner_centralizer_card U E f hf]
  rw [show 979200=2^8*3825 from rfl,
    Nat.factorization_mul (by decide) (by decide),Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2∣3825)]
  norm_num

end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
