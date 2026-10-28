module
public import CFSG.Quasithin.ChapterF.Section04.UnitaryFiveSource.GraphSymplectic
public import Theory.GroupAction.FixedSubgroupConjugate

/-!
# Conjugated graph actors on the same projective extension

For f=b sigma b⁻¹, transport sigma-fixed elements by b and then by the
literal base map into the specified extension. This yields the same Sp₄(4)
inner centralizer and its orders without requiring b or sigma to belong to
that extension. Every native subgroup is pulled back along b explicitly,
including the two parabolics and their whole flag overlap.

Source: F.4.29(2) and F.4.37, printed pp.289,293 of refs/quasithin.pdf.
This is transport for a supplied conjugated-graph equation. The equation
itself must still be proved for the selected marked outer involution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.UnitaryFive.GraphFixed
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
variable (U : GreenBook.UnitaryFive.Model 4) (E : FiveExtension U)

/-- The original graph-fixed group maps into the same extension through b
followed by the literal base map; b need not belong to the extension. -/
def conjugateGraphInnerEquiv (f : E.carrier) (b : MulAut U.Carrier)
    (hf : f.val=b*projectiveAut U.form U.matrix*b⁻¹) :
    (projectiveAut U.form U.matrix).fixedSubgroup ≃*
      (E.baseHom.range ⊓ centralizer ({f} : Set E.carrier) : Subgroup E.carrier) :=
  ((MulAut.fixedConjugateEquiv (projectiveAut U.form U.matrix) b).trans
    (MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup hf.symm))).trans
      (innerCentralizerEquiv U E f)

theorem conjugateGraphInnerEquiv_apply (f : E.carrier) (b : MulAut U.Carrier)
    (hf : f.val=b*projectiveAut U.form U.matrix*b⁻¹)
    (x : (projectiveAut U.form U.matrix).fixedSubgroup) :
    (conjugateGraphInnerEquiv U E f b hf x).val=E.baseHom (b x.val) := by
  simp only [conjugateGraphInnerEquiv,MulEquiv.trans_apply,
    innerCentralizerEquiv_apply,MulEquiv.subgroupCongr_apply,
    MulAut.fixedConjugateEquiv_apply]

/-- Exact endpoint transport: the chosen flag is pulled back by b. -/
theorem conjugateGraphInnerEquiv_mem_endpoint (f : E.carrier) (b : MulAut U.Carrier)
    (hf : f.val=b*projectiveAut U.form U.matrix*b⁻¹)
    (x : (projectiveAut U.form U.matrix).fixedSubgroup) (i : Bool) :
    (conjugateGraphInnerEquiv U E f b hf x).val ∈ E.family i ↔
      x.val ∈ (SourceExtension.nativeFamily
        (P₀ := U.leftParabolic) (P₁ := U.rightParabolic) i).comap b.toMonoidHom := by
  rw [conjugateGraphInnerEquiv_apply,E.baseHom_mem_family_iff (five_conj_injective U)]
  rfl

/-- Sp₄(4) identifies the inner centralizer of a conjugated graph actor. -/
def conjugateGraphInnerCentralizerEquiv (f : E.carrier) (b : MulAut U.Carrier)
    (hf : f.val=b*projectiveAut U.form U.matrix*b⁻¹) :
    (E.baseHom.range ⊓ centralizer ({f} : Set E.carrier) : Subgroup E.carrier) ≃*
      Matrix.PSp4Three.Sp 2 (FixedBy.subfield U.F U.form.conj) :=
  (conjugateGraphInnerEquiv U E f b hf).symm.trans U.graph_fixed_symplectic_equiv

theorem conjugate_graph_inner_centralizer_card (f : E.carrier) (b : MulAut U.Carrier)
    (hf : f.val=b*projectiveAut U.form U.matrix*b⁻¹) :
    Nat.card (E.baseHom.range ⊓ centralizer ({f} : Set E.carrier) : Subgroup E.carrier)=979200 := by
  rw [←Nat.card_congr (conjugateGraphInnerEquiv U E f b hf).toEquiv]
  exact U.graph_fixed_card

theorem conjugate_graph_inner_centralizer_sylow_card (f : E.carrier) (b : MulAut U.Carrier)
    (hf : f.val=b*projectiveAut U.form U.matrix*b⁻¹)
    (P : Sylow 2 (E.baseHom.range ⊓ centralizer ({f} : Set E.carrier) : Subgroup E.carrier)) :
    Nat.card P=256 := by
  rw [P.card_eq_multiplicity,conjugate_graph_inner_centralizer_card U E f b hf]
  rw [show 979200=2^8*3825 from rfl,
    Nat.factorization_mul (by decide) (by decide),Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2∣3825)]
  norm_num

/-- Every fixed native subgroup is transported with the same base map.
Applying this to either parabolic or their intersection retains the entire flag. -/
def conjugateGraphFixedSubgroupEquiv (f : E.carrier) (b : MulAut U.Carrier)
    (hf : f.val=b*projectiveAut U.form U.matrix*b⁻¹) (P : Subgroup U.Carrier) :
    (P.comap b.toMonoidHom ⊓ (projectiveAut U.form U.matrix).fixedSubgroup : Subgroup U.Carrier) ≃*
      (P.map E.baseHom ⊓ centralizer ({f} : Set E.carrier) : Subgroup E.carrier) :=
  MulEquiv.ofBijective
    ((E.baseHom.comp (b.toMonoidHom.comp
      (P.comap b.toMonoidHom ⊓ (projectiveAut U.form U.matrix).fixedSubgroup).subtype)).codRestrict
      (P.map E.baseHom ⊓ centralizer ({f} : Set E.carrier)) (fun x => by
        refine ⟨mem_map_of_mem _ x.property.1,?_⟩
        have hh := (conjugateGraphInnerEquiv U E f b hf ⟨x.val,x.property.2⟩).property.2
        rw [conjugateGraphInnerEquiv_apply] at hh
        exact hh))
    ⟨fun x y h => Subtype.ext (b.injective
        (E.baseHom_injective (five_conj_injective U) (congrArg Subtype.val h))), by
      rintro ⟨y,hyP,hyC⟩
      obtain ⟨v,hv,rfl⟩ := hyP
      let z := (conjugateGraphInnerEquiv U E f b hf).symm ⟨E.baseHom v,⟨v,rfl⟩,hyC⟩
      have hz : b z.val=v := by
        apply E.baseHom_injective (five_conj_injective U)
        have he := congrArg Subtype.val
          ((conjugateGraphInnerEquiv U E f b hf).apply_symm_apply ⟨E.baseHom v,⟨v,rfl⟩,hyC⟩)
        rw [conjugateGraphInnerEquiv_apply] at he
        exact he
      refine ⟨⟨z.val,?_,z.property⟩,?_⟩
      · change b z.val ∈ P
        exact hz.symm ▸ hv
      · apply Subtype.ext
        change E.baseHom (b z.val)=E.baseHom v
        rw [hz]⟩

theorem conjugateGraphFixedSubgroupEquiv_apply (f : E.carrier) (b : MulAut U.Carrier)
    (hf : f.val=b*projectiveAut U.form U.matrix*b⁻¹) (P : Subgroup U.Carrier)
    (x : (P.comap b.toMonoidHom ⊓ (projectiveAut U.form U.matrix).fixedSubgroup : Subgroup U.Carrier)) :
    (conjugateGraphFixedSubgroupEquiv U E f b hf P x).val=E.baseHom (b x.val) := by
  rfl
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary
