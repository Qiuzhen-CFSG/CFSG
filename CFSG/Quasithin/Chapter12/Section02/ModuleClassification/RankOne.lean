module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.Branches
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.AlternatingCopies

/-!
# The surviving rank-one source model enters the seven-case list

The earlier rank-one exit supplies a conjugation model on the original V.
Its coordinates identify the chosen subspace with the natural A₅ module.
That module has no fixed vectors, so the literal central quotient has the
same coordinates. The result is precisely 12.2.2(3d), with the canonical
L/C_L(V) projection, together with the binary dimension-four conclusion.
Source: Aschbacher--Smith 6.2.20 and 12.2.2(3d), pp.691 and 795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem a5_fixed_zero (v : BinaryPermutation.natural (Fin 5))
    (hv : ∀ a, Chapter6.Source.a5Module a v = v) : v = 0 := by
  let ρ := Chapter6.Source.a5Module
  let : IsIrreducible ρ := BinaryPermutation.alternatingNatural_isIrreducible (by decide)
  have hf : Function.Injective ρ :=
    (BinaryPermutation.naturalRepresentation_injective (Fin 5) (by decide)).comp
      (alternatingGroup (Fin 5)).subtype_injective
  have hz : invariants (ρ.comp (⊤ : Subgroup (alternatingGroup (Fin 5))).subtype) = ⊥ := by
    by_contra h
    have hk := ρ.le_ker_of_normal_invariants_ne_bot ⊤ h
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    obtain ⟨a,ha⟩ := exists_ne (1 : alternatingGroup (Fin 5))
    exact ha (hf ((hk (mem_top a)).trans (map_one ρ).symm))
  exact hz.le (fun a => hv a)

/-- A full natural A₅ conjugation model produces the exact printed
central-quotient alternative on the same chosen space. -/
theorem alternatives_of_a5_conjugationModel
    (hmodel : Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module) :
    ModuleAlternatives1222 D := by
  obtain ⟨e,f,hf⟩ := hmodel
  let b := D.spaceEquiv.trans f
  let aA : D.space ≃+ BinaryPermutation.natural (Fin 5) := {
    toFun v := (b (Multiplicative.ofAdd v)).toAdd
    invFun w := (b.symm (Multiplicative.ofAdd w)).toAdd
    left_inv v := congrArg Multiplicative.toAdd (b.symm_apply_apply (Multiplicative.ofAdd v))
    right_inv w := congrArg Multiplicative.toAdd (b.apply_symm_apply (Multiplicative.ofAdd w))
    map_add' v w := congrArg Multiplicative.toAdd (b.map_mul
      (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  let a : D.space ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) :=
    aA.toLinearEquiv (ZMod.map_smul aA)
  have ha (l : L) (v : D.space) : a (D.chosenAction l v) =
      Chapter6.Source.a5Module (e (QuotientGroup.mk' (pCore 2 L) l)) (a v) := by
    apply Multiplicative.ofAdd.injective
    change f (D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l v))) = _
    apply f.symm.injective
    rw [f.symm_apply_apply]
    apply Subtype.ext
    rw [D.spaceEquiv_apply]
    have hh := (hf l (D.spaceEquiv (Multiplicative.ofAdd v))).symm
    rw [D.spaceEquiv_apply] at hh
    exact hh
  let C := (fixedSpace (reducedRepresentation (L ⊔ (T : Subgroup G)))
    (L.subgroupOf (L ⊔ (T : Subgroup G)))).comap D.space.subtype
  have hC : C = ⊥ := by
    apply bot_unique
    intro v hv
    apply a.injective
    rw [map_zero]
    apply a5_fixed_zero
    intro g
    obtain ⟨l,hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (e.symm g)
    have he : e (QuotientGroup.mk' (pCore 2 L) l) = g := by
      rw [hl,MulEquiv.apply_symm_apply]
    rw [← he,← ha]
    congr 1
    exact Subtype.ext (hv ((subgroupOfEquivOfLe
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm l))
  let c : D.chosenCentralQuotient ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5) :=
    (C.quotEquivOfEqBot hC).trans a
  have hc (l : L) (v : D.chosenCentralQuotient) :
      c (D.chosenCentralAction l v) =
        Chapter6.Source.a5Module (e (QuotientGroup.mk' (pCore 2 L) l)) (c v) := by
    induction v using Submodule.Quotient.induction_on with
    | _ v => exact ha l v
  exact (D.alternatives_and_a5_model_of_central_quotient e c hc).1

/-- The module exit from 6.2.20 now feeds the literal 12.2.2 list and retains
its original four-dimensional chosen space. -/
theorem alternatives_and_dimension_of_one_or_two_a5
    (h : Chapter6.Source.IsOneOrTwoA5Modules L V) :
    ModuleAlternatives1222 D ∧ Module.finrank (ZMod 2) D.space = 4 :=
  ⟨D.alternatives_of_a5_conjugationModel (D.one_a5_of_one_or_two h),
    D.a5_space_finrank_of_one_or_two h⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
