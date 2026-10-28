module
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.CComponent.RadicalKernel
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.GeneralizedFitting.LayerImages
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The literal simple-section action in the odd-local Mathieu comparison

The containing C-component Q is used with the quotient
(Q/O₂(Q))/Z(Q/O₂(Q)). Its projection has solvable kernel, so the full
perfect residual retains its nontrivial image and actual M₂₂ radical quotient.
Perfect central descent shows that triviality of the induced action gives
the required commutator bound modulo the original intrinsic two-core.
Theorem A and C identify this exact simple section, without assuming that
strong quasithinness passes to arbitrary quotients.

The exterior application is Hall.OddNormalizer.OddLocalAction. Source:
Aschbacher--Smith 4.4.3, final odd-local comparison, printed p.623.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
namespace CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu

abbrev SimpleSection (X : Type*) [Group X] :=
  (X ⧸ pCore 2 X) ⧸ center (X ⧸ pCore 2 X)

@[expose] def projection (X : Type*) [Group X] : X →* SimpleSection X :=
  (QuotientGroup.mk' (center (X ⧸ pCore 2 X))).comp (QuotientGroup.mk' (pCore 2 X))

theorem projection_surjective (X : Type*) [Group X] :
    Function.Surjective (projection X) :=
  (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)

theorem projection_kernel_solvable (X : Type*) [Group X] [Finite X] :
    Group.IsSolvable (projection X).ker := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let : Group.IsNilpotent (pCore 2 X) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  change Group.IsSolvable ((QuotientGroup.mk' (center (X ⧸ pCore 2 X))).comp q).ker
  rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
  let : Group.IsSolvable (center (X ⧸ pCore 2 X)) := Group.isSolvable_of_comm
    (fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm)
  exact isSolvable_comap_of_solvable_ker q _

@[expose] def simpleAction {C : Type*} [Group C] (Q : Subgroup C) [Q.Normal] :
    C →* MulAut (SimpleSection Q) :=
  (quotientAut (center (Q ⧸ pCore 2 Q))).comp
    ((quotientAut (pCore 2 Q)).comp MulAut.conjNormal)

theorem simpleAction_projection {C : Type*} [Group C] (Q : Subgroup C) [Q.Normal]
    (x : C) (y : Q) :
    simpleAction Q x (projection Q y) = projection Q (MulAut.conjNormal x y) := by
  simp only [simpleAction,projection,MonoidHom.comp_apply,quotientAut_apply_mk]

theorem commutator_le_of_trivial_simpleAction {C : Type*} [Group C]
    (Q : Subgroup C) [Q.Normal] [IsQuasisimple (Q ⧸ pCore 2 Q)]
    (A : Subgroup C) (hA : ∀ a : A, simpleAction Q a = 1) :
    ⁅A,Q⁆ ≤ Q.pCoreIn 2 := by
  apply commutator_le.mpr
  intro x hx y hy
  have ha : quotientAut (pCore 2 Q) (MulAut.conjNormal x) = 1 := by
    apply MulAut.quotient_center_injective
    rw [map_one]
    exact hA ⟨x,hx⟩
  have hf := DFunLike.congr_fun ha (QuotientGroup.mk' (pCore 2 Q) ⟨y,hy⟩)
  simp only [quotientAut_apply_mk,MulAut.one_apply] at hf
  have hm := QuotientGroup.eq_iff_div_mem.mp hf
  exact ⟨(MulAut.conjNormal x (⟨y,hy⟩ : Q)) / ⟨y,hy⟩,hm,by
    simp [div_eq_mul_inv,commutatorElement_def]⟩

/-- The original full residual has a nontrivial image, with unchanged radical
quotient, in the literal double quotient of the containing component. -/
theorem seed_image {P Q : Type*} [Group P] [Finite P] [Group Q] [Finite Q]
    [Group.IsPerfect P] [Nontrivial P]
    (j : P →* Q) (hj : Function.Injective j)
    (e : (P ⧸ solvableRadical P) ≃* Sporadic.Mathieu.M22) :
    let f := (projection Q).comp j
    f.range ≠ ⊥ ∧ Group.IsSolvable f.ker ∧
      Nonempty ((f.range ⧸ solvableRadical f.range) ≃* Sporadic.Mathieu.M22) := by
  let f := (projection Q).comp j
  let : Group.IsSolvable (projection Q).ker := projection_kernel_solvable Q
  let g : f.ker →* (projection Q).ker :=
    (j.comp f.ker.subtype).codRestrict _ (fun x => x.property)
  have hg : Function.Injective g := by
    intro x y h
    exact Subtype.ext (hj (congrArg Subtype.val h))
  have hk : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hg
  let := hk
  have hn : f.range ≠ ⊥ := by
    intro hb
    have hf : f = 1 := MonoidHom.range_eq_bot_iff.mp hb
    have ht : f.ker = ⊤ := MonoidHom.ker_eq_top_iff.mpr hf
    let : Group.IsSolvable (⊤ : Subgroup P) := ht ▸ hk
    let : Group.IsSolvable P := Group.isSolvable_of_surjective
      (f := (topEquiv : (⊤ : Subgroup P) ≃* P).toMonoidHom) topEquiv.surjective
    exact Group.IsPerfect.not_isSolvable P inferInstance
  let : Group.IsSolvable f.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hk
  exact ⟨hn,hk,⟨(solvableRadicalQuotientEquiv f.rangeRestrict
    f.rangeRestrict_surjective).symm.trans e⟩⟩

theorem simpleSection_model {Q : Type*} [Group Q] [Finite Q]
    [IsQuasisimple (Q ⧸ pCore 2 Q)]
    (hQ : IsSQTK KnownSimple.IsKnownSimple Q) :
    ChapterA.Section02.IsTheoremCModel (SimpleSection Q) := by
  let E := Q ⧸ pCore 2 Q
  let S := SimpleSection Q
  let : IsSimpleGroup S := IsQuasisimple.simple
  let : Group.IsPerfect S := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center E)) (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple S := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center E)) (QuotientGroup.mk'_surjective _)
  have hsemi : ChapterA.Section02.IsSemisimple S := by
    apply top_unique
    apply le_sSup
    exact ⟨(inferInstance : (⊤ : Subgroup S).Normal).isSubnormal,
      IsQuasisimple.of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup S) ≃* S).symm⟩
  have hsec := ChapterA.Section02.IsSectionOf.of_surjective (projection Q) (projection_surjective Q)
  exact ChapterA.Section02.theoremC_knownSimple inferInstance
    (Group.IsPerfect.not_isMulCommutative S)
    (ChapterA.Section02.theoremA_knownSimple.stronglyQuasithin_section
      hQ.stronglyQuasithin hQ.isKGroup hsec hsemi)
    ((hQ.isKGroup.quotient (pCore 2 Q)).quotient (center E))

end CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu
namespace CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu
@[expose] def seedInclusion {G : Type*} [Group G] {D C : Subgroup G}
    (hDC : D ≤ C) {P : Subgroup D} {Q : Subgroup C}
    (hPQ : P.map (inclusion hDC) ≤ Q) : P →* Q where
  toFun x := ⟨inclusion hDC x,hPQ (mem_map_of_mem _ x.property)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem seedInclusion_injective {G : Type*} [Group G] {D C : Subgroup G}
    (hDC : D ≤ C) {P : Subgroup D} {Q : Subgroup C}
    (hPQ : P.map (inclusion hDC) ≤ Q) : Function.Injective (seedInclusion hDC hPQ) := by
  intro x y he
  exact Subtype.ext (Subtype.ext (congrArg (fun z : Q => ((z : C) : G)) he))
end CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu

