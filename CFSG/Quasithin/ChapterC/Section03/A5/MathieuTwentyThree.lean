module
public import CFSG.Quasithin.ChapterC.Section03.A5.QuintetObstruction
public import CFSG.Quasithin.ChapterC.Section03.A5.HeptadObstruction
public import Theory.Mathieu.M23.QuasithinGeometry.ChapterHLocalActions.CoreNormalizers
public import Theory.Mathieu.M23.QuasithinGeometry.CommonFour.Fusion
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport

/-!
# The native M23 ordinary-component obstruction for the original A5 block

The exhaustive elementary-Sylow calculation places the actual U of order
16 in a conjugate of the quintet or heptad core. Their full normalizers
are the corresponding literal locals. The original normalizer control
therefore makes the same block normal in that local. The actual semilinear
module excludes the quintet case, and the simple A7 quotient excludes the
heptad case. No local classification or module-identification premise is
left in the native theorem.
Source: Aschbacher–Smith C.3.1(4), printed pp.149–151, and 4.3.6, pp.614–615.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC
variable {G : Type*} [Group G] [Finite G]

/-- Transport full core-normalizer control into a local obstruction, retaining the original block. -/
theorem no_normalized_alternatingFive_of_conjugate_core
    (A P : Subgroup G) (hA : IsAlternatingBlock A 5)
    (hctrl : normalizer ((blockU A).map A.subtype : Set G) ≤ normalizer (A : Set G))
    (e : G ≃* G)
    (hU : (blockU A).map A.subtype = ((pCore 2 P).map P.subtype).map e.toMonoidHom)
    (hP : normalizer ((pCore 2 P).map P.subtype : Set G) = P)
    (hexclude : ∀ B : Subgroup P, B.Normal → ¬ IsAlternatingBlock B 5) : False := by
  let P' := P.map e.toMonoidHom
  have hn : normalizer ((blockU A).map A.subtype : Set G) = P' := by
    rw [hU, ← map_equiv_normalizer_eq,hP]
  have hAP : A ≤ P' := by
    rw [←hn]
    exact A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (blockU A))
  have hPA : P' ≤ normalizer (A : Set G) := by rwa [←hn]
  let C := A.subgroupOf P'
  let : C.Normal := normal_subgroupOf_of_le_normalizer hPA
  let eP : P ≃* P' := e.subgroupMap P
  let B := C.map eP.symm.toMonoidHom
  have hB : B.Normal := Subgroup.Normal.map inferInstance eP.symm.toMonoidHom eP.symm.surjective
  let aC : A ≃* C := (subgroupOfEquivOfLe hAP).symm
  let aB : A ≃* B := aC.trans (eP.symm.subgroupMap C)
  exact hexclude B hB (RankOne.Solvable.isAlternatingBlock_of_equiv aB hA)

theorem native_m23_no_normalized_alternatingFive
    (A : Subgroup Sporadic.Mathieu.M23) (hA : IsAlternatingBlock A 5)
    (hc : Nat.card ((blockU A).map A.subtype) = 16)
    (hctrl : normalizer ((blockU A).map A.subtype : Set Sporadic.Mathieu.M23) ≤
      normalizer (A : Set Sporadic.Mathieu.M23)) : False := by
  let U := (blockU A).map A.subtype
  let := hA.2.1.elementary
  have hU : IsElementaryAbelian 2 U := IsElementaryAbelian.map A.subtype
  obtain ⟨g,hg⟩ := Sporadic.Mathieu.M23Geometry.CommonFour.card16_conjugate_core U hU hc
  rcases hg with hg | hg
  · apply no_normalized_alternatingFive_of_conjugate_core A _ hA hctrl (MulAut.conj g) hg
      Sporadic.Mathieu.M23Geometry.quintet_core_normalizer
    intro B hB
    let := hB
    exact native_quintet_no_normal_alternatingFive B
  · apply no_normalized_alternatingFive_of_conjugate_core A _ hA hctrl (MulAut.conj g) hg
      Sporadic.Mathieu.M23Geometry.source_heptad_core_normalizer
    intro B hB
    let := hB
    exact native_heptad_no_normal_alternatingFive B
end CFSG.Quasithin.ChapterC
