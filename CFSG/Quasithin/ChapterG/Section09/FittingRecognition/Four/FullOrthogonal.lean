module
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.OrthogonalOrder
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.IndexTwoCubic
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.ThreeCore.Source

/-!
# The full orthogonal action from the original degree-four case

The degree-four Fitting alternative realizes the original representation on
an index-at-most-two subgroup of the prescribed orthogonal carrier. Its
marked elementary four-group is mapped through that realization. The finite
orthogonal alternative then either gives the full carrier or a normal cubic
in the original acting group. The latter contradicts the source normal-cubic
exclusion. The original group equivalence, linear coordinates and action
identity are retained, rather than replaced by an abstract group model.

Source: Aschbacher--Smith 14.3.15, using G.9.4(4).
-/

open Subgroup
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition
variable {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [Finite G] in
/-- The original four-group and no-normal-cubic premise force the full
prescribed degree-four orthogonal action. -/
public theorem CaseFour.full_orthogonal_of_no_normal_cubic
    {ρ : Representation (ZMod 2) G V} {m : ℕ} (h : CaseFour ρ m)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hA : Nat.card A=4)
    (hno : ∀ C : Subgroup G, C.Normal → Nat.card C=3 → False) :
    OrthogonalRealization ρ ⊤ := by
  obtain ⟨_,_,H,hi,e,f,hact⟩ := h
  let E := Four.splitOrthogonalEquiv
  let j : G→*BinaryFourPlus.q.isometrySubgroup := E.toMonoidHom.comp (H.subtype.comp e.toMonoidHom)
  let B := A.map j
  let K := H.map E.toMonoidHom
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map (A:=A) j
  have hj : Function.Injective j := E.injective.comp (H.subtype_injective.comp e.injective)
  have hB : Nat.card B=4 := (card_map_of_injective hj).trans hA
  have hBK : B≤K := by
    rintro x ⟨a,_,rfl⟩
    exact ⟨e a,(e a).property,rfl⟩
  have hKi : K.index≤2 := by rw [index_map_of_bijective E.bijective H]; exact hi
  rcases BinaryFourPlus.eq_top_or_normal_cubic_of_index_le_two K B hKi hBK hB with htop | ⟨C,hCn,hCc⟩
  · have hH : H=⊤ := by
      apply Subgroup.map_injective (f:=E.toMonoidHom) E.injective
      exact htop.trans (Subgroup.map_top_of_surjective E.toMonoidHom E.surjective).symm
    subst H
    exact ⟨e,f,hact⟩
  · let k : G≃*K := e.trans (E.subgroupMap H)
    let D := C.map k.symm.toMonoidHom
    have hDn : D.Normal := hCn.map _ k.symm.surjective
    have hDc : Nat.card D=3 := (card_map_of_injective k.symm.injective).trans hCc
    exact (hno D hDn hDc).elim
/-- The original cubic, rank-two, degree-four source branch has the full
orthogonal action once its source normal-cubic exclusion is supplied. -/
public theorem source_cubic_rank_two_degree_four_full
    {K : GroupClass} {ρ : Representation (ZMod 2) G V} {A : Subgroup G}
    (h : FittingHypothesis K ρ A 2)
    (hc : IsPGroup 3 (⁅fittingSubgroup G,A⁆ : Subgroup G))
    (hd : Module.finrank (ZMod 2) V=4)
    (hno : ∀ C : Subgroup G, C.Normal → Nat.card C=3 → False) :
    OrthogonalRealization ρ ⊤ := by
  let : IsElementaryAbelian 2 A := h.elementary
  apply (source_cubic_rank_two_degree_four h hc hd).full_orthogonal_of_no_normal_cubic A
  · simpa using h.card_actor
  · exact hno
end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
