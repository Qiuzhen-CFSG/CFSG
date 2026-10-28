module
public import CFSG.Quasithin.ChapterG.Section12.RecognitionQuadratic

/-!
# The literal orthogonal point radical in the quadratic branch

A quadratic isometry fixing the perpendicular hyperplane of a singular
center is the identity. Nondegeneracy confines every remaining displacement
to that center line, and preservation of quadratic values eliminates it.
The faithful radical order calculation then identifies the original point
radical with the full orthogonal one, without replacing either action.

This is the radical equality used in Aschbacher--Smith G.12.10, printed
p.373. The terminal constituent applies it to every nonzero singular point.
Generation of the orthogonal residual remains a separate obligation.
-/

public noncomputable section
open Subgroup Module
namespace CFSG.Quasithin.ChapterG.Section12
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {D : Subgroup (V ≃ₗ[ZMod 2] V)} {B : LinearMap.BilinForm (ZMod 2) V}
  {hB : B.IsAlt} {v : V}

omit [FiniteDimensional (ZMod 2) V] in
private theorem quadratic_preserves (q : QuadraticForm (ZMod 2) V)
    (hq : q.polarBilin = B) : q.isometrySubgroup ≤ formStabilizer B := by
  intro a ha x y
  have hh := (QuadraticMap.mem_isometrySubgroup q a).mp ha
  rw [← hq]
  change q (a x+a y)-q (a x)-q (a y)=q (x+y)-q x-q y
  rw [← map_add,hh,hh,hh]

include hB in
/-- A singular center makes the orthogonal radical faithful on its perpendicular
hyperplane. The possible extra symplectic transvection changes quadratic values. -/
theorem pointRadical_faithful_of_quadratic_singular
    (hnd : B.Nondegenerate) (q : QuadraticForm (ZMod 2) V)
    (hq : q.polarBilin = B) (hv : q v=0)
    (a : V ≃ₗ[ZMod 2] V) (ha : a∈pointRadical q.isometrySubgroup B v)
    (hf : ∀ w : V,B v w=0 → a w=w) : a=1 := by
  have hp := quadratic_preserves q hq ha.1
  have hs (x y : V) : B x y=B y x := by
    rw [← hB.neg_eq x y]
    exact (show ∀ c : ZMod 2,-c=c from by decide) (B x y) |>.symm
  apply LinearEquiv.ext
  intro y
  change a y=y
  by_cases hy : B v y=0
  · exact hf y hy
  have hy1 : B v y=1 :=
    ((show ∀ c : ZMod 2,c=0 ∨ c=1 from by decide) _).resolve_left hy
  have hd : a y-y∈Submodule.span (ZMod 2) {v} := by
    rw [← B.orthogonal_orthogonal hnd hB.isRefl (Submodule.span (ZMod 2) {v}),
      LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]
    intro w hw
    rw [hs w (a y-y),map_sub,LinearMap.sub_apply]
    have hh := hp y w
    rw [hf w hw] at hh
    exact sub_eq_zero.mpr hh
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hd
  have hay : a y=y+c • v := by rw [hc]; abel
  have he := (QuadraticMap.mem_isometrySubgroup q a).mp ha.1 y
  rw [hay,QuadraticMap.map_add q,QuadraticMap.map_smul,hv,smul_zero,add_zero] at he
  change q y + q.polarBilin y (c • v)=q y at he
  rw [hq,map_smul,smul_eq_mul,hs y v,hy1,mul_one] at he
  have hc0 : c=0 := add_eq_left.mp he
  rw [hay,hc0,zero_smul,add_zero]

/-- In the quadratic branch the original source radical is the full orthogonal
point radical on the same space, not merely an abstract isomorphic group. -/
theorem GoodVector.pointRadical_eq_orthogonal
    (h : GoodVector D B hB v) (hnd : B.Nondegenerate)
    (q : QuadraticForm (ZMod 2) V) (hq : q.polarBilin=B)
    (hD : D≤q.isometrySubgroup) (hv : q v=0)
    (hd : 2≤finrank (ZMod 2) V) :
    pointRadical D B v=pointRadical q.isometrySubgroup B v := by
  have hp := quadratic_preserves q hq
  have ho := h.mono hD hp
  have hf := pointRadical_faithful_of_quadratic_singular (hB := hB) hnd q hq hv
  have hle : pointRadical D B v≤pointRadical q.isometrySubgroup B v :=
    inf_le_inf hD le_rfl
  have hn : B v≠0 := fun hz => h.nonzero (hnd.1 v (fun w => LinearMap.congr_fun hz w))
  obtain ⟨x,hx⟩ := Module.Dual.range_eq_top_of_ne_zero hn ▸
    (show (1 : ZMod 2)∈(⊤ : Submodule (ZMod 2) (ZMod 2)) from trivial)
  have hc1 := h.card_pointRadical_of_faithful hnd (hD.trans hp)
    (fun a ha => hf a (hle ha)) hd hx
  have hc2 := ho.card_pointRadical_of_faithful hnd hp hf hd hx
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun a : V ≃ₗ[ZMod 2] V => (a : V → V)) DFunLike.coe_injective
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hc1,hc2]

end CFSG.Quasithin.ChapterG.Section12
