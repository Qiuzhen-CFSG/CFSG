module
public import Theory.GroupAction.RankTwoCosetGeometry
import Mathlib.Tactic.Group

/-!
# Fusion along a connected fixed coset graph

Compatible endpoint maps assign conjugacy-class labels to fixed vertices.
Common representatives identify the labels across every edge, and a fixed
path transfers conjugacy between endpoints without requiring a homomorphism
from the whole carrier. This general argument is extracted, unchanged in
mathematics, from the general Ree F.4.30 application and is used also for
unitary-five extensions. Source: Aschbacher–Smith F.4.30, printed p.290.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry SimpleGraph
namespace Subgroup.CosetGeometry.Fusion
variable {N G : Type*} [Group N] [Group G]
variable (F : Bool → Subgroup N) (f : ∀ i, F i →* G)

private theorem conjugate_mem {x : N} {v : CosetGeometry.Vertex F}
    (hv : x • v = v) (g : N) (hg : g • CosetGeometry.base F v.type = v) :
    g⁻¹*x*g ∈ F v.type := by
  rw [←CosetGeometry.stabilizer_base F v.type]
  change (g⁻¹*x*g) • CosetGeometry.base F v.type = _
  rw [mul_smul,mul_smul,hg,hv,←hg,inv_smul_smul]
  rfl

private theorem representatives {x : N} {v : CosetGeometry.Vertex F}
    (hv : x • v = v) (g h : N)
    (hg : g • CosetGeometry.base F v.type = v)
    (hh : h • CosetGeometry.base F v.type = v) :
    IsConj (f v.type ⟨g⁻¹*x*g,conjugate_mem F hv g hg⟩)
      (f v.type ⟨h⁻¹*x*h,conjugate_mem F hv h hh⟩) := by
  have ha : h⁻¹*g ∈ F v.type := by
    rw [←CosetGeometry.stabilizer_base F v.type]
    change (h⁻¹*g) • CosetGeometry.base F v.type = _
    rw [mul_smul,hg,←hh,inv_smul_smul]
    rfl
  apply isConj_iff.mpr
  refine ⟨f v.type ⟨h⁻¹*g,ha⟩,?_⟩
  rw [←map_inv,←map_mul,←map_mul]
  apply congrArg (f v.type)
  apply Subtype.ext
  change (h⁻¹*g)*(g⁻¹*x*g)*(h⁻¹*g)⁻¹ = h⁻¹*x*h
  group

private def representative (v : CosetGeometry.Vertex F) : N :=
  Classical.choose (CosetGeometry.exists_smul_base F v)

private theorem representative_spec (v : CosetGeometry.Vertex F) :
    representative F v • CosetGeometry.base F v.type = v :=
  Classical.choose_spec (CosetGeometry.exists_smul_base F v)

private def label (x : N) (v : {v : CosetGeometry.Vertex F // x • v = v}) : G :=
  f v.val.type ⟨(representative F v.val)⁻¹*x*representative F v.val,
    conjugate_mem F v.property _ (representative_spec F v.val)⟩

private theorem label_conj (x : N) (v : {v : CosetGeometry.Vertex F // x • v = v})
    (g : N) (hg : g • CosetGeometry.base F v.val.type = v.val) :
    IsConj (label F f x v) (f v.val.type ⟨g⁻¹*x*g,conjugate_mem F v.property g hg⟩) :=
  representatives F f v.property _ _ (representative_spec F v.val) hg

private theorem label_adjacent (x : N)
    (hc : ∀ (y : N) (h₀ : y ∈ F false) (h₁ : y ∈ F true),
      f false ⟨y,h₀⟩ = f true ⟨y,h₁⟩)
    {v w : {v : CosetGeometry.Vertex F // x • v = v}}
    (ha : ((CosetGeometry.RankTwo.graph F).induce {v | x • v = v}).Adj v w) :
    IsConj (label F f x v) (label F f x w) := by
  obtain ⟨g,hg,hh⟩ := CosetGeometry.RankTwo.incident_common_translate F ha.2
  have he : f v.val.type ⟨g⁻¹*x*g,conjugate_mem F v.property g hg⟩ =
      f w.val.type ⟨g⁻¹*x*g,conjugate_mem F w.property g hh⟩ := by
    have compat (i j : Bool) (z : N) (hi : z ∈ F i) (hj : z ∈ F j) :
        f i ⟨z,hi⟩ = f j ⟨z,hj⟩ := by
      cases i <;> cases j
      · rfl
      · exact hc _ _ _
      · exact (hc _ _ _).symm
      · rfl
    exact compat _ _ _ _ _
  exact (label_conj F f x v g hg).trans (he ▸ (label_conj F f x w g hh).symm)

private theorem label_connected (x : N)
    (hc : ∀ (y : N) (h₀ : y ∈ F false) (h₁ : y ∈ F true),
      f false ⟨y,h₀⟩ = f true ⟨y,h₁⟩)
    (hconn : ((CosetGeometry.RankTwo.graph F).induce {v | x • v = v}).Preconnected)
    (v w : {v : CosetGeometry.Vertex F // x • v = v}) :
    IsConj (label F f x v) (label F f x w) := by
  obtain ⟨p⟩ := hconn v w
  induction p with
  | nil => exact IsConj.refl _
  | cons ha p ih => exact (label_adjacent F f x hc ha).trans ih

/-- A connected fixed graph transfers endpoint fusion through compatible maps. -/
theorem of_fixed_connected
    (hc : ∀ (y : N) (h₀ : y ∈ F false) (h₁ : y ∈ F true),
      f false ⟨y,h₀⟩ = f true ⟨y,h₁⟩)
    {i j : Bool} (x : F i) (y : F j)
    (hconn : ((CosetGeometry.RankTwo.graph F).induce {v | x.val • v = v}).Preconnected)
    (hxy : IsConj x.val y.val) : IsConj (f i x) (f j y) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hxy
  have hx : x.val • CosetGeometry.base F i = CosetGeometry.base F i := by
    change x.val ∈ MulAction.stabilizer N (CosetGeometry.base F i)
    rw [CosetGeometry.stabilizer_base]
    exact x.property
  have hy : y.val • CosetGeometry.base F j = CosetGeometry.base F j := by
    change y.val ∈ MulAction.stabilizer N (CosetGeometry.base F j)
    rw [CosetGeometry.stabilizer_base]
    exact y.property
  have hy' : x.val • (g⁻¹ • CosetGeometry.base F j) = g⁻¹ • CosetGeometry.base F j := by
    apply (MulAction.toPerm g).injective
    change g • (x.val • (g⁻¹ • CosetGeometry.base F j)) = g • (g⁻¹ • CosetGeometry.base F j)
    rw [smul_inv_smul,←mul_smul,←mul_smul]
    have he : g*x.val*g⁻¹ = y.val := hg
    rw [he]
    exact hy
  let v : {v : CosetGeometry.Vertex F // x.val • v = v} := ⟨CosetGeometry.base F i,hx⟩
  let w : {v : CosetGeometry.Vertex F // x.val • v = v} := ⟨g⁻¹ • CosetGeometry.base F j,hy'⟩
  have h₀ := label_conj F f x.val v 1 (one_smul _ _)
  have h₁ := label_conj F f x.val w g⁻¹ rfl
  have h₀' : IsConj (label F f x.val v) (f i x) := by
    convert h₀ using 1
    exact congrArg (f i) (Subtype.ext (by simp))
  have h₁' : IsConj (label F f x.val w) (f j y) := by
    convert h₁ using 1
    exact congrArg (f j) (Subtype.ext (by simpa only [inv_inv] using hg.symm))
  exact h₀'.symm.trans ((label_connected F f x.val hc hconn v w).trans h₁')

end Subgroup.CosetGeometry.Fusion
