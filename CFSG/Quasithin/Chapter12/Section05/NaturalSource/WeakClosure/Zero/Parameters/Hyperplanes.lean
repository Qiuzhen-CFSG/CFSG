module
public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.WeakClosure.Zero.Parameters.FixedSpaces
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Hyperplane centralizers in the exterior branch

Every linear functional on the original exterior square vanishes on a
conjugate of the marked V₃. The two bivector normal forms apply to its
coefficient vector, with transpose carrying the action to linear
functionals. A fixed permutation exhibits the same isotropic three-space
in both forms. Applying this to the literal one-dimensional quotient V/U
puts a conjugate of V₃ inside each hyperplane U.

The original G₃≤M containment then controls C_G(U), with the conjugating
element lifted through the unchanged L/O₂(L) marking. This supplies a
source-specialized way to exclude corank one in 12.5.6.
The G₃ premise is the earlier input owned by qt-d-1251-local.

Source: Aschbacher--Smith, 12.5.4--6, printed pp.819--820.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Representation
open scoped Matrix
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
open Representation.SL5ExteriorSquare Representation.SL5TenDimensional

private def transposeActor (g : Representation.SL5TenDimensional.Group) :
    Representation.SL5TenDimensional.Group :=
  ⟨g.val.transpose, by rw [Matrix.det_transpose, g.property]⟩

private theorem actionMatrix_transposeActor (g : Representation.SL5TenDimensional.Group) :
    actionMatrix (transposeActor g) = (actionMatrix g).transpose := by
  ext i j
  simp only [actionMatrix, transposeActor, Matrix.transpose_apply]
  ring

private theorem functional_coordinates (f : V →ₗ[ZMod 2] ZMod 2) (v : V) :
    f v = dotProduct (fun i => f (basis i)) (coordinates v) := by
  conv_lhs => rw [← basis.sum_equivFun v]
  simp only [map_sum, map_smul, smul_eq_mul, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

set_option maxRecDepth 4000 in
private def isotropicActor : Representation.SL5TenDimensional.Group :=
  ⟨!![1,0,0,0,0;0,0,0,1,0;0,1,0,0,0;0,0,0,0,1;0,0,1,0,0], by decide⟩

private theorem isotropicActor_coordinates (v : V) (hv : v ∈ V₃) :
    coordinates (exteriorAction 2 isotropicActor v) 0 = 0 ∧
      coordinates (exteriorAction 2 isotropicActor v) 7 = 0 := by
  have hh := (mem_coordinateSpan {0,1,4} v).mp hv
  rw [coordinates_action]
  constructor
  · simpa [actionMatrix, isotropicActor, pair, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] using hh 2 (by decide)
  · simpa [actionMatrix, isotropicActor, pair, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] using hh 6 (by decide)

private theorem functional_conjugate_Vthree (f : V →ₗ[ZMod 2] ZMod 2) :
    ∃ g : Representation.SL5TenDimensional.Group,
      ∀ v ∈ V₃, f (exteriorAction 2 g v) = 0 := by
  let c : Coordinates := fun i => f (basis i)
  by_cases hc : c = 0
  · refine ⟨1, fun v _ => ?_⟩
    rw [functional_coordinates]
    change dotProduct c _ = 0
    rw [hc, zero_dotProduct]
  have hv : coordinates.symm c ≠ 0 := by
    intro hh
    apply hc
    rw [← coordinates.apply_symm_apply c, hh, map_zero]
  obtain ⟨g, hg | hg⟩ := bivector_normal_form (coordinates.symm c) hv
  all_goals
    refine ⟨transposeActor g * isotropicActor, fun v hv => ?_⟩
    have he := congrArg coordinates hg
    rw [coordinates_action, coordinates.apply_symm_apply] at he
    rw [functional_coordinates, map_mul, Module.End.mul_apply,
      coordinates_action, actionMatrix_transposeActor]
    change dotProduct c ((actionMatrix g).transpose.mulVec
      (coordinates (exteriorAction 2 isotropicActor v))) = 0
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, he]
  · rw [coordinates_decomposable]
    simpa [dotProduct, Fin.sum_univ_succ] using (isotropicActor_coordinates v hv).1
  · rw [coordinates_nondecomposable]
    simpa [dotProduct, Fin.sum_univ_succ] using
      congrArg₂ (· + ·) (isotropicActor_coordinates v hv).1
        (isotropicActor_coordinates v hv).2

open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

namespace ExteriorMarking
variable (a : ExteriorMarking D)

/-- Every hyperplane contains an actual L-conjugate of the marked V₃. -/
theorem hyperplane_contains_conjugate_Vthree
    {U : Subgroup G} (_hUV : U ≤ V) (hc : subgroupCorank V U = 1) :
    ∃ l : L, (a.Vi 3).map (MulAut.conj (l : G)).toMonoidHom ≤ U := by
  let := D.elementary
  have hd : Module.finrank (ZMod 2) (Additive (V ⧸ U.subgroupOf V)) = 1 := by
    rwa [← subgroupCorank_eq_quotient_finrank]
  let q := (QuotientGroup.mk' (U.subgroupOf V)).toAdditive.toZModLinearMap 2
  let e : Additive (V ⧸ U.subgroupOf V) ≃ₗ[ZMod 2] ZMod 2 :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
  let f : Representation.SL5ExteriorSquare.V →ₗ[ZMod 2] ZMod 2 :=
    e.toLinearMap.comp (q.comp a.linearCoordinates.symm.toLinearMap)
  obtain ⟨g, hg⟩ := functional_conjugate_Vthree f
  obtain ⟨z, hz⟩ := a.quotientEquiv.surjective g
  obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) z
  refine ⟨l, ?_⟩
  rintro x ⟨v, hv, rfl⟩
  let v₀ : V := ⟨v, a.subspace_le _ hv⟩
  have hn := (mem_normalizer_iff.mp (D.normalizes l.property) v).mp v₀.property
  let w : V := ⟨(l : G) * v * (l : G)⁻¹, hn⟩
  have he := congrArg Multiplicative.toAdd (a.equivariant l v₀)
  rw [hl, hz] at he
  change (a.coordinates w).toAdd = exteriorAction 2 g (a.coordinates v₀).toAdd at he
  have hf := hg (a.coordinates v₀).toAdd ((a.mem_subspace V₃ v₀).mp hv)
  rw [← he] at hf
  change e (q (a.linearCoordinates.symm (a.linearCoordinates (Additive.ofMul w)))) = 0 at hf
  rw [LinearEquiv.symm_apply_apply] at hf
  have hq : q (Additive.ofMul w) = 0 := e.injective (hf.trans (map_zero e).symm)
  exact (QuotientGroup.eq_one_iff w).mp hq

/-- G₃≤M excludes every escaping hyperplane centralizer. -/
theorem centralizer_hyperplane_le
    (hG₃ : a.Gi 3 ≤ a.M) {U : Subgroup G}
    (hUV : U ≤ V) (hc : subgroupCorank V U = 1) :
    centralizer (U : Set G) ≤ a.M := by
  obtain ⟨l, hl⟩ := a.hyperplane_contains_conjugate_Vthree hUV hc
  have hm : a.M.map (MulAut.conj (l : G)).toMonoidHom = a.M :=
    mem_normalizer_iff_map_conj_eq.mp
      (a.M.le_normalizer (L.le_normalizer l.property))
  have hn : normalizer ((a.Vi 3).map (MulAut.conj (l : G)).toMonoidHom : Set G) ≤
      a.M := by
    rw [← map_equiv_normalizer_eq]
    exact (map_mono hG₃).trans_eq hm
  exact (Subgroup.centralizer_le hl).trans
    ((Subgroup.centralizer_le_normalizer _).trans hn)

end ExteriorMarking

end CFSG.Quasithin.Chapter12.Section05.NaturalSource
