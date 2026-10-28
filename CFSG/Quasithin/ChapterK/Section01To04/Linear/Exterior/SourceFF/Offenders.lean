module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Exterior.SourceFF.SixImage
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.HyperplanePlacement
public import Theory.Representation.BinaryOffender.Stability
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.RatioFromStrong
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Irreducible
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Exterior
public import Theory.Representation.BinaryOffender.EquivariantStabilizer
public import Theory.GroupTheory.SylowKernelCore

/-!
# All offenders on the binary SL₅ exterior square

Move an elementary actor into the standard hyperplane parabolic. A minimal
best offender centralizes its six-dimensional exterior subspace by the
B.7.1 restriction theorem and the actual A₈ image calculation. Its pointwise
kernel is the shear radical. That radical is self-centralizing in the
parabolic, so every best offender is a conjugate of it. These same actors
have rank and displacement four, exclude strong offenders, generate SL₅(2),
and give the sharp global quadratic ratio one.

The geometric conclusion retains the literal two-core of a conjugate
hyperplane stabilizer, as required by B.4.2(11).
Source: Aschbacher–Smith K.3.2.3, printed p.455, and B.4.2(11), p.86.
-/

public section
noncomputable section
open Representation Representation.SL5TenDimensional Representation.SL5ExteriorSquare
open Representation.BinaryOffender Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterK.Linear.Exterior.SourceFF
open ChapterB.QuasisimpleSource BinaryLinear.OuterCyclic

theorem best_le_parabolic_eq_shear {A : Subgroup Group}
    (hA : IsBestOffender (exteriorAction 2) A) (hAP : A ≤ parabolic 4) :
    A = shearSubgroup := by
  obtain ⟨B, hB, hBA⟩ := hA.exists_minimal (exteriorAction 2)
  have hBP := hBA.1.trans hAP
  have hstable : ∀ a ∈ B, ∀ w ∈ V₆, exteriorAction 2 a w ∈ V₆ := by
    intro a ha w hw
    have hp : a ∈ exteriorStabilizer V₆ := by
      rw [exteriorStabilizer_V₆_eq_parabolic]
      exact hBP ha
    exact (hp w).mpr hw
  have hfixed := minimal_best_stable_fixed hB hstable
  have hBX : B ≤ shearSubgroup := by
    rw [← pointwiseV₆_eq_shearSubgroup]
    intro b hb
    exact ⟨hBP hb, fun v hv => hfixed hv ⟨b, hb⟩⟩
  have hBeq := (offender_below_shear_iff hBX).mp (hB.1.isOffender _)
  rw [hBeq] at hBA
  apply le_antisymm ?_ hBA.1
  let : IsElementaryAbelian 2 A := hA.1.2
  intro a ha
  apply parabolic_centralizer_shear_le (hAP ha)
  apply mem_centralizer_iff.mpr
  intro x hx
  exact congrArg Subtype.val (mul_comm (⟨x, hBA.1 hx⟩ : A) ⟨a, ha⟩)

theorem best_conjugate_shear {A : Subgroup Group}
    (hA : IsBestOffender (exteriorAction 2) A) :
    ∃ g : Group, A.map (MulAut.conj g).toMonoidHom = shearSubgroup := by
  let : IsElementaryAbelian 2 A := hA.1.2
  obtain ⟨g, hg⟩ := pGroup_conjugate_le_parabolic_four A (IsElementaryAbelian.isPGroup 2 A)
  exact ⟨g, best_le_parabolic_eq_shear (hA.map_conj (exteriorAction 2) g) hg⟩

theorem best_rank_codim {A : Subgroup Group}
    (hA : IsBestOffender (exteriorAction 2) A) :
    rank A = 4 ∧ fixedCodim (exteriorAction 2) A = 4 := by
  obtain ⟨g, hg⟩ := best_conjugate_shear hA
  constructor
  · rw [← rank_map_conj A g, hg]
    exact shear_rank
  · rw [← fixedCodim_map_conj (exteriorAction 2) A g, hg]
    exact shear_fixedCodim

theorem exterior_not_strong : ¬ IsStrongFFModule (exteriorAction 2) := by
  rintro ⟨A, hA⟩
  obtain ⟨B, _, hB, _, hstrong⟩ := hA.exists_quadratic_minimalBestOffender (exteriorAction 2)
  obtain ⟨hr, hc⟩ := best_rank_codim hB.1
  have hi := hstrong.2
  rw [hr, hc] at hi
  exact Nat.lt_irrefl _ hi

theorem exterior_quadraticRatio : quadraticRatio (exteriorAction 2) = 1 := by
  apply quadraticRatio_eq_one_of_no_strong (exteriorAction 2)
    ⟨shearSubgroup, shear_bestOffender.isOffender _⟩
  intro A hA
  exact exterior_not_strong ⟨A, hA⟩

theorem exterior_offenderSubgroup : offenderSubgroup (exteriorAction 2) = ⊤ := by
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 5) (ZMod 2)) :=
    Atlas.psl_simple_high_rank 5 (by decide)
  let : IsSimpleGroup Group := projectiveEquiv.isSimpleGroup
  exact (offenderSubgroup_normal (exteriorAction 2)).eq_bot_or_eq_top.resolve_left
    (by
      intro h
      exact shear_elementary.1 (le_bot_iff.mp (h ▸ shear_bestOffender.le_offenderSubgroup _)))

/-- The marked shear subgroup is the actual hyperplane radical. -/
theorem shear_endNode : IsEndNodeRadical shearSubgroup := by
  refine ⟨naturalFlag 4, Or.inr (finrank_naturalFlag 4 (by decide)), ?_⟩
  change shearSubgroup = (pCore 2 (parabolic 4)).map (parabolic 4).subtype
  rw [← parabolicResidualTwoCore_four, parabolicResidualTwoCore, parabolicResidualFlag_four]

/-- Conjugation preserves the geometric end-node radical property. -/
theorem endNode_map_conj {A : Subgroup Group} (hA : IsEndNodeRadical A) (g : Group) :
    IsEndNodeRadical (A.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨P, hP, hA⟩ := hA
  let ρ := linearNatural BinaryField.two 5
  let E := slEquivLinear 5 g
  have hi (a : Group) (v : Fin 5 → ZMod 2) :
      E (ρ a v) = ρ (MulAut.conj g a) (E v) := by
    change (slEquivLinear 5 g) ((slEquivLinear 5 a) v) =
      (slEquivLinear 5 (g * a * g⁻¹)) ((slEquivLinear 5 g) v)
    simp only [map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply]
  refine ⟨P.map E.toLinearMap, ?_, ?_⟩
  · rw [← (P.equivMapOfInjective E.toLinearMap E.injective).finrank_eq]
    exact hP
  · change A.map (MulAut.conj g).toMonoidHom =
      (BinaryOffender.subspaceStabilizer ρ (P.map E.toLinearMap)).pCoreIn 2
    rw [hA]
    change ((BinaryOffender.subspaceStabilizer ρ P).pCoreIn 2).map
      (MulAut.conj g).toMonoidHom = _
    have hs := map_subspaceStabilizer_equivariant ρ ρ (MulAut.conj g) E hi P
    exact (map_pCoreIn_of_injective 2 (BinaryOffender.subspaceStabilizer ρ P)
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (congrArg (fun H : Subgroup Group => H.pCoreIn 2) hs)
/-- Every best offender is an actual end-node parabolic radical. -/
theorem best_endNode {A : Subgroup Group}
    (hA : IsBestOffender (exteriorAction 2) A) : IsEndNodeRadical A := by
  obtain ⟨g, hg⟩ := best_conjugate_shear hA
  have he := congrArg (fun B : Subgroup Group => B.map (MulAut.conj g⁻¹).toMonoidHom) hg
  rw [Subgroup.map_map] at he
  have hi : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id Group := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hi, Subgroup.map_id] at he
  rw [he]
  exact endNode_map_conj shear_endNode g⁻¹

end CFSG.Quasithin.ChapterK.Linear.Exterior.SourceFF
