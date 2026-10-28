module

public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsSingularComponentsLocal
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.OriginalHigmanSimsPointCore

/-!
# The returned nonsingular pair lies in the actual singular two-core

Two nonsingular binary vectors whose sum is singular are perpendicular to
that sum. The original marked coordinates therefore place both u and w in
the actual V₅ at z=u*w. In the hypothetical escaping HS branch, the proved
original perpendicular-core theorem puts this V₅ in O₂(G_z). This retains
the actual returned points, rather than replacing them by model vectors.

No inclusion of V_u in the common residual J is asserted: the native
residual has only half of that marked sixteen-space.

Source: the original polar geometry and F.9 reduction in Section12.6,
Aschbacher--Smith, printed pp.830--831.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open BinaryPermutation.TerminalOrthogonal.Eight
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

omit [Finite G] in
/-- Both original nonsingular points belong to the literal perpendicular
of their singular product under the unchanged full coordinates. -/
theorem OrthogonalMarking.nonsingular_pair_mem_singular_perpendicular
    {hn : L ≤ normalizer (V : Set G)} (D : OrthogonalMarking L V hn)
    (hZ : ZV L V = ⊥) (T : Sylow 2 G) (u w : V)
    (hu : D.Nonsingular u) (hw : D.Nonsingular w)
    (hs : ¬ D.Nonsingular (u*w)) :
    (u : G) ∈ (D.fullSetup hZ T (u*w)).V₅ ∧
      (w : G) ∈ (D.fullSetup hZ T (u*w)).V₅ := by
  let E := D.fullSetup hZ T (u*w)
  let f := D.fullCoordinates hZ
  have binary_one : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  have hqu : form (f u).toAdd = 1 :=
    binary_one _ ((D.fullCoordinates_nonsingular_iff hZ u).mpr hu)
  have hqw : form (f w).toAdd = 1 :=
    binary_one _ ((D.fullCoordinates_nonsingular_iff hZ w).mpr hw)
  have hqz : form (f (u*w)).toAdd = 0 := by
    by_contra hh
    exact hs ((D.fullCoordinates_nonsingular_iff hZ (u*w)).mp hh)
  have hu2 : u*u = 1 := by
    apply Subtype.ext
    change (u : G)*(u : G) = 1
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (u : G) u.property
  have hw2 : w*w = 1 := by
    apply Subtype.ext
    change (w : G)*(w : G) = 1
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) (w : G) w.property
  have hzu : (f (u*w)).toAdd + (f u).toAdd =
      (f w).toAdd := by
    change (f (u*w) * f u).toAdd = _
    rw [←map_mul,show (u*w)*u = w by rw [mul_comm u w,mul_assoc,hu2,mul_one]]
  have hzw : (f (u*w)).toAdd + (f w).toAdd =
      (f u).toAdd := by
    change (f (u*w) * f w).toAdd = _
    rw [←map_mul,mul_assoc,hw2,mul_one]
  constructor
  · apply (E.mem_V₅_iff u).mpr
    change form.polarBilin (f (u*w)).toAdd (f u).toAdd = 0
    rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,hzu,hqw,hqz,hqu]
    simp
  · apply (E.mem_V₅_iff w).mpr
    change form.polarBilin (f (u*w)).toAdd (f w).toAdd = 0
    rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,hzw,hqu,hqz,hqw]
    simp

/-- Under the original escaping HS hypotheses, each such pair lies in the
actual two-core of its singular product centralizer, through the same V₅. -/
theorem SourceHypothesis.original_hs_nonsingular_pair_mem_singular_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (v : V) (hv : D.Nonsingular v) (he : ¬ Gv (v : G) ≤ M L)
    (hZ : ZV L V = ⊥) (u w : V)
    (hu : D.Nonsingular u) (hw : D.Nonsingular w)
    (hz : u*w ≠ 1) (hs : ¬ D.Nonsingular (u*w)) :
    let E := D.fullSetup hZ T (u*w)
    E.V₅ ≤ (Gv ((u*w : V) : G)).pCoreIn 2 ∧
      (u : G) ∈ E.V₅ ∧ (w : G) ∈ E.V₅ ∧
      (u : G) ∈ (Gv ((u*w : V) : G)).pCoreIn 2 ∧
      (w : G) ∈ (Gv ((u*w : V) : G)).pCoreIn 2 := by
  obtain ⟨_,hc⟩ := H.original_hs_singular_perpendicular_core D hTV hTI v hv he
  have hcore := hc (u*w) hz hs
  obtain ⟨hu5,hw5⟩ := D.nonsingular_pair_mem_singular_perpendicular hZ T u w hu hw hs
  exact ⟨hcore,hu5,hw5,hcore hu5,hcore hw5⟩

end CFSG.Quasithin.Chapter12.Section06
