module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition.DegreeSelection.Outer.Geometry
public import Theory.Representation.SL2.BinaryInvolutionDisplacement

/-!
# Inner PSL₂ involutions on the original Chapter K module

The actual marking `L ≃* SL₂(K)` transports the layer restriction to an
irreducible binary SL₂ representation. Faithfulness makes its action
nontrivial. The intrinsic involution bound then gives half-dimension
displacement for every nonidentity involution in the original subgroup L.

This discharges `hinner` in the Schur-linear degree-selection argument.
The outer involution calculation and final degree assembly remain with that
argument; no recognition, degree, or tensor-displacement premise is added here.

Source: Aschbacher–Smith, Chapter K, printed pp.451,453–454;
Guralnick–Malle, Classification of 2F-modules II, §3.5 and Proposition 4.1(2),
manuscript pp.20,22.
-/

public section
open scoped MatrixGroups
open Representation
namespace CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  {K : Type*} [Field K] [Finite K] [CharP K 2]
  (h : SourceHypotheses ρ L) (e : L ≃* SL(2,K))

include h e

omit [Finite G] in
/-- Every nonidentity inner involution moves at least half of the original
binary module. This supplies the literal `hinner` premise of the Schur-linear
degree argument without a degree, recognition, or offender assumption. -/
theorem psl2_inner_involution_displacement (x : G) (hx : x ∈ L)
    (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) :
    Module.finrank (ZMod 2) V ≤
      2 * Module.finrank (ZMod 2) (LinearMap.range (ρ x - 1)) := by
  let σ : Representation (ZMod 2) SL(2,K) V :=
    (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp L.subtype)).mpr h.irreducible
  let y : SL(2,K) := e ⟨x, hx⟩
  have hy1 : y ≠ 1 := by
    intro he
    have hh : (⟨x, hx⟩ : L) = 1 := e.injective (he.trans (map_one e).symm)
    exact hx1 (congrArg Subtype.val hh)
  have hy2 : y ^ 2 = 1 := by
    change (e ⟨x, hx⟩) ^ 2 = 1
    rw [← map_pow]
    have hh : (⟨x, hx⟩ : L) ^ 2 = 1 := Subtype.ext hx2
    rw [hh, map_one]
  have hyρ : σ y = ρ x := by
    change ρ (e.symm (e ⟨x, hx⟩) : L) = ρ x
    rw [e.symm_apply_apply]
  have hn : σ y ≠ 1 := by
    rw [hyρ]
    intro he
    exact hx1 (h.faithful (he.trans (map_one ρ).symm))
  have hh := Representation.SL2.binary_involution_displacement σ ⟨y, hn⟩ y hy1 hy2
  rwa [hyρ] at hh

end CFSG.Quasithin.ChapterK.RankOne.SourceHypotheses
