module

public import Theory.AtlasPort.LinearGroups.G2.SolvableParabolic.RankOne
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification.Stabilizer

/-!
# Solvable overgroups of the positive roots in the full short G₂ parabolic

The full short parabolic preserves the plane spanned by the first two octonion
basis vectors. Its action on this plane is a two-dimensional matrix
representation, and the positive root `rootF` supplies every upper
transvection. Over a finite field of characteristic two with more than two
elements, the rank-one solvability lemma forces the lower-left entry to
vanish. Thus a solvable overgroup of the positive roots fixes the first
projective point as well as the plane, so it lies in the Borel flag stabilizer.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528), the characteristic-two paragraph for p = 3. The argument uses
the full `parabolic₁`, including its torus, and does not invoke A.3.15.

The split-octonion model, root coordinates and flag stabilizers are from the
licensed ATLAS port by Gerald Höhn and the ATLAS contributors; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff. This module adds the plane
representation and its solvable-subgroup refinement.
-/

public section

namespace Atlas.G2.SolvableParabolic

open Atlas.SplitOctonion Explicit LieParabolicSetup
open EvenLocal.NormalizerCover.OctonionHexagon
open EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification

variable {F : Type*} [Field F]

private theorem plane_decomposition {x : Carrier F} (hx : x ∈ standardPlane) :
    x = x 0 • basisVector 0 + x 1 • basisVector 1 := by
  obtain ⟨h2,h3,h4,h5,h6,h7⟩ := (mem_standardPlane_iff_coordinates x).mp hx
  funext i
  fin_cases i <;> simp [basisVector,h2,h3,h4,h5,h6,h7]

private theorem short_preserves_plane (g : parabolic₁ (F := F))
    {x : Carrier F} (hx : x ∈ standardPlane) : g.val.val x ∈ standardPlane := by
  have he : g.val • (standardLine (F := F)) = standardLine :=
    shortParabolic_le_lineStabilizer g.property
  have hm := (mem_line_smul g.val standardLine x).mpr hx
  rwa [he] at hm

private theorem short_basis_decomposition (g : parabolic₁ (F := F)) (j : Fin 2) :
    g.val.val (basisVector (j.castLE (by decide : 2 ≤ 8))) =
      g.val.val (basisVector (j.castLE (by decide : 2 ≤ 8))) 0 • basisVector 0 +
      g.val.val (basisVector (j.castLE (by decide : 2 ≤ 8))) 1 • basisVector 1 := by
  apply plane_decomposition
  apply short_preserves_plane g
  fin_cases j <;> exact Submodule.subset_span (by simp)

/-- The actual action of the full short parabolic on its invariant plane. -/
private def shortRepresentation : parabolic₁ (F := F) →* Matrix (Fin 2) (Fin 2) F where
  toFun g i j := g.val.val (basisVector (j.castLE (by decide : 2 ≤ 8)))
    (i.castLE (by decide : 2 ≤ 8))
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [basisVector]
  map_mul' g h := by
    ext i j
    change g.val.val (h.val.val (basisVector (j.castLE (by decide : 2 ≤ 8))))
      (i.castLE (by decide : 2 ≤ 8)) =
      ∑ k : Fin 2, g.val.val (basisVector (k.castLE (by decide : 2 ≤ 8)))
        (i.castLE (by decide : 2 ≤ 8)) *
        h.val.val (basisVector (j.castLE (by decide : 2 ≤ 8)))
          (k.castLE (by decide : 2 ≤ 8))
    rw [short_basis_decomposition h j, map_add, map_smul, map_smul]
    simp [Fin.sum_univ_two, basisVector, mul_comm]

private theorem rootF_mem_unipotent (a : F) : rootF a ∈ unipotent :=
  Subgroup.subset_closure (by simp)

private theorem shortRepresentation_rootF (a : F) :
    shortRepresentation ⟨rootF (-a), rootF_mem_shortParabolic (-a)⟩ = !![1,a;0,1] := by
  ext i j
  change (rootF (-a)).val (basisVector (j.castLE (by decide : 2 ≤ 8)))
    (i.castLE (by decide : 2 ≤ 8)) = _
  fin_cases i <;> fin_cases j <;>
    simp [rootF,rootFEquiv,rootFLinear,rootFApply,basisVector]

/-- A solvable overgroup of the standard positive-root subgroup in the full
short parabolic lies in the standard Borel when the field has order above two. -/
theorem short_standard_le_borel [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F) (H : Subgroup (Model F))
    (hU : unipotent ≤ H) (hH : Group.IsSolvable H) (hHP : H ≤ parabolic₁) :
    H ≤ borel := by
  let : Group.IsSolvable H := hH
  let ρ := shortRepresentation.comp (Subgroup.inclusion hHP)
  have hu : ∀ a : F, ∃ g : H, ρ g = !![1,a;0,1] := by
    intro a
    refine ⟨⟨rootF (-a), hU (rootF_mem_unipotent (-a))⟩, ?_⟩
    exact shortRepresentation_rootF a
  intro g hg
  have hz : g.val (basisVector 0) 1 = 0 :=
    RankOne.representation_lower_left_eq_zero hq ρ hu ⟨g,hg⟩
  have he := short_basis_decomposition ⟨g,hHP hg⟩ 0
  change g.val (basisVector 0) =
    g.val (basisVector 0) 0 • basisVector 0 + g.val (basisVector 0) 1 • basisVector 1 at he
  rw [hz, zero_smul, add_zero] at he
  have ha : g.val (basisVector 0) 0 ≠ 0 := by
    intro ha
    rw [ha, zero_smul] at he
    exact first_basis_ne_zero (g.val.injective (he.trans (map_zero g.val).symm))
  have hp : g ∈ pointStabilizer := by
    apply (mem_pointStabilizer_iff g).mpr
    refine ⟨Units.mk0 _ ha, ?_⟩
    simpa only [Units.smul_def, Units.val_mk0] using he
  exact standardFlag_stabilizer.le ⟨hp,shortParabolic_le_lineStabilizer (hHP hg)⟩

end Atlas.G2.SolvableParabolic
