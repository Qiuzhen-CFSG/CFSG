module

public import Theory.AtlasPort.LinearGroups.G2.SolvableParabolic.RankOne
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.SylowNormalizer
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification.Stabilizer

/-!
# Solvable overgroups in the full long G₂ parabolic

Over a finite field of characteristic two and order greater than two, a solvable
subgroup containing the positive-root Sylow subgroup `U` and lying in the long
parabolic lies in the Borel.

First consider its intersection with `local₂`. The actual plane-quotient action
`longSLHom` contains every upper transvection, so the solvable rank-one lemma
forces upper-triangular images. The section represents these images by Borel
elements, and its kernel consists of five positive roots, also in the Borel.

For the full parabolic, relative normality of `local₂` puts every conjugate of
`U` by the given subgroup inside this intersection, hence inside `B = N(U)`.
Sylow maximality then puts each such two-subgroup inside `U`, proving that the
whole subgroup normalizes `U`.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528), the characteristic-two paragraph for p = 3. This proves the long
standard-Sylow refinement without A.3.15 or a Borel-containment premise.
The concrete root and block calculations are supplied by the imported licensed
ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section

open Subgroup
open Atlas.G2 Atlas.G2.Explicit Atlas.G2.PairStabilizer Atlas.G2.LieParabolicSetup
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
open scoped MatrixGroups

namespace Atlas.G2.SolvableParabolic
variable {F : Type*} [Field F] [CharP F 2]

private theorem local_mem_borel_of_lower_left_zero (g : local₂ (F := F))
    (hg : (longSLHom g).val 1 0 = 0) : g.val ∈ borel := by
  let m := longSLHom g
  let k := g * (longSLSection m)⁻¹
  have hk : k ∈ longSLHom.ker := by
    change longSLHom (g * (longSLSection m)⁻¹) = 1
    rw [map_mul, map_inv, longSLHom_section]
    exact mul_inv_cancel m
  rw [longSLHom_ker] at hk
  have hkU : k.val ∈ unipotent := (fiveRootSubgroup_le_unipotent 4 (Or.inl rfl)) hk
  have hmB : (longSLSection m).val ∈ borel :=
    block_mem_borel_of_lower_left_zero m hg
  have hb := borel.mul_mem ((show unipotent ≤ borel (K := F) from le_sup_left) hkU) hmB
  change g.val * (longSLSection m).val⁻¹ * (longSLSection m).val ∈ borel at hb
  simpa only [inv_mul_cancel_right] using hb

variable [Finite F]

private theorem long_local_standard_le_borel
    (hq : 2 < Nat.card F) (H : Subgroup (Model F))
    (hU : unipotent ≤ H) (hH : Group.IsSolvable H) (hL : H ≤ local₂) : H ≤ borel := by
  let : Group.IsSolvable H := hH
  let ρ : H →* Matrix (Fin 2) (Fin 2) F :=
    Matrix.SpecialLinearGroup.coeMonoidHom.comp (longSLHom.comp (Subgroup.inclusion hL))
  have hu (a : F) : ∃ g : H, ρ g = !![1,a;0,1] := by
    have ha : (longSLSection (upperSL a)).val ∈ H := by
      change blockHom (upperSL a) ∈ H
      rw [block_upper]
      exact hU (Subgroup.subset_closure (by simp))
    refine ⟨⟨(longSLSection (upperSL a)).val, ha⟩, ?_⟩
    change (longSLHom (longSLSection (upperSL a))).val = _
    rw [longSLHom_section]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [upperSL, Matrix.SpecialLinearGroup.transvection_coe]
  intro g hg
  exact local_mem_borel_of_lower_left_zero ⟨g, hL hg⟩
    (RankOne.representation_lower_left_eq_zero hq ρ hu ⟨g, hg⟩)

/-- A solvable overgroup of the standard Sylow two-subgroup inside the full
long parabolic lies in its Borel, over every finite field of characteristic two
and order greater than two. -/
theorem long_standard_le_borel
    (hq : 2 < Nat.card F) (H : Subgroup (Model F))
    (hU : unipotent ≤ H) (hH : Group.IsSolvable H) (hP : H ≤ parabolic₂) : H ≤ borel := by
  let : Group.IsSolvable H := hH
  have hI : Group.IsSolvable ↥(H ⊓ local₂ (F := F)) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (show H ⊓ local₂ ≤ H from inf_le_left))
      (Subgroup.inclusion_injective _)
  have hIB : H ⊓ local₂ ≤ borel := long_local_standard_le_borel hq _
    (le_inf hU unipotent_le_local₂) hI inf_le_right
  rw [← SylowNormalizer.normalizer_unipotent]
  apply le_normalizer_iff.mpr
  intro h hh u hu
  let V := (unipotent (K := F)).map (MulAut.conj h).toMonoidHom
  have hVH : V ≤ H := by
    rintro _ ⟨v, hv, rfl⟩
    exact H.mul_mem (H.mul_mem hh (hU hv)) (H.inv_mem hh)
  have hVL : V ≤ local₂ := by
    have hn := parabolic₂_le_normalizer_local₂ (hP hh)
    have he := mem_normalizer_iff_map_conj_eq.mp hn
    exact (map_mono unipotent_le_local₂).trans_eq he
  have hVB : V ≤ borel := (le_inf hVH hVL).trans hIB
  have hp : IsPGroup 2 V := unipotent_isTwoGroup.map _
  have hi := hp.inf_normalizer_sylow (sylow (F := F))
  change V ⊓ normalizer (unipotent (K := F) : Set (Model F)) = V ⊓ unipotent at hi
  rw [SylowNormalizer.normalizer_unipotent, inf_eq_left.mpr hVB] at hi
  exact (inf_eq_left.mp hi.symm) ⟨u, hu, rfl⟩

end Atlas.G2.SolvableParabolic
