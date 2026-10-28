module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The unipotent diagonal calculation is adapted from Atlas/LinearGroups/G2/Borel.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: character separation and rank-one torus-normalizer covers in the CFSG port.
-/

public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage.FrameAlignment.WeylCorrection
public import Theory.AtlasPort.LinearGroups.G2.EvenLocal.NormalizerCover.OctonionHexagon.CoordinateFrame

/-!
# Split-torus normalizers in the two standard parabolics

Over a finite field of characteristic two with more than two elements, the
six off-diagonal torus weights are distinct characters, including over F₄.
Indeed, a unit `a ≠ 1` also satisfies `a ≠ a⁻¹`; evaluating the weights at
`(a,1)` and `(1,a)` separates them. The only torus-invariant singular lines
are consequently the six coordinate lines. A normalizer permutes these lines,
and a normalizer in the Borel fixes each, since its diagonal entries are nonzero.
The existing coordinate-frame calculation then identifies it with the torus.

The short parabolic preserves the plane spanned by coordinates 0 and 1, so its
normalizers either fix coordinate 0 or do so after the short reflection. The
long parabolic fixes coordinate 0; the octonion zero product restricts the
image of coordinate 1 to coordinates 1 and 2. The long reflection corrects the
second case. In both cases the corrected element stabilizes the standard flag,
hence lies in the Borel. Conjugation gives the required order `torus l m * w`.

These are concrete subgroup calculations for the G₂ automorphism input used
in Aschbacher--Smith F.1.12, printed pp.263--264, and the invariant parabolics
in 2.3.9(7), printed p.526. They discharge precisely the two normalizer-cover
premises of `root_frame_alignment_of_rankOne_torusNormalizers`.
-/

public section

open Atlas.G2 Atlas.SplitOctonion Atlas.G2.Explicit
open Atlas.G2.LieParabolicSetup
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon.CosetIdentification
open Atlas.G2.EvenLocal.NormalizerCover.OctonionHexagon
namespace Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem exists_separating_unit (hq : 2 < Nat.card F) :
    ∃ a : Fˣ, a ≠ 1 ∧ a ≠ a⁻¹ := by
  classical
  let := Fintype.ofFinite F
  have hc : ({0,1} : Finset F).card < (Finset.univ : Finset F).card := by
    simpa [Nat.card_eq_fintype_card] using hq
  obtain ⟨t,_,ht⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have ht' : t ≠ 0 ∧ t ≠ 1 := by simpa using ht
  let a : Fˣ := Units.mk0 t ht'.1
  have ha : a ≠ 1 := by intro h; exact ht'.2 (congrArg Units.val h)
  refine ⟨a, ha, ?_⟩
  intro h
  have hh : t * t = 1 := by
    change (a : F) * (a : F) = 1
    conv_lhs => rhs; rw [h]
    simp
  have he : t = 1 ∨ t = -1 := (sq_eq_one_iff).mp (by simpa [pow_two] using hh)
  rcases he with he | he
  · exact ht'.2 he
  · exact ht'.2 (by simpa [CharTwo.neg_eq] using he)

private theorem torusWeights_separate (hq : 2 < Nat.card F) (i : Fin 6) (j : Fin 8)
    (h : ∀ l m : Fˣ, torusWeights l m (offDiagonalIndex i) = torusWeights l m j) :
    offDiagonalIndex i = j := by
  obtain ⟨a,ha,hainv⟩ := exists_separating_unit hq
  have ha' : a⁻¹ ≠ 1 := inv_ne_one.mpr ha
  have hai : a⁻¹ ≠ a := Ne.symm hainv
  have h1 := h a 1
  have h2 := h 1 a
  fin_cases i <;> fin_cases j <;>
    simp [torusWeights, offDiagonalIndex, ha, ha', Ne.symm ha, Ne.symm ha', hainv, hai] at h1 h2 ⊢

private theorem singular_eigenvector_coordinate (hq : 2 < Nat.card F) (x : Carrier F)
    (hx : x ≠ 0) (ht : trace x = 0) (hn : SplitOctonion.norm x = 0)
    (he : ∀ l m : Fˣ, ∃ c : F, (torus l m).val x = c • x) :
    ∃ i : Fin 6, ∃ c : Fˣ, x = (c : F) • offDiagonalVector i := by
  have hex : ∃ i : Fin 6, x (offDiagonalIndex i) ≠ 0 := by
    by_contra! hh
    have h0 := hh 0
    have h1 := hh 1
    have h2 := hh 2
    have h5 := hh 3
    have h6 := hh 4
    have h7 := hh 5
    simp only [offDiagonalIndex, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val] at h0 h1 h2 h5 h6 h7
    simp only [trace] at ht
    simp only [SplitOctonion.norm, h0,h1,h2,h5,h6,h7,zero_mul,zero_add] at hn
    have h3 : x 3 = 0 := by rcases mul_eq_zero.mp hn with hh | hh <;> simp_all
    have h4 : x 4 = 0 := by simpa [h3] using ht
    apply hx
    funext j
    fin_cases j <;> assumption
  obtain ⟨i,hi⟩ := hex
  have hs (j : Fin 8) (hj : x j ≠ 0) : offDiagonalIndex i = j := by
    apply torusWeights_separate hq i j
    intro l m
    obtain ⟨c,hc⟩ := he l m
    have hci := congrFun hc (offDiagonalIndex i)
    have hcj := congrFun hc j
    change (torusWeights l m (offDiagonalIndex i) : F) * x (offDiagonalIndex i) =
      c * x (offDiagonalIndex i) at hci
    change (torusWeights l m j : F) * x j = c * x j at hcj
    apply Units.ext
    exact (mul_right_cancel₀ hi hci).trans (mul_right_cancel₀ hj hcj).symm
  refine ⟨i, Units.mk0 _ hi, ?_⟩
  funext j
  by_cases hj : j = offDiagonalIndex i
  · subst j
    simp [offDiagonalVector, basisVector]
  · have hz : x j = 0 := by by_contra hn; exact hj (hs j hn).symm
    simp [offDiagonalVector, basisVector, hj, hz]

omit [Finite F] [CharP F 2] in
private theorem torus_basis (l m : Fˣ) (i : Fin 8) :
    (torus l m).val (basisVector i) = (torusWeights l m i : F) • basisVector i := by
  funext j
  by_cases hj : j = i
  · subst j; simp [torus, torusEquiv, torusLinear, basisVector]
  · simp [torus, torusEquiv, torusLinear, basisVector, hj]

private theorem normalizer_basis_image (hq : 2 < Nat.card F) (g : Model F)
    (hg : g ∈ Subgroup.normalizer (splitTorus (K := F) : Set (Model F))) (i : Fin 6) :
    ∃ j : Fin 6, ∃ c : Fˣ, g.val (offDiagonalVector i) = (c : F) • offDiagonalVector j := by
  apply singular_eigenvector_coordinate hq
  · exact fun hh => offDiagonalVector_ne_zero i (g.val.injective (hh.trans (map_zero g.val).symm))
  · rw [automorphism_trace]; exact (offDiagonal_singular i).1
  · rw [automorphism_norm]; exact (offDiagonal_singular i).2
  · intro l m
    have hh := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer _).inv_mem hg) (torus l m)).mp ⟨(l,m),rfl⟩
    obtain ⟨⟨a,b⟩,hab⟩ := hh
    change torus a b = g⁻¹ * torus l m * g⁻¹⁻¹ at hab
    rw [inv_inv] at hab
    have hcomm : torus l m * g = g * torus a b := by rw [hab]; group
    refine ⟨(torusWeights a b (offDiagonalIndex i) : F), ?_⟩
    have hc := congrArg (fun k : Model F => k.val (offDiagonalVector i)) hcomm
    change (torus l m).val (g.val (offDiagonalVector i)) =
      g.val ((torus a b).val (basisVector (offDiagonalIndex i))) at hc
    rw [torus_basis, map_smul] at hc
    exact hc

omit [Finite F] [CharP F 2] in
private theorem unipotent_diagonal (t : Fin 6 → F) (i : Fin 8) :
    (unipotentProduct t).val (basisVector i) i = 1 := by
  fin_cases i <;> simp [unipotentProduct,basisVector,
    rootA,rootB,rootC,rootD,rootE,rootF,
    rootAEquiv,rootBEquiv,rootCEquiv,
    rootDEquiv,rootEEquiv,rootFEquiv,
    rootALinear,rootBLinear,rootCLinear,
    rootDLinear,rootELinear,rootFLinear,
    rootAApply,rootBApply,rootCApply,
    rootDApply,rootEApply,rootFApply]

omit [Finite F] [CharP F 2] in
private theorem borel_diagonal_ne_zero (g : Model F) (hg : g ∈ borel) (i : Fin 8) :
    g.val (basisVector i) i ≠ 0 := by
  obtain ⟨⟨u,t⟩,he⟩ := borelProductEquiv.surjective ⟨g,hg⟩
  have he : u.val * t.val = g := congrArg Subtype.val he
  have hu := u.property
  simp only [unipotent_eq_range] at hu
  obtain ⟨v,hv⟩ := hu
  obtain ⟨⟨l,m⟩,ht⟩ := t.property
  rw [← he, ← hv, ← ht]
  change (unipotentProduct v).val ((torus l m).val (basisVector i)) i ≠ 0
  rw [torus_basis, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul, unipotent_diagonal, mul_one]
  exact Units.ne_zero _

private theorem borel_torusNormalizer_le_torus (hq : 2 < Nat.card F) (g : Model F)
    (hb : g ∈ borel) (hn : g ∈ Subgroup.normalizer (splitTorus (K := F) : Set (Model F))) :
    g ∈ splitTorus := by
  apply (fixes_coordinatePoints_iff g).mp
  intro i
  rw [coordinatePoint_fixed_iff]
  obtain ⟨j,c,hc⟩ := normalizer_basis_image hq g hn i
  have hi := borel_diagonal_ne_zero g hb (offDiagonalIndex i)
  have he : offDiagonalIndex i = offDiagonalIndex j := by
    by_contra hh
    change g.val (offDiagonalVector i) (offDiagonalIndex i) ≠ 0 at hi
    rw [hc] at hi
    simp [offDiagonalVector, basisVector, hh] at hi
  refine ⟨c, ?_⟩
  simpa only [offDiagonalVector, ← he] using hc

omit [Finite F] [CharP F 2] in
private theorem basis_zero_mem_plane : (basisVector 0 : Carrier F) ∈ standardPlane := by
  rw [mem_standardPlane_iff_coordinates]
  simp [basisVector]

omit [Finite F] [CharP F 2] in
private theorem basis_one_mem_plane : (basisVector 1 : Carrier F) ∈ standardPlane := by
  rw [mem_standardPlane_iff_coordinates]
  simp [basisVector]

omit [Finite F] [CharP F 2] in
private theorem short_basis_image_mem_plane (g : Model F) (hg : g ∈ parabolic₁) :
    g.val (basisVector 0) ∈ standardPlane := by
  have hline := shortParabolic_le_lineStabilizer hg
  have hmem := (mem_line_smul g standardLine (basisVector 0)).mpr basis_zero_mem_plane
  rw [show g • standardLine = standardLine from hline] at hmem
  exact hmem

omit [Finite F] [CharP F 2] in
private theorem coset_of_left_correction (g w : Model F)
    (hn : g ∈ Subgroup.normalizer (splitTorus (K := F) : Set (Model F)))
    (hww : w*w = 1) (hwg : w*g ∈ splitTorus) :
    ∃ l m : Fˣ, g = torus l m * w := by
  have ht := (Subgroup.mem_normalizer_iff.mp hn (w*g)).mp hwg
  have ht' : g*w ∈ splitTorus := by
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using ht
  obtain ⟨⟨l,m⟩,he⟩ := ht'
  change torus l m = g*w at he
  exact ⟨l,m, by rw [he, mul_assoc, hww, mul_one]⟩

/-- In the short standard parabolic, the split-torus normalizer is covered by
its torus and the right coset represented by `weylS`, also over F₄. -/
theorem rankOne_torusNormalizerCover_short (hq : 2 < Nat.card F) :
    RankOneTorusNormalizerCover (parabolic₁ (F := F)) weylS := by
  intro g hp hn
  obtain ⟨j,c,hc⟩ := normalizer_basis_image hq g hn 0
  change g.val (basisVector 0) = (c : F) • offDiagonalVector j at hc
  have hm := short_basis_image_mem_plane g hp
  rw [hc, mem_standardPlane_iff_coordinates] at hm
  have hj : j = 0 ∨ j = 1 := by
    fin_cases j <;> simp_all [offDiagonalVector, offDiagonalIndex, basisVector, Units.ne_zero]
  rcases hj with rfl | rfl
  · left
    apply borel_torusNormalizer_le_torus hq g _ hn
    rw [← SylowNormalizer.parabolics_intersection]
    refine ⟨hp, ?_⟩
    rw [parabolic₂, parabolic_eq_pointStabilizer]
    apply (mem_pointStabilizer_iff _).mpr
    exact ⟨c, by simpa [offDiagonalVector,offDiagonalIndex,Units.smul_def] using hc⟩
  · right
    apply coset_of_left_correction g weylS hn (by rw [← pow_two, weylS_sq])
    apply borel_torusNormalizer_le_torus hq (weylS*g)
    · rw [← SylowNormalizer.parabolics_intersection]
      refine ⟨parabolic₁.mul_mem weylS_mem_shortParabolic hp, ?_⟩
      rw [parabolic₂, parabolic_eq_pointStabilizer]
      apply (mem_pointStabilizer_iff _).mpr
      refine ⟨c, ?_⟩
      change weylS.val (g.val (basisVector 0)) = _
      rw [hc, map_smul]
      funext k
      fin_cases k <;> simp [weylS,weylSEquiv,weylSLinear,weylSApply,
        offDiagonalVector,offDiagonalIndex,basisVector,CharTwo.neg_eq,Units.smul_def]
    · exact (Subgroup.normalizer _).mul_mem weylS_mem_torusNormalizer hn
private theorem long_second_basis_image (hq : 2 < Nat.card F) (g : Model F)
    (hp : g ∈ parabolic₂)
    (hn : g ∈ Subgroup.normalizer (splitTorus (K := F) : Set (Model F))) :
    ∃ c : Fˣ, g.val (basisVector 1) = (c : F) • basisVector 1 ∨
      g.val (basisVector 1) = (c : F) • basisVector 2 := by
  have hp' : g ∈ pointStabilizer := by rwa [parabolic₂, parabolic_eq_pointStabilizer] at hp
  obtain ⟨a,ha⟩ := (mem_pointStabilizer_iff g).mp hp'
  simp only [Units.smul_def] at ha
  obtain ⟨j,c,hc⟩ := normalizer_basis_image hq g hn 1
  change g.val (basisVector 1) = (c : F) • offDiagonalVector j at hc
  have h01 : mul (basisVector (F := F) 0) (basisVector 1) = 0 := by
    funext k
    fin_cases k <;> simp [mul,basisVector]
  have hh := automorphism_mul g (basisVector 0) (basisVector 1)
  rw [h01, map_zero, ha, hc] at hh
  have hz : mul (basisVector (F := F) 0) (offDiagonalVector j) = 0 := by
    simpa [SplitOctonion.smul_mul, SplitOctonion.mul_smul, smul_smul] using hh.symm
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by
    have h1 := congrFun hz 1
    have h2 := congrFun hz 2
    have h3 := congrFun hz 3
    fin_cases j <;> simp_all [mul, offDiagonalVector, offDiagonalIndex, basisVector]
  rcases hj with rfl | rfl | rfl
  · have he : g.val (((c : F)/(a : F)) • basisVector 0) = g.val (basisVector 1) := by
      rw [map_smul, ha, hc, smul_smul]
      simp [offDiagonalVector, offDiagonalIndex]
    have he' := congrFun (g.val.injective he) 1
    simp [basisVector] at he'
  · exact ⟨c, Or.inl (by simpa [offDiagonalVector,offDiagonalIndex] using hc)⟩
  · exact ⟨c, Or.inr (by simpa [offDiagonalVector,offDiagonalIndex] using hc)⟩

omit [Finite F] in
private theorem weylR_basis_zero : (weylR : Model F).val (basisVector 0) = basisVector 0 := by
  funext k
  fin_cases k <;> simp [weylR,weylREquiv,weylRLinear,weylRApply,basisVector,CharTwo.neg_eq]

omit [Finite F] in
private theorem weylR_basis_two : (weylR : Model F).val (basisVector 2) = basisVector 1 := by
  funext k
  fin_cases k <;> simp [weylR,weylREquiv,weylRLinear,weylRApply,basisVector,CharTwo.neg_eq]

/-- In the long standard parabolic, the split-torus normalizer is covered by
its torus and the right coset represented by `weylR`, also over F₄. -/
theorem rankOne_torusNormalizerCover_long (hq : 2 < Nat.card F) :
    RankOneTorusNormalizerCover (parabolic₂ (F := F)) weylR := by
  intro g hp hn
  have hp' : g ∈ pointStabilizer := by rwa [parabolic₂, parabolic_eq_pointStabilizer] at hp
  obtain ⟨a,ha⟩ := (mem_pointStabilizer_iff g).mp hp'
  simp only [Units.smul_def] at ha
  obtain ⟨c,hc | hc⟩ := long_second_basis_image hq g hp hn
  · left
    apply borel_torusNormalizer_le_torus hq g _ hn
    rw [← SylowNormalizer.parabolics_intersection]
    refine ⟨?_,hp⟩
    rw [shortParabolic_eq_lineStabilizer]
    apply fixes_standardLine_of_basis_images
    · rw [ha]; exact standardPlane.smul_mem _ basis_zero_mem_plane
    · rw [hc]; exact standardPlane.smul_mem _ basis_one_mem_plane
  · right
    apply coset_of_left_correction g weylR hn (by rw [← pow_two, weylR_sq])
    apply borel_torusNormalizer_le_torus hq (weylR*g)
    · rw [← SylowNormalizer.parabolics_intersection]
      refine ⟨?_, parabolic₂.mul_mem weylR_mem_parabolic hp⟩
      rw [shortParabolic_eq_lineStabilizer]
      apply fixes_standardLine_of_basis_images
      · change weylR.val (g.val (basisVector 0)) ∈ standardPlane
        rw [ha, map_smul, weylR_basis_zero]
        exact standardPlane.smul_mem _ basis_zero_mem_plane
      · change weylR.val (g.val (basisVector 1)) ∈ standardPlane
        rw [hc, map_smul, weylR_basis_two]
        exact standardPlane.smul_mem _ basis_one_mem_plane
    · exact (Subgroup.normalizer _).mul_mem weylR_mem_torusNormalizer hn
end Atlas.G2.LieAutomorphismExtensions.InnerFieldCoverage

end
