module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.Cosets
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.Separation
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.LinearCover.RankOne
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.LinearCover.BorelGeneration
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.LinearCover.Normalization

/-!
# The linear parabolic cover from local root geometry

Let `X` and `Y` be the negative and positive linear blocks, and let `n` be
the proved paired Weyl representative. The scalar rank-one identities show
that `X` and `Y` preserve `X B ∪ n B`. The prescribed radical also preserves
these cells when `X` normalizes it and Weyl conjugation carries it into the
Borel. The fixed torus preserves them when it normalizes `X` and has the
same Weyl-conjugation property. Borel generation by `Y`, the radical and
the torus therefore gives coverage for every element of `B ⊔ X`.

The final cover theorem discharges these geometric inputs using ordered
fixed-root collection, root exchanges, diagonal scaling, and the paired
Weyl action. It assumes only equality of the coroot-word and diagonal tori;
no simplicity, perfectness, odd index, or lower bound on `m` is needed.
The cover concerns actual left Borel cosets. Index assembly remains in
`LocalIndices`.

Source: GLS3, Theorems 2.3.4–8, Table 2.4 type VI, and the rank-one case
of the Levi decomposition in 2.6.5, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices
open Subgroup LargeLocalSeeds Parabolics BlockParameters.FieldRecovery
variable {m : ℕ}

private def panelCell (d : LocalBlockInput m) (g : d.fixedGroup) : Prop :=
  (linearPanelWeyl d 1)⁻¹ * g ∈ rootBorel d ∨
    ∃ u : simpleBlock d .linear false, u.val⁻¹ * g ∈ rootBorel d

private theorem cell_of_borel (d : LocalBlockInput m) {g : d.fixedGroup}
    (hg : g ∈ rootBorel d) : panelCell d g := by
  right
  exact ⟨1, by simpa using hg⟩

private theorem cell_weyl (d : LocalBlockInput m) : panelCell d (linearPanelWeyl d 1) := by
  left
  rw [inv_mul_cancel]
  exact one_mem _

private theorem cell_mul_borel (d : LocalBlockInput m) {g b : d.fixedGroup}
    (hg : panelCell d g) (hb : b ∈ rootBorel d) : panelCell d (g * b) := by
  rcases hg with hg | ⟨u, hu⟩
  · exact Or.inl (by simpa only [mul_assoc] using (rootBorel d).mul_mem hg hb)
  · exact Or.inr ⟨u, by simpa only [mul_assoc] using (rootBorel d).mul_mem hu hb⟩

private theorem positive_mul_weyl_cell (d : LocalBlockInput m) (a : CoefficientField m) :
    panelCell d (linearElement d true a * linearPanelWeyl d 1) := by
  by_cases ha : a = 0
  · simpa only [ha, linearElement_zero, one_mul] using cell_weyl d
  · let t : (CoefficientField m)ˣ := Units.mk0 a ha
    right
    refine ⟨linearEquiv d false (Multiplicative.ofAdd a⁻¹), ?_⟩
    change (linearElement d false a⁻¹)⁻¹ * (linearElement d true a * linearPanelWeyl d 1) ∈ rootBorel d
    have hratio := (rootBorel d).inv_mem (linearPanelWeyl_ratio_mem_borel d t)
    simp only [mul_inv_rev, linearPanelWeyl_inv] at hratio
    have hp := (rootBorel d).mul_mem (linearElement_positive_mem_borel d a) hratio
    convert hp using 1
    have hw : linearPanelWeyl d t = linearElement d true a *
        linearElement d false a⁻¹ * linearElement d true a := by
      simp only [linearPanelWeyl, Units.val_inv_eq_inv_val, t, Units.val_mk0]
    rw [linearElement_inv, hw]
    symm
    calc
      _ = (linearElement d true a * linearElement d true a) *
          (linearElement d false a⁻¹ * (linearElement d true a * linearPanelWeyl d 1)) := by group
      _ = _ := by rw [linearElement_self_mul, one_mul]

private theorem positive_mul_negative_cell (d : LocalBlockInput m) (a b : CoefficientField m) :
    panelCell d (linearElement d true a * linearElement d false b) := by
  by_cases hb : b = 0
  · simpa only [hb, linearElement_zero, mul_one] using
      cell_of_borel d (linearElement_positive_mem_borel d a)
  · let t : (CoefficientField m)ˣ := (Units.mk0 b hb)⁻¹
    have hborel : (linearPanelWeyl d 1)⁻¹ * linearPanelWeyl d t *
        linearElement d true b⁻¹ ∈ rootBorel d :=
      (rootBorel d).mul_mem (linearPanelWeyl_ratio_mem_borel d t)
        (linearElement_positive_mem_borel d b⁻¹)
    have h := cell_mul_borel d (positive_mul_weyl_cell d (a + b⁻¹)) hborel
    convert h using 1
    rw [linearElement_add]
    have hw : linearPanelWeyl d t = linearElement d true b⁻¹ *
        linearElement d false b * linearElement d true b⁻¹ := by
      simp only [linearPanelWeyl, t, Units.val_inv_eq_inv_val, Units.val_mk0, inv_inv]
    symm
    calc
      _ = linearElement d true a *
          (linearElement d true b⁻¹ * linearPanelWeyl d t * linearElement d true b⁻¹) := by group
      _ = _ := by
        rw [hw]
        have hy := linearElement_self_mul d true b⁻¹
        calc
          _ = linearElement d true a *
              ((linearElement d true b⁻¹ * linearElement d true b⁻¹) * linearElement d false b *
                (linearElement d true b⁻¹ * linearElement d true b⁻¹)) := by group
          _ = _ := by rw [hy]; simp only [one_mul, mul_one]

private def leftCellStabilizer {G : Type*} [Group G] (p : G → Prop) : Subgroup G where
  carrier := {a | ∀ g, p (a * g) ↔ p g}
  one_mem' := by intro g; simp
  mul_mem' := by
    intro a b ha hb g
    rw [mul_assoc, ha, hb]
  inv_mem' := by
    intro a ha g
    simpa only [mul_inv_cancel_left] using (ha (a⁻¹ * g)).symm

private theorem le_leftCellStabilizer {G : Type*} [Group G] (p : G → Prop)
    (H : Subgroup G) (h : ∀ a ∈ H, ∀ g, p g → p (a * g)) :
    H ≤ leftCellStabilizer p := by
  intro a ha g
  constructor
  · intro hg
    simpa only [inv_mul_cancel_left] using h a⁻¹ (H.inv_mem ha) (a * g) hg
  · exact h a ha g

private theorem positive_stabilizes (d : LocalBlockInput m) :
    simpleBlock d .linear true ≤ leftCellStabilizer (panelCell d) := by
  apply le_leftCellStabilizer
  intro y hy g hg
  obtain ⟨a, rfl⟩ := linearElement_surjective d true hy
  rcases hg with hg | ⟨u, hu⟩
  · have h := cell_mul_borel d (positive_mul_weyl_cell d a) hg
    simpa only [mul_assoc, mul_inv_cancel_left] using h
  · obtain ⟨b, hb⟩ := linearElement_surjective d false u.property
    have h := cell_mul_borel d (positive_mul_negative_cell d a b) hu
    simpa only [hb, mul_assoc, mul_inv_cancel_left] using h

private theorem negative_stabilizes (d : LocalBlockInput m) :
    simpleBlock d .linear false ≤ leftCellStabilizer (panelCell d) := by
  apply le_leftCellStabilizer
  intro x hx g hg
  rcases hg with hg | ⟨u, hu⟩
  · obtain ⟨a, rfl⟩ := linearElement_surjective d false hx
    left
    have hconj : (linearPanelWeyl d 1)⁻¹ * linearElement d false a * linearPanelWeyl d 1 ∈
        rootBorel d := by
      have hc := linearPanelWeyl_conj_negative d a
      rw [linearPanelWeyl_inv] at hc
      simpa only [linearPanelWeyl_inv, hc] using linearElement_positive_mem_borel d a
    convert (rootBorel d).mul_mem hconj hg using 1
    group
  · right
    refine ⟨⟨x, hx⟩ * u, ?_⟩
    simpa only [Subgroup.coe_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hu

/-- Root generation and the two normalization actions imply coverage of every
actual coset. The remaining hypotheses are root geometry, not an index or a cover. -/
theorem linear_rankOneCover_of_root_geometry (d : LocalBlockInput m)
    (hgen : rootBorel d ≤ (simpleBlock d .linear true ⊔ linearPanelRadical d) ⊔ linearPanelTorus d)
    (hRX : simpleBlock d .linear false ≤ normalizer (linearPanelRadical d))
    (hTX : linearPanelTorus d ≤ normalizer (simpleBlock d .linear false))
    (hRn : linearPanelRadical d ≤ (rootBorel d).comap
      (MulAut.conj (linearPanelWeyl d 1)).toMonoidHom)
    (hTn : linearPanelTorus d ≤ (rootBorel d).comap
      (MulAut.conj (linearPanelWeyl d 1)).toMonoidHom) :
    RankOneCover d .linear (linearPanelRepresentative d) := by
  have hR : linearPanelRadical d ≤ leftCellStabilizer (panelCell d) := by
    apply le_leftCellStabilizer
    intro r hr g hg
    rcases hg with hg | ⟨u, hu⟩
    · left
      have hn := hRn hr
      change linearPanelWeyl d 1 * r * (linearPanelWeyl d 1)⁻¹ ∈ rootBorel d at hn
      have hn' : (linearPanelWeyl d 1)⁻¹ * r * linearPanelWeyl d 1 ∈ rootBorel d := by
        simpa only [linearPanelWeyl_inv] using hn
      convert (rootBorel d).mul_mem hn' hg using 1
      group
    · right
      refine ⟨u, ?_⟩
      have hconj := (mem_normalizer_iff.mp (hRX ((simpleBlock d .linear false).inv_mem u.property)) r).mp hr
      have h := (rootBorel d).mul_mem (linearPanelRadical_le_borel d hconj) hu
      convert h using 1
      group
  have hT : linearPanelTorus d ≤ leftCellStabilizer (panelCell d) := by
    apply le_leftCellStabilizer
    intro t ht g hg
    rcases hg with hg | ⟨u, hu⟩
    · left
      have hn := hTn ht
      change linearPanelWeyl d 1 * t * (linearPanelWeyl d 1)⁻¹ ∈ rootBorel d at hn
      have hn' : (linearPanelWeyl d 1)⁻¹ * t * linearPanelWeyl d 1 ∈ rootBorel d := by
        simpa only [linearPanelWeyl_inv] using hn
      convert (rootBorel d).mul_mem hn' hg using 1
      group
    · right
      refine ⟨⟨t * u.val * t⁻¹, (mem_normalizer_iff.mp (hTX ht) u.val).mp u.property⟩, ?_⟩
      have h := (rootBorel d).mul_mem (linearPanelTorus_le_borel d ht) hu
      convert h using 1
      group
  have hP : rootParabolic d .linear ≤ leftCellStabilizer (panelCell d) :=
    sup_le (hgen.trans (sup_le (sup_le (positive_stabilizes d) hR) hT)) (negative_stabilizes d)
  intro g
  have h := (hP g.property 1).mpr (cell_of_borel d (one_mem (rootBorel d)))
  change panelCell d g.val
  simpa only [mul_one] using h

/-- The paired Weyl representative and the negative linear block cover every
actual Borel coset in the generated linear parabolic. -/
theorem linear_rankOneCover (d : LocalBlockInput m)
    (hT : splitTorus m = diagonalTorus m) :
    RankOneCover d .linear (linearPanelRepresentative d) :=
  linear_rankOneCover_of_root_geometry d
    (rootBorel_le_linearBlock_sup_radical_sup_torus d hT)
    (linear_negative_le_radical_normalizer d)
    (linearPanelTorus_le_negative_normalizer d hT)
    (linearPanelRadical_le_borel_comap_weyl d)
    (linearPanelTorus_le_borel_comap_weyl d)

/-- Existence of the linear parabolic coset cover, with all root-generation
and conjugation premises discharged. -/
theorem exists_linear_rankOneCover (d : LocalBlockInput m)
    (hT : splitTorus m = diagonalTorus m) :
    ∃ n : rootParabolic d .linear, RankOneCover d .linear n :=
  ⟨linearPanelRepresentative d, linear_rankOneCover d hT⟩

end ReeF4.LocalBlockInput.PairRigidity.LocalIndices
