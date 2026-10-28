module
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.Cosets
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.Separation
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.RankOne
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.BorelGeneration
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Gauss
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition.LocalIndices.SuzukiCover.Normalization

/-!
# The Suzuki parabolic cover from local root calculations

Let `X` be the negative Suzuki block, `B` the root Borel, and `n` the
middle longest-word representative. The negative block preserves the two
cells `X B ∪ n B`, since it acts by translation on the first and fixes the
second. The local Suzuki inversion identity makes `n` preserve these cells,
so the conjugate positive block preserves them too.

The prescribed radical preserves both cells when `X` normalizes it and its
Weyl conjugate lies in `B`. The fixed torus does so when it normalizes `X`
and its Weyl conjugate lies in `B`. Generation of `B` by the positive block,
radical and torus then proves coverage for every element of `B ⊔ X`.
The subgroup-stabilizer argument follows the existing linear-cover proof.

The final cover theorem discharges the local inversion, fixed-factor generation,
and conjugation premises using `Gauss`, `BorelGeneration`, and `Normalization`.
It retains the explicit full signed Suzuki coordinates and the equality of the
coroot and diagonal tori. The representative is the actual middle Weyl word
inside the generated parabolic. Borel-index assembly stays in `LocalIndices`.

Source: GLS3, Theorems 2.3.4–8, Table 2.4 type V, and 2.6.5,
`refs/KGroup/GLS3/chapter2.tex`. The field size here is `2^(2*m+1)`,
the square of the book's Suzuki–Ree parameter.
-/

public section
namespace ReeF4.LocalBlockInput.PairRigidity.LocalIndices
open Subgroup LargeLocalSeeds Parabolics BlockParameters.FieldRecovery
variable {m : ℕ}

private def suzukiCell (d : LocalBlockInput m) (g : d.fixedGroup) : Prop :=
  (suzukiPanelWeyl d)⁻¹ * g ∈ rootBorel d ∨
    ∃ u : simpleBlock d .suzuki false, u.val⁻¹ * g ∈ rootBorel d

private theorem cell_of_borel (d : LocalBlockInput m) {g : d.fixedGroup}
    (hg : g ∈ rootBorel d) : suzukiCell d g := by
  right
  exact ⟨1, by simpa using hg⟩

private theorem cell_weyl (d : LocalBlockInput m) : suzukiCell d (suzukiPanelWeyl d) := by
  left
  rw [inv_mul_cancel]
  exact one_mem _

private theorem cell_mul_borel (d : LocalBlockInput m) {g b : d.fixedGroup}
    (hg : suzukiCell d g) (hb : b ∈ rootBorel d) : suzukiCell d (g * b) := by
  rcases hg with hg | ⟨u, hu⟩
  · exact Or.inl (by simpa only [mul_assoc] using (rootBorel d).mul_mem hg hb)
  · exact Or.inr ⟨u, by simpa only [mul_assoc] using (rootBorel d).mul_mem hu hb⟩

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

private theorem weyl_stabilizes (d : LocalBlockInput m) (C : SuzukiCoordinates d)
    (hG : SuzukiGauss d C) : suzukiPanelWeyl d ∈ leftCellStabilizer (suzukiCell d) := by
  have hn : ∀ g, suzukiCell d g → suzukiCell d (suzukiPanelWeyl d * g) := by
    intro g hg
    rcases hg with hg | ⟨x, hx⟩
    · exact cell_of_borel d (by simpa only [suzukiPanelWeyl_inv] using hg)
    · obtain ⟨t, u, htu⟩ := C.element_cover false x.property
      by_cases hz : t = 0 ∧ u = 0
      · have hx1 : x.val = 1 := by rw [← htu, hz.1, hz.2, C.element_zero]
        have hb : g ∈ rootBorel d := by simpa only [hx1, inv_one, one_mul] using hx
        exact cell_mul_borel d (cell_weyl d) hb
      · have hne : t ≠ 0 ∨ u ≠ 0 := by tauto
        obtain ⟨v, w, hvw⟩ := hG t u hne
        have hp : suzukiCell d (suzukiPanelWeyl d * x.val) := by
          right
          refine ⟨⟨C.element false v w, C.element_mem false v w⟩, ?_⟩
          simpa only [htu, mul_assoc] using hvw
        have h := cell_mul_borel d hp hx
        simpa only [mul_assoc, mul_inv_cancel_left] using h
  intro g
  constructor
  · intro hg
    have h := hn (suzukiPanelWeyl d * g) hg
    simpa only [← mul_assoc, suzukiPanelWeyl_mul_self, one_mul] using h
  · exact hn g

private theorem negative_stabilizes (d : LocalBlockInput m) (C : SuzukiCoordinates d) :
    simpleBlock d .suzuki false ≤ leftCellStabilizer (suzukiCell d) := by
  apply le_leftCellStabilizer
  intro x hx g hg
  rcases hg with hg | ⟨u, hu⟩
  · obtain ⟨a, b, rfl⟩ := C.element_cover false hx
    left
    have hconj : (suzukiPanelWeyl d)⁻¹ * C.element false a b * suzukiPanelWeyl d ∈
        rootBorel d := by
      have hc := suzukiPanelWeyl_conj_negative d C a b
      rw [suzukiPanelWeyl_inv] at hc
      simpa only [suzukiPanelWeyl_inv, hc] using suzukiElement_positive_mem_borel d C a b
    convert (rootBorel d).mul_mem hconj hg using 1
    group
  · right
    refine ⟨⟨x, hx⟩ * u, ?_⟩
    simpa only [Subgroup.coe_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left] using hu

private theorem positive_stabilizes (d : LocalBlockInput m) (C : SuzukiCoordinates d)
    (hG : SuzukiGauss d C) :
    simpleBlock d .suzuki true ≤ leftCellStabilizer (suzukiCell d) := by
  intro y hy
  obtain ⟨a, b, rfl⟩ := C.element_cover true hy
  rw [← suzukiPanelWeyl_conj_negative d C a b]
  exact (leftCellStabilizer (suzukiCell d)).mul_mem
    ((leftCellStabilizer (suzukiCell d)).mul_mem (weyl_stabilizes d C hG)
      (negative_stabilizes d C (C.element_mem false a b)))
    ((leftCellStabilizer (suzukiCell d)).inv_mem (weyl_stabilizes d C hG))

/-- Local inversion, Borel generation, and the radical/torus actions give the
cover of every actual coset. Each additional root-calculation premise stays explicit. -/
theorem suzuki_rankOneCover_of_root_geometry (d : LocalBlockInput m) (C : SuzukiCoordinates d)
    (hG : SuzukiGauss d C)
    (hgen : rootBorel d ≤ (simpleBlock d .suzuki true ⊔ suzukiPanelRadical d) ⊔ suzukiPanelTorus d)
    (hRX : simpleBlock d .suzuki false ≤ normalizer (suzukiPanelRadical d))
    (hTX : suzukiPanelTorus d ≤ normalizer (simpleBlock d .suzuki false))
    (hRn : suzukiPanelRadical d ≤ (rootBorel d).comap
      (MulAut.conj (suzukiPanelWeyl d)).toMonoidHom)
    (hTn : suzukiPanelTorus d ≤ (rootBorel d).comap
      (MulAut.conj (suzukiPanelWeyl d)).toMonoidHom) :
    RankOneCover d .suzuki (suzukiPanelRepresentative d C hG) := by
  have hR : suzukiPanelRadical d ≤ leftCellStabilizer (suzukiCell d) := by
    apply le_leftCellStabilizer
    intro r hr g hg
    rcases hg with hg | ⟨u, hu⟩
    · left
      have hn := hRn hr
      change suzukiPanelWeyl d * r * (suzukiPanelWeyl d)⁻¹ ∈ rootBorel d at hn
      have hn' : (suzukiPanelWeyl d)⁻¹ * r * suzukiPanelWeyl d ∈ rootBorel d := by
        simpa only [suzukiPanelWeyl_inv] using hn
      convert (rootBorel d).mul_mem hn' hg using 1
      group
    · right
      refine ⟨u, ?_⟩
      have hconj := (mem_normalizer_iff.mp (hRX ((simpleBlock d .suzuki false).inv_mem u.property)) r).mp hr
      have h := (rootBorel d).mul_mem (suzukiPanelRadical_le_borel d hconj) hu
      convert h using 1
      group
  have hT : suzukiPanelTorus d ≤ leftCellStabilizer (suzukiCell d) := by
    apply le_leftCellStabilizer
    intro t ht g hg
    rcases hg with hg | ⟨u, hu⟩
    · left
      have hn := hTn ht
      change suzukiPanelWeyl d * t * (suzukiPanelWeyl d)⁻¹ ∈ rootBorel d at hn
      have hn' : (suzukiPanelWeyl d)⁻¹ * t * suzukiPanelWeyl d ∈ rootBorel d := by
        simpa only [suzukiPanelWeyl_inv] using hn
      convert (rootBorel d).mul_mem hn' hg using 1
      group
    · right
      refine ⟨⟨t * u.val * t⁻¹, (mem_normalizer_iff.mp (hTX ht) u.val).mp u.property⟩, ?_⟩
      have h := (rootBorel d).mul_mem (suzukiPanelTorus_le_borel d ht) hu
      convert h using 1
      group
  have hP : rootParabolic d .suzuki ≤ leftCellStabilizer (suzukiCell d) :=
    sup_le (hgen.trans (sup_le (sup_le (positive_stabilizes d C hG) hR) hT)) (negative_stabilizes d C)
  intro g
  have h := (hP g.property 1).mpr (cell_of_borel d (one_mem (rootBorel d)))
  change suzukiCell d g.val
  simpa only [mul_one] using h

/-- The middle Weyl representative and the negative Suzuki block cover every
actual Borel coset in the generated Suzuki parabolic. -/
theorem suzuki_rankOneCover (hm : 1 ≤ m) (d : LocalBlockInput m)
    (hT : splitTorus m = diagonalTorus m) (C : SuzukiCoordinates d) :
    RankOneCover d .suzuki (suzukiPanelRepresentative d C (suzukiGauss hm d C hT)) :=
  suzuki_rankOneCover_of_root_geometry d C (suzukiGauss hm d C hT)
    (rootBorel_le_suzukiBlock_sup_radical_sup_torus d hT)
    (suzuki_negative_le_radical_normalizer d C)
    (suzukiPanelTorus_le_negative_normalizer d hT)
    (suzukiPanelRadical_le_borel_comap_weyl d)
    (suzukiPanelTorus_le_borel_comap_weyl d)

/-- Existence of the Suzuki parabolic coset cover from the supplied coordinates,
with all local inversion, generation, and conjugation premises discharged. -/
theorem exists_suzuki_rankOneCover (hm : 1 ≤ m) (d : LocalBlockInput m)
    (hT : splitTorus m = diagonalTorus m) (C : SuzukiCoordinates d) :
    ∃ n : rootParabolic d .suzuki, RankOneCover d .suzuki n :=
  ⟨suzukiPanelRepresentative d C (suzukiGauss hm d C hT), suzuki_rankOneCover hm d hT C⟩

end ReeF4.LocalBlockInput.PairRigidity.LocalIndices
