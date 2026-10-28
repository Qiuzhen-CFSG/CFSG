module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical.TensorFacts.Coordinates
import Mathlib.Tactic.FinCases

/-!
# Fixed spaces and displacement separation for the point radical

A shear with coefficients (a,b) moves a three-row tensor by the seed vector
whose first row is a times the second row plus b times the third. Each
nonidentity shear therefore has the whole two-dimensional seed as its image.
The full radical fixes exactly the seed; its nontrivial proper subgroups have
order two and fixed codimension two. On each such fixed space another shear
still has the full seed as its displacement image, excluding every line.

This is the concrete representation calculation required by the critical-pair
argument for Aschbacher–Smith 13.8.21(1), printed p.957. In particular it does
not infer cyclicity from quadraticity of the radical.
-/

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

@[expose] public section
open Matrix Representation Representation.BinaryOffender TensorProduct
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical.TensorFacts

private abbrev shear (c : ZMod 2 × ZMod 2) : TensorGroup :=
  componentInclusion (pointShear (Multiplicative.ofAdd c))

private lemma shear_injective : Function.Injective shear := by
  intro c d h
  exact pointShear_injective (congrArg Prod.fst h)

private lemma shear_zero : shear (0, 0) = 1 := by
  change componentInclusion (pointShear 1) = 1
  simp

private lemma mem_radical (g : TensorGroup) : g ∈ tensorPointRadical ↔ ∃ c, shear c = g := by
  constructor
  · rintro ⟨a, ⟨c, rfl⟩, rfl⟩
    exact ⟨c.toAdd, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨_, ⟨Multiplicative.ofAdd c, rfl⟩, rfl⟩

private lemma s3Action_one (x : Fin 2 → ZMod 2) : s3Action 1 x = x := by
  ext k; fin_cases k <;> rfl

private lemma coordinates_shear (c : ZMod 2 × ZMod 2) (z : TensorSpace) :
    coordinates (naturalTensor (shear c) z) =
      ![coordinates z 0 + c.1 • coordinates z 1 + c.2 • coordinates z 2,
        coordinates z 1, coordinates z 2] := by
  rw [coordinates_action]
  change matrixAction !![1,c.1,c.2;0,1,0;0,0,1] 1 (coordinates z) = _
  ext i k
  fin_cases i <;>
    simp [matrixAction, shear, componentInclusion, pointShear, s3Action_one,
      Fin.sum_univ_three]

private noncomputable def seed : (Fin 2 → ZMod 2) →ₗ[ZMod 2] TensorSpace :=
  coordinates.symm.toLinearMap.comp
    ({
      toFun := fun x => ![x, 0, 0]
      map_add' := by intro x y; ext i k; fin_cases i <;> rfl
      map_smul' := by intro c x; ext i k; fin_cases i <;> rfl } :
      (Fin 2 → ZMod 2) →ₗ[ZMod 2] Coordinates)

private lemma coordinates_seed (x : Fin 2 → ZMod 2) : coordinates (seed x) = ![x,0,0] :=
  coordinates.apply_symm_apply _

private lemma seed_injective : Function.Injective seed := by
  intro x y h
  have hh := congrArg (fun z => coordinates z 0) h
  simpa only [coordinates_seed, Matrix.cons_val_zero] using hh

private lemma finrank_seed : Module.finrank (ZMod 2) (LinearMap.range seed) = 2 := by
  rw [LinearMap.finrank_range_of_inj seed_injective]
  simp

private lemma shear_displacement (c : ZMod 2 × ZMod 2) (z : TensorSpace) :
    naturalTensor (shear c) z - z =
      seed (c.1 • coordinates z 1 + c.2 • coordinates z 2) := by
  apply coordinates.injective
  rw [map_sub, coordinates_shear, coordinates_seed]
  ext i k
  fin_cases i <;> simp [add_sub_cancel_left, add_assoc]

private lemma nonzero_pair_dual (c : ZMod 2 × ZMod 2) (hc : c ≠ 0) :
    ∃ d : ZMod 2 × ZMod 2, c.1*d.1 + c.2*d.2 = 1 := by
  revert c
  decide

private lemma shear_range (c : ZMod 2 × ZMod 2) (hc : c ≠ 0) :
    LinearMap.range (naturalTensor (shear c) - 1) = LinearMap.range seed := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact ⟨_, (shear_displacement c z).symm⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨d, hd⟩ := nonzero_pair_dual c hc
    refine ⟨coordinates.symm ![0,d.1 • x,d.2 • x], ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    rw [shear_displacement, coordinates.apply_symm_apply]
    congr 1
    change c.1 • (d.1 • x) + c.2 • (d.2 • x) = x
    rw [smul_smul, smul_smul, ← add_smul, hd, one_smul]

private lemma radical_fixedSpace : fixedSpace naturalTensor tensorPointRadical = LinearMap.range seed := by
  apply le_antisymm
  · intro z hz
    have hz' : ∀ c : ZMod 2 × ZMod 2, naturalTensor (shear c) z = z :=
      fun c => hz ⟨shear c, (mem_radical _).mpr ⟨c,rfl⟩⟩
    have h1 := congrArg (fun z => coordinates z 0) (hz' (1,0))
    have h2 := congrArg (fun z => coordinates z 0) (hz' (0,1))
    rw [coordinates_shear] at h1 h2
    have hx1 : coordinates z 1 = 0 := by simpa using h1
    have hx2 : coordinates z 2 = 0 := by simpa using h2
    refine ⟨coordinates z 0, coordinates.injective ?_⟩
    rw [coordinates_seed]
    ext i k
    fin_cases i <;> simp [hx1, hx2]
  · rintro _ ⟨x,rfl⟩ ⟨g,hg⟩
    obtain ⟨c,rfl⟩ := (mem_radical _).mp hg
    change naturalTensor (shear c) (seed x) = seed x
    apply sub_eq_zero.mp
    rw [shear_displacement, coordinates_seed]
    simp

/-- The full rank-two point radical has fixed codimension four. -/
theorem fixedCodim_radical : fixedCodim naturalTensor tensorPointRadical = 4 := by
  have h := fixedCodim_add_finrank naturalTensor tensorPointRadical
  rw [radical_fixedSpace, finrank_seed, finrank_tensorSpace] at h
  omega


theorem card_tensorPointRadical : Nat.card tensorPointRadical = 4 := by
  rw [tensorPointRadical, Subgroup.card_map_of_injective
    (show Function.Injective componentInclusion from fun _ _ h => congrArg Prod.fst h),
    card_pointRadical]

/-- Every nontrivial proper subgroup of the point radical has order two. -/
theorem card_proper_radical (A : Subgroup TensorGroup) (hA : A < tensorPointRadical)
    (hA0 : A ≠ ⊥) : Nat.card A = 2 := by
  have hle := Subgroup.card_le_of_le hA.le
  rw [card_tensorPointRadical] at hle
  have hlo := A.one_lt_card_iff_ne_bot.mpr hA0
  have hne : Nat.card A ≠ 4 := by
    intro h
    exact hA.ne (Subgroup.eq_of_le_of_card_ge hA.le (by rw [card_tensorPointRadical, h]))
  have hdiv := Subgroup.card_dvd_of_le hA.le
  rw [card_tensorPointRadical] at hdiv
  have hn : Nat.card A = 2 ∨ Nat.card A = 3 := by omega
  rcases hn with h | h
  · exact h
  · norm_num [h] at hdiv

private lemma proper_radical_generator (A : Subgroup TensorGroup) (hA : A < tensorPointRadical)
    (hA0 : A ≠ ⊥) : ∃ c : ZMod 2 × ZMod 2, c ≠ 0 ∧ A = Subgroup.zpowers (shear c) := by
  have hex : ∃ g ∈ A, g ≠ 1 := by
    by_contra! h
    exact hA0 (bot_unique (fun g hg => Subgroup.mem_bot.mpr (h g hg)))
  obtain ⟨g, hg, hg1⟩ := hex
  obtain ⟨c, rfl⟩ := (mem_radical _).mp (hA.le hg)
  have hc : c ≠ 0 := by intro h; exact hg1 (h ▸ shear_zero)
  refine ⟨c, hc, ?_⟩
  have hle : Subgroup.zpowers (shear c) ≤ A := Subgroup.zpowers_le.mpr hg
  have hcyc : Subgroup.zpowers (shear c) ≠ ⊥ := by
    intro h
    have := Subgroup.mem_zpowers (shear c)
    rw [h, Subgroup.mem_bot] at this
    exact hg1 this
  have hcard := (Subgroup.zpowers (shear c)).one_lt_card_iff_ne_bot.mpr hcyc
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [card_proper_radical A hA hA0]; omega)).symm

/-- Every nontrivial proper subgroup of the point radical has fixed codimension two. -/
theorem fixedCodim_proper_radical (A : Subgroup TensorGroup) (hA : A < tensorPointRadical)
    (hA0 : A ≠ ⊥) : fixedCodim naturalTensor A = 2 := by
  obtain ⟨c,hc,rfl⟩ := proper_radical_generator A hA hA0
  rw [fixedCodim_zpowers_eq_range, shear_range c hc, finrank_seed]

/-- A nonidentity point-radical element has a two-dimensional displacement image. -/
theorem finrank_radical_displacement (g : TensorGroup) (hg : g ∈ tensorPointRadical)
    (hg1 : g ≠ 1) : Module.finrank (ZMod 2) (LinearMap.range (naturalTensor g - 1)) = 2 := by
  obtain ⟨c,rfl⟩ := (mem_radical _).mp hg
  have hc : c ≠ 0 := by intro h; exact hg1 (h ▸ shear_zero)
  rw [shear_range c hc, finrank_seed]

private lemma seed_not_le_line (D : Submodule (ZMod 2) TensorSpace)
    (hD : Module.finrank (ZMod 2) D ≤ 1) : ∃ x, seed x ∉ D := by
  by_contra! h
  have hs : LinearMap.range seed ≤ D := by rintro _ ⟨x,rfl⟩; exact h x
  have := Submodule.finrank_mono hs
  rw [finrank_seed] at this
  omega

private lemma separation_coefficients (c : ZMod 2 × ZMod 2) (hc : c ≠ 0) :
    ∃ d : ZMod 2 × ZMod 2,
      c.1*c.2 + c.2*c.1 = 0 ∧ d.1*c.2 + d.2*c.1 = 1 := by
  revert c
  decide

/-- On the fixed space of a nontrivial proper radical subgroup, radical
displacements cannot all lie in any binary subspace of dimension at most one.
This is the obstruction to the line supplied by `exists_section_displacement_line`. -/
theorem exists_radical_displacement_not_mem (A : Subgroup TensorGroup)
    (hA : A < tensorPointRadical) (hA0 : A ≠ ⊥)
    (D : Submodule (ZMod 2) TensorSpace) (hD : Module.finrank (ZMod 2) D ≤ 1) :
    ∃ b ∈ tensorPointRadical, ∃ w ∈ fixedSpace naturalTensor A,
      naturalTensor b w - w ∉ D := by
  obtain ⟨c,hc,rfl⟩ := proper_radical_generator A hA hA0
  obtain ⟨x,hx⟩ := seed_not_le_line D hD
  obtain ⟨d,hzero,hone⟩ := separation_coefficients c hc
  let w := coordinates.symm ![0,c.2 • x,c.1 • x]
  have hdisp (e : ZMod 2 × ZMod 2) :
      naturalTensor (shear e) w - w = seed ((e.1*c.2 + e.2*c.1) • x) := by
    rw [shear_displacement]
    dsimp only [w]
    rw [coordinates.apply_symm_apply]
    change seed (e.1 • (c.2 • x) + e.2 • (c.1 • x)) = _
    rw [smul_smul, smul_smul, ← add_smul]
  refine ⟨shear d, (mem_radical _).mpr ⟨d,rfl⟩, w, ?_, ?_⟩
  · rw [mem_fixedSpace_zpowers, ← sub_eq_zero, hdisp c, hzero]
    simp
  · rw [hdisp d, hone, one_smul]
    exact hx

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.MarkedCritical.TensorFacts
