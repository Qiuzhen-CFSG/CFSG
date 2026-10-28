module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.WordCertificate
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.MarkedParabolics
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.LongRoot
public import Theory.SpecificGroups.Tits.InvolutionRootGeometry.ParabolicContainment.ShortRoot
public import Theory.SpecificGroups.Tits.OuterOddSubgroups.OverlapCentralizers.FirstCover

/-!
# Marked long-root words in the binary Ree group

The alternating Weyl word r₈r₁r₈ carries the Sylow-central r₅ to s₁.
Thus the fourth-point involution inverts the literal first rotation s₁r₁.
For the six-step apartment segment centered at the linear vertex, the two
endpoint words are (r₁r₈)r₅(r₁r₈)⁻¹ and s₁. Their product has order four,
and their commutator is s₇s₄s₇⁻¹, an actual marked short-root involution.

The identities are checked in the faithful Atlas action and transported by
the fixed embedding into the full Ree matrix group. These are coordinate
identities; the graph distances and full short-root centralizer are separate
geometric assertions. Source: Aschbacher--Smith F.4.27(4) and the proof of
J.4.7, printed pp.288 and 444; Parrott (1972), §5, p.683.
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics.FullRee.LongRootPaths
open Subgroup
open OuterOddSubgroups.OverlapCentralizers

local notation "a" => Atlas.a
local notation "w" => Atlas.w
local notation "leftWord" => Atlas.leftWord
open Tits.ExceptionalParabolics.FullRee.LongRootPaths.Atlas
  (fourth_word short_word product_four product_square_ne)

private theorem gen_mem_sylow (i : ParrottGenerator) (h1 : i ≠ .r1) (h8 : i ≠ .r8) :
    a i ∈ ExceptionalParabolics.S := by
  rw [ExceptionalParabolics.S, atlas1600SylowTwoSubgroup_eq]
  apply Subgroup.subset_closure
  cases i <;> simp_all [Atlas.a]

/-- The specified central long-root involution, with its actual matrix marking. -/
def z : ReeF4.Model 0 := atlasEmbedding atlas1600R5

/-- The involution at the fourth point in alternating Weyl coordinates. -/
def u : ReeF4.Model 0 := atlasEmbedding (a .s1)

/-- The actual alternating Weyl word, without an arbitrary conjugating choice. -/
def fourthWord : ReeF4.Model 0 := atlasEmbedding w

/-- The left endpoint of the centered six-step segment. -/
def leftSix : ReeF4.Model 0 := atlasEmbedding leftWord

/-- The specified element of order five in the first parabolic. -/
def rotation : ReeF4.Model 0 := atlasEmbedding firstRotation

/-- The short-root commutator of the two marked long-root endpoints. -/
def shortCommutator : ReeF4.Model 0 :=
  atlasEmbedding (a .s7) * atlasEmbedding (a .s4) * (atlasEmbedding (a .s7))⁻¹

theorem fourthWord_conjugates : fourthWord * z * fourthWord⁻¹ = u := by
  simpa only [fourthWord, z, u, map_mul, map_inv] using congrArg atlasEmbedding fourth_word

theorem u_eq_longRoot : u = (InvolutionRootGeometry.longRoot : ReeF4.Model 0) := by
  rw [u, Atlas.a, atlasEmbedding_generator]
  exact (InvolutionRootGeometry.embedding_generator .s1).symm

theorem z_isLongRoot : IsConj (InvolutionRootGeometry.longRoot : ReeF4.Model 0) z := by
  rw [← u_eq_longRoot]
  exact (isConj_iff.mpr ⟨fourthWord, fourthWord_conjugates⟩).symm

theorem u_mem_borel : u ∈ B := by
  rw [borel_eq_sylow]
  exact atlas_sylow_map_le (mem_map_of_mem _ (gen_mem_sylow .s1 (by decide) (by decide)))

theorem rotation_order : orderOf rotation = 5 :=
  (orderOf_injective atlasEmbedding atlasEmbedding_injective firstRotation).trans firstRotation_order

theorem rotation_mem_first : rotation ∈ first := by
  apply atlas_first_map_le
  apply mem_map_of_mem
  exact ExceptionalParabolics.first.mul_mem
    (ExceptionalParabolics.sylow_le_first (gen_mem_sylow .s1 (by decide) (by decide)))
    ExceptionalParabolics.reflection_mem_first

theorem u_inverts_rotation : u * rotation * u⁻¹ = rotation⁻¹ := by
  have h1 : a .s1 ^ 2 = 1 := by
    simpa only [Atlas.a, parrottRelator, map_pow, FreeGroup.lift_apply_of] using
      atlas1600ParrottAssignment_relations .i_s1
  have h8 : a .r1 ^ 2 = 1 := by
    simpa only [Atlas.a, parrottRelator, map_pow, FreeGroup.lift_apply_of] using
      atlas1600ParrottAssignment_relations .i_r1
  have h : a .s1 * firstRotation * (a .s1)⁻¹ = firstRotation⁻¹ := by
    have hi1 : (a .s1)⁻¹ = a .s1 := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using h1)
    have hi8 : (a .r1)⁻¹ = a .r1 := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using h8)
    change a .s1 * (a .s1 * a .r1) * (a .s1)⁻¹ = (a .s1 * a .r1)⁻¹
    rw [mul_inv_rev, hi8, hi1, ← mul_assoc, ← pow_two, h1, one_mul]
  simpa only [u, rotation, map_mul, map_inv] using congrArg atlasEmbedding h

theorem leftSix_mul_u_order : orderOf (leftSix * u) = 4 := by
  have ho : orderOf (leftWord * a .s1) = 4 :=
    orderOf_eq_prime_pow (p := 2) (n := 1) product_square_ne product_four
  simpa only [leftSix, u, map_mul] using
    (orderOf_injective atlasEmbedding atlasEmbedding_injective (leftWord * a .s1)).trans ho

theorem commutator_eq_short : leftSix * u * leftSix⁻¹ * u⁻¹ = shortCommutator := by
  simpa only [leftSix, u, shortCommutator, map_mul, map_inv] using
    congrArg atlasEmbedding short_word

theorem commutator_isShortRoot :
    IsConj (InvolutionRootGeometry.shortRoot : ReeF4.Model 0) shortCommutator := by
  apply isConj_iff.mpr
  refine ⟨atlasEmbedding (a .s7), ?_⟩
  have h : (InvolutionRootGeometry.shortRoot : ReeF4.Model 0) = atlasEmbedding (a .s4) := by
    rw [Atlas.a, atlasEmbedding_generator]
    exact InvolutionRootGeometry.embedding_generator .s4
  rw [h]
  rfl

theorem shortCommutator_mem_second : shortCommutator ∈ second := by
  have hh (i : ParrottGenerator) (h1 : i ≠ .r1) (h8 : i ≠ .r8) :
      atlasEmbedding (a i) ∈ second :=
    sylow_le_second (atlas_sylow_map_le (mem_map_of_mem _ (gen_mem_sylow i h1 h8)))
  exact second.mul_mem (second.mul_mem (hh .s7 (by decide) (by decide))
    (hh .s4 (by decide) (by decide))) (second.inv_mem (hh .s7 (by decide) (by decide)))

end Tits.ExceptionalParabolics.FullRee.LongRootPaths
