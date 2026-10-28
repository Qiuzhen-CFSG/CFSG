module

public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.RootBlocks
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.SuzukiCore.LeviProjection
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylGeometry.Orbits
-- Internal refinement of the checked orbit table: retain the Suzuki side in
-- the conclusion. No private root-table data enters the exported statements.
import all Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.WeylGeometry.Orbits

import all Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.FixedRootFactorization.RootAlignment

/-!
# The four Ree B₂ blocks inside genuine Suzuki Levi subgroups

The fixed middle-node Levi is identified with the literal Suzuki matrix
carrier. Its inclusion into the Ree group and its four Weyl conjugates
contain the complete B₂ blocks. A lift of that prescribed embedding therefore
restricts to ordinary sections of all four requested root subgroups.

Source: GLS3 §§2.3–2.4, Table 2.4 and 2.4.5(d). The covering application is
Aschbacher–Smith I.1.1–4, printed pp.407–408.
-/

@[expose] public noncomputable section
namespace ReeF4.CentralCovers.TwoPrimary.QuartetSplitting
open Subgroup ElementaryTwoBound
open NormalizedRootCentralizers.CenterExponent
variable {m : ℕ}
open BenderSuzuki.MatrixGroups
open LargeLocalSeeds
open LocalBlockInput.PairRigidity
open LocalBlockInput.PairRigidity.FixedCollection
open LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration

private theorem layout_blocks : positiveRootWordLayout.blocks =
    Parabolics.RadicalCoordinates.FixedCoordinates.rootBlocks .positive := rfl

attribute [local irreducible] positiveRootWordLayout

/-- The literal fixed middle-node Suzuki Levi embedding, through its proved
four-dimensional matrix comparison. -/
def suzukiEmbedding (m : ℕ) : SuzukiMatrixGroup m →* Model m :=
  (canonicalLocalBlockInput m).modelEquiv.toMonoidHom.comp
    ((fixedLevi (canonicalLocalBlockInput m) .suzuki).subtype.comp
      (SuzukiLeviProjection.fixedLeviEquivSuzuki
        (canonicalLocalBlockInput m)).symm.toMonoidHom)

theorem suzukiEmbedding_injective (m : ℕ) : Function.Injective (suzukiEmbedding m) :=
  (canonicalLocalBlockInput m).modelEquiv.injective.comp
    (Subtype.val_injective.comp
      (SuzukiLeviProjection.fixedLeviEquivSuzuki (canonicalLocalBlockInput m)).symm.injective)

private theorem quartet_split_orbit (d : LocalBlockInput m) (j : Fin 4) :
    ∃ n : d.fixedGroup, splitPositiveBlock m (.inr j) ≤
      (splitSimpleBlock m .suzuki true).map (MulAut.conj n.val).toMonoidHom := by
  let n := ((orbitSides (.inr j)).map (relativeWeyl d)).prod
  refine ⟨n, (closure_le _).mpr ?_⟩
  rintro x ⟨r, t, ⟨k, rfl⟩, rfl⟩
  refine ⟨rootGeneratorInGroup m
    ((Parabolics.RadicalCoordinates.FixedCoordinates.rootBlocks .positive).roots
      (.inr ((0 : Fin 4), k))).val t, ?_, ?_⟩
  · exact subset_closure ⟨_, t, (positiveBlockRoots_simple_iff .suzuki _).mp ⟨k, rfl⟩, rfl⟩
  · change n.val * _ * n.val⁻¹ = _
    rw [show n.val = Parabolics.Binary.FixedGeometry.simpleWord m
      (orbitWord (.inr j)) from sidesWord_val d _, simpleWord_conj_root, quartet_orbit]

private theorem main_mem_splitPositiveBlock (m : ℕ) (j : Fin 4) (t : CoefficientField m) :
    rootWord m (rootIndex (.inr j)) t ∈ splitPositiveBlock m (.inr j) := by
  have hroot (k : Fin 4) (a : CoefficientField m) :
      rootGeneratorInGroup m
        ((Parabolics.RadicalCoordinates.FixedCoordinates.rootBlocks .positive).roots
          (.inr (j, k))).val a ∈ splitPositiveBlock m (.inr j) :=
    subset_closure ⟨_, a, ⟨k, rfl⟩, rfl⟩
  change rootWord m (positiveRootWordLayout.quartetIndex j) t ∈ _
  rw [rootWord, if_pos (positiveRootWordLayout.quartet_even j)]
  rw [← positiveRootWordLayout.quartet_long j, ← positiveRootWordLayout.quartet_short j,
    ← positiveRootWordLayout.quartet_mixed j]
  rw [layout_blocks]
  exact mul_mem (mul_mem (hroot 0 _) (hroot 1 _)) (hroot 2 _)

/-- Each complete nonabelian block is contained in an actual conjugate of
the prescribed Suzuki embedding. The root order is `[0,4,6,2]`. -/
theorem quartet_le_conjugate_suzuki (m : ℕ) (j : Fin 4) :
    ∃ n : Model m, X m (rootIndex (.inr j)) ≤
      (suzukiEmbedding m).range.map (MulAut.conj n).toMonoidHom := by
  let d := canonicalLocalBlockInput m
  obtain ⟨n, hn⟩ := quartet_split_orbit d j
  refine ⟨d.modelEquiv n, (closure_le _).mpr ?_⟩
  rintro _ ⟨t, rfl⟩
  let x := d.modelEquiv.symm (mainElement m (rootIndex (.inr j)) t)
  have hx : x.val ∈ splitPositiveBlock m (.inr j) := by
    rw [Parabolics.modelEquiv_symm_coe]
    exact main_mem_splitPositiveBlock m j t
  obtain ⟨y, hy, he⟩ := hn hx
  let z : d.fixedGroup := n⁻¹ * x * n
  have hz : z.val = y := by
    change n.val⁻¹ * x.val * n.val = y
    rw [← he]
    change n.val⁻¹ * (n.val * y * n.val⁻¹) * n.val = y
    group
  have hzL : z ∈ fixedLevi d .suzuki := by
    change z.val ∈ splitLevi m .suzuki
    rw [hz]
    exact mem_sup_left hy
  refine ⟨d.modelEquiv z, ?_, ?_⟩
  · refine ⟨SuzukiLeviProjection.fixedLeviEquivSuzuki d ⟨z,hzL⟩, ?_⟩
    change d.modelEquiv
      ((SuzukiLeviProjection.fixedLeviEquivSuzuki d).symm
        (SuzukiLeviProjection.fixedLeviEquivSuzuki d ⟨z,hzL⟩)).val = _
    rw [MulEquiv.symm_apply_apply]
  · change d.modelEquiv n * d.modelEquiv z * (d.modelEquiv n)⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul]
    have heq : n * z * n⁻¹ = x := by dsimp [z]; group
    rw [heq]
    exact d.modelEquiv.apply_symm_apply _

/-- A prescribed Suzuki lift supplies the four literal root-subgroup sections.
Conjugating elements are lifted through the original surjection. -/
theorem quartet_sections_of_suzuki_lift (m : ℕ)
    {E : Type*} [Group E] (f : E →* Model m) (hf : Function.Surjective f)
    (s : SuzukiMatrixGroup m →* E) (hs : f.comp s = suzukiEmbedding m) :
    ∀ j : Fin 4, ∃ l : X m (rootIndex (.inr j)) →* E,
      f.comp l = (X m (rootIndex (.inr j))).subtype := by
  intro j
  obtain ⟨n, hn⟩ := quartet_le_conjugate_suzuki m j
  obtain ⟨v, hv⟩ := hf n
  let e := MonoidHom.ofInjective (suzukiEmbedding_injective m)
  let H := X m (rootIndex (.inr j))
  let r : H →* (suzukiEmbedding m).range :=
    ((MulAut.conj n⁻¹).toMonoidHom.comp H.subtype).codRestrict _ (by
      intro x
      obtain ⟨y, hy, he⟩ := hn x.property
      change n⁻¹ * x.val * (n⁻¹)⁻¹ ∈ (suzukiEmbedding m).range
      rw [← he]
      have heq : n⁻¹ * (MulAut.conj n y) * (n⁻¹)⁻¹ = y := by
        change n⁻¹ * (n * y * n⁻¹) * (n⁻¹)⁻¹ = y
        group
      simp only [MulEquiv.coe_toMonoidHom, heq]
      exact hy)
  refine ⟨(MulAut.conj v).toMonoidHom.comp (s.comp (e.symm.toMonoidHom.comp r)), ?_⟩
  apply MonoidHom.ext
  intro x
  change f (v * s (e.symm (r x)) * v⁻¹) = x.val
  rw [map_mul, map_mul, map_inv, hv]
  have hp : f (s (e.symm (r x))) = (r x).val :=
    (DFunLike.congr_fun hs _).trans (congrArg Subtype.val (e.apply_symm_apply (r x)))
  rw [hp]
  change n * (n⁻¹ * x.val * (n⁻¹)⁻¹) * n⁻¹ = x.val
  group

end ReeF4.CentralCovers.TwoPrimary.QuartetSplitting
