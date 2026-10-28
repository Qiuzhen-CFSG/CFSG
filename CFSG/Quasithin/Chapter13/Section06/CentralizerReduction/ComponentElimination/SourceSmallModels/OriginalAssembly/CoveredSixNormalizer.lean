module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixNormalizer.Geometry
public import Theory.Representation.HexacodeAction.ProjectiveLineNormalizer

/-!
# The original covered-six normalizer contradiction

The faithful full hexacode action on the original elementary U identifies the
Thompson and Baumann images with one best offender. Its full even fixed-space
stabilizer lifts through the actual plus map into the original Baumann
normalizer, hence into Mᵥ. This makes the literal source commutator [V,Lᵥ],
of order four, an invariant binary two-space. The concrete hexacode projective
line calculation excludes it.

Source: Aschbacher–Smith, 13.6.22, printed p.932. This route uses the full
source action directly and does not reconstruct an exceptional block.
-/

@[expose] public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixNormalizer
open ComponentSelection
variable {G : Type*} [Group G] [Finite G]

private theorem stabilizer_le_normalizer_of_kernel
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (A : Subgroup D)
    (he : A = subspaceKernel ρ (fixedSpace ρ A) ⊤) :
    subspaceStabilizer ρ (fixedSpace ρ A) ≤ normalizer (A : Set D) := by
  apply le_normalizer_iff.mpr
  intro g hg a ha
  apply he.ge
  refine ⟨mem_top _, ?_⟩
  intro u hu
  have hi := (subspaceStabilizer ρ (fixedSpace ρ A)).inv_mem hg
  have hfix := (he.le ha).2 _ ((hi u).mpr hu)
  change ρ (g * a * g⁻¹) u = u
  simp only [map_mul, Module.End.mul_apply]
  rw [hfix]
  simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

/-- The full hexacode action on the actual elementary U rules out the covered-six row.
The even-cover range hypothesis is supplied by the original component marking. -/
theorem contradiction
    {K L T M V U : Subgroup G} (s : A5Module.Marking L V)
    (hL : Tv T (A5Module.markedV s) ≤ normalizer (Lv L (A5Module.markedV s) : Set G))
    (hz : Tv T (A5Module.markedV s) ≤ centralizer ({A5Module.markedZ s} : Set G))
    [IsElementaryAbelian 2 U]
    (d : Model K L T U (A5Module.markedZ s) (A5Module.markedV s) hL hz)
    (hEven : Atlas.Codes.hexSign.ker ≤ d.embedding.range)
    (hK : K ∈ Yz L T (A5Module.markedZ s) (A5Module.markedV s))
    (hn : Tv T (A5Module.markedV s) ≤ normalizer (K : Set G))
    (hLK : Lv L (A5Module.markedV s) ≤ K)
    (hUT : U ≤ Tv T (A5Module.markedV s))
    (hUN : plusActor K L T (A5Module.markedV s) ≤ normalizer (U : Set G))
    (hline : ⁅V, Lv L (A5Module.markedV s)⁆ ≤ U)
    (hk : IsPGroup 2 (plusMk K L T (A5Module.markedZ s) (A5Module.markedV s) hL hz).ker)
    (hc : Gv (A5Module.markedV s) ⊓
      normalizer (ChapterB.baumann (Tv T (A5Module.markedV s)) : Set G) ≤ Mv M (A5Module.markedV s))
    (hML : M ≤ normalizer (L : Set G))
    (hMV : Mv M (A5Module.markedV s) ≤ normalizer (V : Set G)) : False := by
  let z := A5Module.markedZ s
  let v := A5Module.markedV s
  let B := plusImage K L T z v hL hz (elementaryAbelianMaxJ (Tv T v))
  have hB : IsBestOffender d.action B := d.thompson_isBestOffender hK hn hUT hUN
  let Am := B.map d.embedding
  have hAm : IsBestOffender Hexacode.action Am := d.model_best hB
  have hAe : Am ≤ Atlas.Codes.hexSign.ker := Hexacode.bestOffender_le_even Am hAm
  let A := Am.subgroupOf Atlas.Codes.hexSign.ker
  let : IsElementaryAbelian 2 Am := hAm.1.2
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hAe
  have hA : Nat.card A = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAe).toEquiv).trans (Hexacode.bestOffender_card Am hAm)
  have hfixed : fixedSpace Hexacode.evenAction A = fixedSpace Hexacode.action Am := by
    change fixedSpace (Hexacode.action.comp Atlas.Codes.hexSign.ker.subtype) A = _
    rw [fixedSpace_comp_map, map_subgroupOf_eq_of_le hAe]
  have hP : Module.finrank (ZMod 2) (fixedSpace Hexacode.evenAction A) = 4 := by
    rw [hfixed]
    exact Hexacode.bestOffender_fixedSpace_finrank Am hAm
  let Q := NormalElementaryQuotient.subspace U ((⁅V, Lv L v⁆).subgroupOf U)
  let eQ : Q ≃ (⁅V, Lv L v⁆ : Subgroup G) := {
    toFun u := ⟨u.val.toMul.val, u.property⟩
    invFun u := ⟨Additive.ofMul ⟨u.val, hline u.property⟩, u.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hQcard : Nat.card Q = 4 :=
    (Nat.card_congr eQ).trans (AlternatingBranches.CoveredSix.source_commutator_card s)
  have hQ : Module.finrank (ZMod 2) Q = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hQcard
    exact Nat.pow_right_injective (by decide : 1 < 2) hQcard
  have hBA : plusImage K L T z v hL hz (ChapterB.baumann (Tv T v)) = B :=
    d.baumann_eq_thompson hUT (d.bestOffender_kernel hB)
  have hker := AlternatingBranches.CoveredSix.plus_kernel_le_sylow
    K L T z v hK hn hLK hL hz hk
  have hplace := AlternatingBranches.CoveredSix.source_plus_baumann_normalizer_le
    K L T M z v hK.1.1 hL hz hker hc
  have hnorm := AlternatingBranches.CoveredSix.source_commutator_normalized _ hplace hML hMV
  apply Hexacode.ProjectiveLineNormalizer.fourGroup_no_invariant_two A hA hP
    (Q.map d.coordinates.toLinearMap) ((d.coordinates.finrank_map_eq Q).trans hQ)
  apply le_subspaceStabilizer
  intro g hg w hw
  obtain ⟨u, hu, rfl⟩ := hw
  obtain ⟨a, ha⟩ := hEven g.property
  have ham : d.embedding a ∈ subspaceStabilizer Hexacode.action (fixedSpace Hexacode.action Am) := by
    rw [ha]
    intro x
    change Hexacode.action g.val x ∈ fixedSpace Hexacode.action Am ↔ x ∈ fixedSpace Hexacode.action Am
    rw [← hfixed]
    exact hg x
  have han : d.embedding a ∈ normalizer (Am : Set Atlas.Codes.HexAutomorphisms) :=
    stabilizer_le_normalizer_of_kernel Hexacode.action Am
      (Hexacode.bestOffender_eq_kernel Am hAm) ham
  have han' : a ∈ normalizer (B : Set (Gplus K L T z v hL hz)) := by
    have he := Am.comap_normalizer_eq_of_le_range (map_le_range d.embedding B)
    rw [comap_map_eq_self_of_injective d.injective] at he
    exact he.le han
  obtain ⟨b, rfl⟩ := plusMk_surjective K L T z v hL hz a
  have hb : (b : G) ∈ normalizer ((⁅V, Lv L v⁆ : Subgroup G) : Set G) := by
    apply hnorm
    refine mem_map.mpr ⟨b, ?_, rfl⟩
    change plusMk K L T z v hL hz b ∈ normalizer _
    rw [hBA]
    exact han'
  have hqu : d.action (plusMk K L T z v hL hz b) u ∈ Q := by
    change ((d.action (plusMk K L T z v hL hz b) u).toMul : G) ∈ ⁅V, Lv L v⁆
    rw [d.action_conjugation]
    exact (mem_normalizer_iff.mp hb (u.toMul : G)).mp hu
  refine Submodule.mem_map.mpr ⟨d.action (plusMk K L T z v hL hz b) u, hqu, ?_⟩
  change d.coordinates (d.action (plusMk K L T z v hL hz b) u) =
    Hexacode.action g.val (d.coordinates u)
  rw [d.intertwining, ha]

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixNormalizer
