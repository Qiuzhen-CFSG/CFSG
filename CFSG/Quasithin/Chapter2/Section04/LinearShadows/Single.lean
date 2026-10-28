module
public import CFSG.Quasithin.Chapter2.Section04.BlockResidual
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.PResidual.NormalizerCore
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.Splitting
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.Models
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.Transfer

/-!
# Initial and terminal implications for the single linear-block shadow

The common fixed subgroup C_R(B) centralizes L and R and is normalized
by N_S(B). Hence H = L R N_S(B) normalizes it. An element of T − S
normalizing both R and B violates the exact normalizer barrier of 2.4.4
unless C_R(B) = 1. Coprime action now puts R in L whenever [R,B] ≤ L.
Since the single block is the actual two-residual, this absorbs O₂(H)
and identifies O₂(L) with it. Characteristicity then supplies the reverse
normalizer containment to the earlier 2.4.6 input.

The torus geometry remains explicit here. Constructing D and B, the marked
PSL₃(q)/Sp₄(q) parabolic alternatives, and their fusion geometry is still
needed for the complete single-block exclusion. The imported leaves prove
the actual complement step, transfer implication, and q = 4 quaternion
obstruction, with their preceding local premises displayed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 2.4.8, 2.4.11(1), and the end of the single-block branch of 2.4.7,
printed pp.529–539.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

/-- The normalizer barrier kills C_R(B), as in the proof of 2.4.8(5). -/
theorem fixedCentralizer_eq_bot (d : MinimalBlockSetup M)
    (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (R B : Subgroup G)
    (hRS : R ≤ (d.S : Subgroup d.H).map d.H.subtype)
    (hSR : (d.S : Subgroup d.H).map d.H.subtype ≤ normalizer (R : Set G))
    (hgen : d.H = (d.block.map d.H.subtype ⊔ R) ⊔
      ((d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (B : Set G)))
    (hfixed : R ⊓ centralizer (B : Set G) ≤
      centralizer ((d.block.map d.H.subtype ⊔ R : Subgroup G) : Set G))
    {x : G} (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (hxR : x ∈ normalizer (R : Set G)) (hxB : x ∈ normalizer (B : Set G)) :
    R ⊓ centralizer (B : Set G) = ⊥ := by
  let C := R ⊓ centralizer (B : Set G)
  have hCS : C ≤ (d.S : Subgroup d.H).map d.H.subtype := inf_le_left.trans hRS
  have hLC : d.block.map d.H.subtype ⊔ R ≤ normalizer (C : Set G) :=
    (le_centralizer_iff.mp hfixed).trans (centralizer_le_normalizer _)
  have hFC : ((d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (B : Set G)) ≤
      normalizer (C : Set G) :=
    (le_inf (inf_le_left.trans hSR)
      (inf_le_right.trans (normalizer_le_normalizer_centralizer B))).trans
        inf_normalizer_le_normalizer_inf
  have hHC : d.H ≤ normalizer (C : Set G) := by
    rw [hgen]
    exact sup_le hLC hFC
  by_contra hne
  have hbarrier := lemma_2_4_4 d.mem_gammaEvenZero.1 d.full_pair d.S le_rfl T hST C
    hne hCS ((normal_subgroupOf_iff_le_normalizer
      (hCS.trans (map_subtype_le _))).mpr hHC)
  have hxC : x ∈ normalizer (C : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hxR, normalizer_le_normalizer_centralizer B hxB⟩
  exact hxS (hbarrier ▸ (show x ∈ (T : Subgroup G) ⊓ normalizer (C : Set G) from ⟨hxT, hxC⟩))

/-- The fixed-free coprime action supplies R ≤ L and the two-core identity
used in 2.4.8(2), with the literal ambient block map. -/
theorem core_absorption_of_torus_geometry (d : MinimalBlockSetup M)
    (hsingle : d.L0 = d.block) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype ≤ (T : Subgroup G))
    (R B : Subgroup G)
    (hRS : R ≤ (d.S : Subgroup d.H).map d.H.subtype)
    (hSR : (d.S : Subgroup d.H).map d.H.subtype ≤ normalizer (R : Set G))
    (hgen : d.H = (d.block.map d.H.subtype ⊔ R) ⊔
      ((d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (B : Set G)))
    (hfixed : R ⊓ centralizer (B : Set G) ≤
      centralizer ((d.block.map d.H.subtype ⊔ R : Subgroup G) : Set G))
    (hBR : B ≤ normalizer (R : Set G))
    (hcop : Nat.Coprime (Nat.card B) (Nat.card R))
    (hcomm : ⁅R, B⁆ ≤ d.block.map d.H.subtype)
    (hQR : twoCore d.H ≤ R)
    {x : G} (hxT : x ∈ T) (hxS : x ∉ (d.S : Subgroup d.H).map d.H.subtype)
    (hxR : x ∈ normalizer (R : Set G)) (hxB : x ∈ normalizer (B : Set G)) :
    R ≤ d.block.map d.H.subtype ∧
      twoCore (d.block.map d.H.subtype) = twoCore d.H := by
  have hfixed0 := fixedCentralizer_eq_bot d T hST R B hRS hSR hgen hfixed hxT hxS hxR hxB
  have hp : IsPGroup 2 R := T.isPGroup'.to_le (hRS.trans hST)
  have hdecomp := eq_commutator_sup_centralizer_of_solvable_coprime R B hBR
    (@IsNilpotent.to_isSolvable R _ hp.isNilpotent) hcop
  rw [hfixed0, sup_bot_eq] at hdecomp
  have hRL : R ≤ d.block.map d.H.subtype := hdecomp ▸ hcomm
  refine ⟨hRL, ?_⟩
  have he : d.block.map d.H.subtype = (pResidual 2 d.H).map d.H.subtype := by
    rw [← d.L0_eq_residual, hsingle]
  change (d.block.map d.H.subtype).pCoreIn 2 = d.H.pCoreIn 2
  rw [he]
  apply pCoreIn_embedded_pResidual_eq_of_core_le
  exact he ▸ hQR.trans hRL

omit [Finite G] in
/-- Source 2.4.11(1), once absorption is proved and the preceding 2.4.6
normalization input is supplied. -/
theorem coreNormalizer_eq_blockNormalizer (d : MinimalBlockSetup M)
    (hcore : twoCore (d.block.map d.H.subtype) = twoCore d.H)
    (hn : normalizer (twoCore d.H : Set G) ≤
      normalizer (d.block.map d.H.subtype : Set G)) :
    normalizer (twoCore d.H : Set G) = normalizer (d.block.map d.H.subtype : Set G) := by
  apply le_antisymm hn
  have hchar := normalizer_le_normalizer_characteristic_image
    (d.block.map d.H.subtype) (pCore 2 (d.block.map d.H.subtype))
  change normalizer (d.block.map d.H.subtype : Set G) ≤
    normalizer (twoCore (d.block.map d.H.subtype) : Set G) at hchar
  rwa [hcore] at hchar
end CFSG.Quasithin.Chapter2.LinearShadows.Single
