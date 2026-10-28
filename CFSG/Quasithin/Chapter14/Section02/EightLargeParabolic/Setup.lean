module

public import CFSG.Quasithin.Chapter14.Section02.NormalF11
public import CFSG.Quasithin.ChapterF.Section01.SourceIncidence
public import CFSG.Quasithin.ChapterF.Section01.SourceFaithfulTriple
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.Amalgam.RankTwo
public import Theory.SpecificGroups.PSL2.AutomorphismModel

/-!
# The literal normal L₂(8) source amalgam

Specialize the normal F.1.1 construction to R = O²(H), transporting the
given intrinsic quotient equivalence to its embedded copy. The first
parabolic is H; the second is YT(M ∩ R), and their whole overlap is H ∩ M.
In particular the odd Borel factor is retained in the second parabolic.

This supplies the exact inclusion amalgam for the eight-field branch of
14.2.16. It does not recognize that amalgam or its ambient completion.
Source: Aschbacher--Smith 14.2.8(1), 14.2.11--16, pp.983--986.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The actual two-residual embedded in the original ambient group. -/
def residual (H : Subgroup G) : Subgroup G := (pResidual 2 H).map H.subtype

/-- The source S₂, with the intersection T ∩ R retained literally. -/
def secondSylow (T : Sylow 2 G) (M Mc H : Subgroup G) : Subgroup G :=
  (sourceResidual M Mc).pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ residual H)

/-- The two local factors to which the genuine F.1.1 theorem applies. -/
def locals (T : Sylow 2 G) (M Mc H : Subgroup G) : Fin 2 → Subgroup G :=
  ![residual H, sourceResidual M Mc ⊔ secondSylow T M Mc H]

/-- The second parabolic includes the odd part of the first Borel. -/
def secondParabolic (T : Sylow 2 G) (M Mc H : Subgroup G) : Subgroup G :=
  sourceResidual M Mc ⊔ (T : Subgroup G) ⊔ (M ⊓ residual H)

/-- The literal inclusion amalgam, with the entire intersection as middle group. -/
def amalgam (T : Sylow 2 G) (M Mc H : Subgroup G) :=
  RankTwoAmalgam.ofSubgroups H (H ⊓ secondParabolic T M Mc H)
    (secondParabolic T M Mc H) inf_le_left inf_le_right

private theorem residual_sup_sylow (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) : residual H ⊔ (T : Subgroup G) = H := by
  have h := congrArg (Subgroup.map H.subtype)
    (pResidual_sup_sylow_eq_top (T.subtype hTH))
  simpa only [residual, Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH,
    ← MonoidHom.range_eq_map, range_subtype] using h

variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)

include hG hempty hM hu hmany hcard e hH eR

/-- All genuine F.1.1 clauses and both Borel identities on the literal residual.
No containment of T in R, generation-parameter bound, or recognition is assumed. -/
theorem source_hypothesis :
    ChapterF.Source.HypothesisF11 (locals T M Mc H) (T : Subgroup G) ∧
      secondSylow T M Mc H ≤ (T : Subgroup G) ∧
      sourceResidual M Mc = ⁅sourceResidual M Mc, secondSylow T M Mc H⁆ ∧
      ChapterF.Source.borel (residual H) (T : Subgroup G) = M ⊓ residual H ∧
      ChapterF.Source.borel (sourceResidual M Mc ⊔ secondSylow T M Mc H)
        (T : Subgroup G) = secondSylow T M Mc H := by
  have hq : ChapterF.Source.IsRankOneModel
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) :=
    .linear 3 (by decide) ⟨GaloisField 2 3, inferInstance, inferInstance,
      GaloisField.card 2 3 (by decide), ⟨eR⟩⟩
  have hgen := pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2)
  obtain ⟨hF, hS, hmove, hB, hB₂⟩ := source_normal_bender_hypothesis_F_1_1
    hG T hempty hM hu hmany hcard e H hH (pResidual 2 H) hgen rfl hq
  obtain ⟨_, _, hS₂, _⟩ := source_normal_amalgam_core
    hG T hempty hM hu hmany hcard e H hH (pResidual 2 H) hgen
  rw [hS] at hF hS₂ hB hB₂
  exact ⟨hF, hS₂, hmove, hB, hB₂⟩

/-- Identify both parabolics and the full intersection, preserving the odd Borel.
These equations connect the F.1.1 construction to `amalgam`. -/
theorem source_parabolics :
    ChapterF.Source.parabolic (locals T M Mc H) (T : Subgroup G) 0 = H ∧
      ChapterF.Source.parabolic (locals T M Mc H) (T : Subgroup G) 1 =
        secondParabolic T M Mc H ∧
      ChapterF.Source.commonBorel (locals T M Mc H) (T : Subgroup G) = H ⊓ M ∧
      H ⊓ secondParabolic T M Mc H = H ⊓ M ∧
      secondParabolic T M Mc H ≤ M := by
  obtain ⟨hF, hS₂, _, hB, hB₂⟩ := source_hypothesis
    hG T hempty hM hu hmany hcard e H hH eR
  have hgen := residual_sup_sylow T H hH.1.1.2
  have hzero : ChapterF.Source.parabolic (locals T M Mc H) (T : Subgroup G) 0 = H := by
    change residual H ⊔ (T : Subgroup G) ⊔
      ChapterF.Source.borel (sourceResidual M Mc ⊔ secondSylow T M Mc H)
        (T : Subgroup G) = H
    rw [hB₂, hgen, sup_eq_left.mpr (hS₂.trans hH.1.1.2)]
  have hone : ChapterF.Source.parabolic (locals T M Mc H) (T : Subgroup G) 1 =
      secondParabolic T M Mc H := by
    change (sourceResidual M Mc ⊔ secondSylow T M Mc H) ⊔ (T : Subgroup G) ⊔
      ChapterF.Source.borel (residual H) (T : Subgroup G) = _
    rw [hB, sup_assoc (sourceResidual M Mc), sup_eq_right.mpr hS₂]
    rfl
  have hCB : ChapterF.Source.commonBorel (locals T M Mc H) (T : Subgroup G) =
      (M ⊓ residual H) ⊔ (T : Subgroup G) := by
    change ChapterF.Source.borel (residual H) (T : Subgroup G) ⊔
      ChapterF.Source.borel (sourceResidual M Mc ⊔ secondSylow T M Mc H)
        (T : Subgroup G) ⊔ (T : Subgroup G) = _
    rw [hB, hB₂, sup_assoc, sup_eq_right.mpr hS₂]
  have hBHM : (M ⊓ residual H) ⊔ (T : Subgroup G) = H ⊓ M := by
    apply le_antisymm
    · exact sup_le (le_inf (inf_le_right.trans (map_subtype_le _)) inf_le_left)
        (le_inf hH.1.1.2 hM.1.2)
    · intro x hx
      have hxH : x ∈ residual H ⊔ (T : Subgroup G) := hgen.symm ▸ hx.1
      have hxprod : x ∈ (residual H : Set G) * (T : Set G) := by
        have hn : (T : Subgroup G) ≤ normalizer (residual H : Set G) := hF.S_normalizes 0
        change x ∈ (residual H : Set G) * ((T : Subgroup G) : Set G)
        rw [← coe_mul_of_right_le_normalizer_left _ _ hn]
        exact hxH
      obtain ⟨r, hr, t, ht, rfl⟩ := hxprod
      have hrM : r ∈ M := (M.mul_mem_cancel_right (hM.1.2 ht)).mp hx.2
      exact ((M ⊓ residual H) ⊔ (T : Subgroup G)).mul_mem
        (mem_sup_left ⟨hrM, hr⟩) (mem_sup_right ht)
  have hinter := ChapterF.Source.lemma_F_1_3_6 hF
  rw [hzero, hone, hCB, hBHM] at hinter
  exact ⟨hzero, hone, hCB.trans hBHM, hinter,
    sup_le (sup_le (sourceResidual_le M Mc) hM.1.2) inf_le_left⟩

/-- The actual inclusion amalgam is core-free and faithful in its generated
subgroup. This does not assert that the generated subgroup is all of G. -/
theorem source_completion :
    pCore 2 (H ⊔ secondParabolic T M Mc H : Subgroup G) = ⊥ ∧
      ∀ N : Subgroup G, N ≤ H ⊓ secondParabolic T M Mc H →
        H ≤ normalizer (N : Set G) →
        secondParabolic T M Mc H ≤ normalizer (N : Set G) → N = ⊥ := by
  have hF := (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1
  obtain ⟨hzero, hone, hCB, hinter, _⟩ := source_parabolics
    hG T hempty hM hu hmany hcard e H hH eR
  constructor
  · have hcore := hF.twoCore_free
    rw [← ChapterF.Source.parabolics_generate, hzero, hone] at hcore
    exact hcore
  · intro N hN hNH hNP
    apply hF.common_normal_eq_bot N
    · rwa [hCB, ← hinter]
    · intro i
      fin_cases i
      · change ChapterF.Source.parabolic (locals T M Mc H) (T : Subgroup G) 0 ≤ _
        rwa [hzero]
      · change ChapterF.Source.parabolic (locals T M Mc H) (T : Subgroup G) 1 ≤ _
        rwa [hone]

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
