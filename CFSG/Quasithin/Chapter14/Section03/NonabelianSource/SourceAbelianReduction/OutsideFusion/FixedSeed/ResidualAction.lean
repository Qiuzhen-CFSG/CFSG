module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.FixedSeed.Centralizer
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.FixedSeed.Defs
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.SeedCubicAction
public import Theory.GroupTheory.InvolutionCosetCentralizerAction
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Mathlib.GroupTheory.FixedPointFree

/-!
# The fixed-seed centralizer generates the seed in its two-residual

Coset transitivity allows each actor in I₂ to be adjusted by R = O₂(I₂)
so that it centralizes t. The adjustment preserves the literal S₃ quotient,
whose cubic acts without fixed points on V. Lift that cubic to O²(C_{I₂}(t));
surjectivity of its commutator map on V then puts V in this embedded residual.
The original equality C_R(t) = V supplies V ≤ C_{I₂}(t).

This is the residual-generation step of Aschbacher--Smith 14.3.21(2),
printed p.998. Transitivity on square-one elements of Rt remains explicit.
-/

public noncomputable section
open Subgroup Theory.GroupTheory InvertedCubicTensor
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition
variable {G : Type*} [Group G] [Finite G]

/-- Coset transitivity supplies the literal fixed-seed residual-generation step. -/
theorem source_fixed_seed_residual_generation_of_coset_transitivity
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g∈F.P (sourceResidual M Mc)) (hgH : g∉F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
    (horbit : FixedSeedCosetTransitivity F (sourceResidual M Mc)) :
    FixedSeedResidualGeneration F (sourceResidual M Mc) := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  let L := sourceResidual M Mc
  have hnat : 3 ≤ 2 → Nonempty (AmbientNaturalMarking L h.L_normalizes_seed 2) := by omega
  obtain ⟨hcomm,hsquare⟩ := F.localKernel_commutator_squares h.simpleQTKE L M (by decide)
    h.seed_le_sylow h.L_normalizes_seed h.sylow_normalizes_L h.L_residual hnat (h.flag_escape F)
  have hspan : F.U = conjugateSpanBy (F.Vi 2) F.H := by rw [F.last]; rfl
  obtain ⟨e₀,_,_,_,hIG,hIN,_,_,_,_,hcore,_,_⟩ :=
    F.binary_generation (by decide) L h.L_normalizes_seed (h.binarySeedAction_surjective F)
      h.centralizer hcomm hsquare hspan hne g hgP hgH
  let I := F.I₂ L
  let R := I.pCoreIn 2
  let V := rankTwoSeed T M
  have hIV : I ≤ normalizer (V : Set G) := by simpa only [Gi,F.last] using hIG
  have hker : I ⊓ centralizer (V : Set G) = R := by simpa only [F.last] using hcore
  let π := F.binaryCoreProjection L e₀
  have hπ : Function.Surjective π := by
    intro s
    obtain ⟨i,hi⟩ := QuotientGroup.mk'_surjective (pCore 2 I) (e₀.symm s)
    exact ⟨i,by rw [F.binaryCoreProjection_apply,hi,e₀.apply_symm_apply]⟩
  have hkπ : π.ker = R.subgroupOf I := by
    have hk : π.ker = pCore 2 I := by
      ext i
      change F.binaryCoreProjection L e₀ i = 1 ↔ i ∈ pCore 2 I
      rw [F.binaryCoreProjection_apply]
      constructor
      · intro hi
        exact (QuotientGroup.eq_one_iff i).mp (e₀.injective (hi.trans e₀.map_one.symm))
      · intro hi
        change e₀ (QuotientGroup.mk i) = 1
        rw [(QuotientGroup.eq_one_iff i).mpr hi,map_one]
    rw [hk]
    exact ((pCore 2 I).comap_map_eq_self_of_injective I.subtype_injective).symm
  intro t ht ht2 htout htV
  let C := I ⊓ centralizer ({t} : Set G)
  have hCR : R ⊓ centralizer ({t} : Set G) = V :=
    source_fixed_seed_core_centralizer_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs t ht ht2 htout htV
  have hVC : V ≤ C := hCR.ge.trans (inf_le_inf_right _ (pCoreIn_le 2 I))
  have htI : t ∈ normalizer (I : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hIG).mp hIN (F.invariant 2 ht)
  let ρ : C →* S₃ := π.comp (inclusion inf_le_left)
  have hρ : Function.Surjective ρ :=
    centralizer_restriction_surjective_of_involution_coset_transitivity
      I R V (pCoreIn_le 2 I) hIV hker t htI htV
      (by rw [← ht2]; exact pow_orderOf_eq_one t)
      (horbit t ht ht2 htout htV) π hπ hkπ
  have hc : cubic ∈ pResidual 2 S₃ := mem_pResidual_of_orderOf_coprime
    ((by decide : Nat.Coprime 2 3).of_dvd_right
      (orderOf_dvd_of_pow_eq_one (by decide +kernel : cubic ^ 3 = 1)))
  rw [← map_pResidual_of_surjective 2 ρ hρ] at hc
  obtain ⟨c,hc,hcubic⟩ := hc
  let i : I := inclusion inf_le_left c
  let α : MulAut V := V.normalizerMonoidHom ⟨i,hIV i.property⟩
  have hfree : MonoidHom.FixedPointFree α.toMonoidHom := by
    intro v hv
    apply Subtype.ext
    exact binary_core_cubic_seed_fixed_free F L e₀ hIG hcore i hcubic v v.property
      (congrArg Subtype.val hv)
  let D := (pResidual 2 C).map C.subtype
  have hCD : ⁅C,D⁆ ≤ D :=
    le_normalizer_iff_commutator_le_right.mp (le_normalizer_embedded_pResidual 2 C)
  change V ≤ D
  intro v hv
  obtain ⟨w,hw⟩ := hfree.commutatorMap_surjective (⟨v,hv⟩ : V)
  have hm : (w : G) / (α w : G) ∈ D := by
    have he : (w : G) / (α w : G) = (w : G) * (c : G) * (w : G)⁻¹ * (c : G)⁻¹ := by
      change (w : G) / ((c : G) * (w : G) * (c : G)⁻¹) = _
      simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
      group
    rw [he]
    exact hCD (commutator_mem_commutator (hVC w.property) (mem_map_of_mem C.subtype hc))
  have he : (w : G) / (α w : G) = v := congrArg Subtype.val hw
  exact he ▸ hm

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
