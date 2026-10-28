module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SixFlags
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.SeedNormalizerBound
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.RankOne
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.GroupTheory.PrimeRankZero
/-!
# The ordinary local quotient in the original six-letter branch

The marked natural plane has the syntheme stabilizer of order 48.
The faithful full H* permutation action therefore bounds the original
component seed-normalizer's three-rank by one, also in the augmentation
cover after its actual natural projection. The contained point residual
has quotient of order three or nine, so the rank is exactly one. Original
13.7.5(5) then forces the ordinary A6 local quotient.

Source: Aschbacher–Smith, 13.7.6(3a), printed p.939. The independent
chief-factor count is not asserted by this rank deduction.
-/
@[expose] public section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation Module
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionParabolic
open Section08.TransvectionParabolic.Marking
open Section08.TransvectionParabolic.Marking.CompatibleFlags
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
private theorem natural_plane_rank_le_one :
    primeRank 3 (subspaceStabilizer (naturalRepresentation (Fin 6)) canonicalPlane) ≤ 1 := by
  have hle : subspaceStabilizer (naturalRepresentation (Fin 6)) canonicalPlane ≤ H2 := by
    intro g hg
    apply (canonicalPlane_stabilizer g).mp
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩
      exact (hg v).mpr hv
    · intro v hv
      refine ⟨naturalRepresentation (Fin 6) g⁻¹ v,?_,?_⟩
      · exact ((subspaceStabilizer (naturalRepresentation (Fin 6)) canonicalPlane).inv_mem hg v).mpr hv
      · simp only [← Module.End.mul_apply,← map_mul,mul_inv_cancel,map_one,Module.End.one_apply]
  apply (primeRank_mono 3 hle).trans
  let P : Sylow 3 H2 := default
  apply P.primeRank_le_one_of_isCyclic
  obtain ⟨a,ha⟩ := P.isPGroup'.exists_card_eq
  have hsmall : a ≤ 1 := by
    by_contra! hh
    have hd := (ha ▸ pow_dvd_pow 3 (by omega : 2 ≤ a)).trans
      (P : Subgroup H2).card_subgroup_dvd_card
    have hc : Nat.card H2 = 48 := synthemeStabilizer_order
    rw [hc] at hd
    norm_num at hd
  apply isCyclic_of_card_dvd_prime (p := 3)
  rw [ha]
  simpa using pow_dvd_pow 3 hsmall
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
include d
/-- Original contained six-letter case: the actual seed normalizer has rank one,
forcing the ordinary local quotient rather than its triple cover. -/
theorem six_seed_rank_and_ordinary_of_one_le
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (alternatingNaturalRepresentation (Fin 6)) eK) :
    primeRank 3 (K ⊓ normalizer (V₃ : Set G) : Subgroup G) = 1 ∧
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨_,hcases⟩ := six_seed_marking_of_one_le d hH hF9 hKH hK hL₁K ρ hρ eK hs
  have hu : primeRank 3 (K ⊓ normalizer (V₃ : Set G) : Subgroup G) ≤ 1 := by
    rcases hcases with ⟨f,E,hf,he,_,hplane⟩ | ⟨f,E,hf,he,_,hplane⟩
    · have hb := seed_normalizer_rank_le_of_full_action hKH ρ hρ
        (naturalRepresentation (Fin 6)) f hf E.toLinearMap he
      rw [hplane,plane_image_eq_canonical] at hb
      exact hb.trans natural_plane_rank_le_one
    · let F := (coreToNatural (Fin 6)).comp E.toLinearMap
      have he' : ∀ a u, F (ρ a u) = naturalRepresentation (Fin 6) (f a) (F u) := by
        intro a u
        change coreToNatural (Fin 6) (E (ρ a u)) = _
        rw [he]
        exact coreToNatural_equivariant (f a) (E u)
      have hb := seed_normalizer_rank_le_of_full_action hKH ρ hρ
        (naturalRepresentation (Fin 6)) f hf F he'
      change primeRank 3 (K ⊓ normalizer (V₃ : Set G) : Subgroup G) ≤
        primeRank 3 (subspaceStabilizer (naturalRepresentation (Fin 6))
          ((sectionImage H V₃ V₁ V₃).map ((coreToNatural (Fin 6)).comp E.toLinearMap))) at hb
      rw [Submodule.map_comp,hplane,plane_image_eq_canonical] at hb
      exact hb.trans natural_plane_rank_le_one
  have hn : primeRank 3 (sourceOne L T V₁) ≠ 0 := by
    intro hz
    have hq : primeRank 3 (sourceOne L T V₁ ⧸ pCore 2 (sourceOne L T V₁)) = 0 := by
      rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup,hz]
    have hnd := PrimeRank.eq_zero_iff_not_dvd_card.mp hq
    rcases point_residual_quotient_card d with hc | hc <;> rw [hc] at hnd <;> exact hnd (by decide)
  have hl := primeRank_mono 3 (le_inf hL₁K (point_residual_normalizes_seed d))
  have hr : primeRank 3 (K ⊓ normalizer (V₃ : Set G) : Subgroup G) = 1 := by omega
  exact ⟨hr,ordinary_of_rank_one d hL₁K hr⟩
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
