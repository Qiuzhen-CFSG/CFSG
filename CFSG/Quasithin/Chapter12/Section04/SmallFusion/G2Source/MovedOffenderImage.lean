module

public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source.NormalizerAction
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionAt.Basic
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerG2Reconstruction
public import Theory.Representation.BinaryConjugationCoordinates.ReciprocalNonStrong
public import Theory.Representation.G2OrthogonalCover.BinaryOffenders

/-!
# The actual moving offender in the binary G₂ source configuration

The chosen module and every Sylow-normalizer conjugate act reciprocally.
The literal source movement outside Q=C_T(V) makes this action nontrivial.
Since the binary Weyl module has no strong offenders, reciprocal indices
are equal and the prescribed full normalizer actor has an offender image
of order eight. The final application retains the actual odd conjugator
and the inverse convention of the source centralizer construction.

Source: Aschbacher--Smith 3.3.27--28 and B.4.6(3),(13), pp.600--601,88--90.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
open Chapter12.Section02 Chapter12.Section02.RecognitionSource
open Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open ChapterB.QuasisimpleSource Atlas.G2.Natural
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
local notation "F" => ZMod 2
local notation "W" => TraceZero F
local notation "σ" => traceZeroAction F

private theorem moved_weyl_not_strong : ¬ IsStrongFFModule σ := by
  rintro ⟨A, hA⟩
  have hoff : IsOffender σ A := ⟨hA.1, hA.2.le⟩
  have hr := OrthogonalCover.BinaryOffenders.offender_rank A hoff
  have hc := OrthogonalCover.BinaryOffenders.offender_fixedCodim A hoff
  have hh := hA.2
  omega

/-- Movement outside the literal original core produces an order-eight
offender for the supplied full normalizer actor. -/
theorem moved_full_actor_offender_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (b : V ≃* Multiplicative W)
    (ψ : normalizer (L : Set G) →* Atlas.G2.Model F)
    (hψ : ∀ (r : normalizer (L : Set G)) (x : W),
      (b.symm (Multiplicative.ofAdd (σ (ψ r) x)) : G) =
        (r : G) * (b.symm (Multiplicative.ofAdd x) : G) * (r : G)⁻¹)
    {d : G} (hd : d ∈ normalizer (T : Set G))
    (hmove : ¬ V.map (MulAut.conj d).toMonoidHom ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    let A := (V.map (MulAut.conj d).toMonoidHom).subgroupOf
      (normalizer (L : Set G))
    IsOffender σ (A.map ψ) ∧ Nat.card (A.map ψ) = 8 := by
  let := D.elementary
  obtain ⟨_, _, _, _, hMV, _, _⟩ := exists_fixed_involution_setup h D structural e hne
  have hTd : (T : Subgroup G).map (MulAut.conj d).toMonoidHom = T :=
    mem_normalizer_iff_map_conj_eq.mp hd
  have hVdT : V.conjBy d ≤ (T : Subgroup G) :=
    (map_mono D.le_sylow).trans hTd.le
  have hAM : V.conjBy d ≤ normalizer (L : Set G) :=
    hVdT.trans D.sylow_normalizes_component
  have hrecip : V ≤ (normalizer (L : Set G)).conjBy d :=
    D.le_sylow.trans (hTd.symm.le.trans (map_mono D.sylow_normalizes_component))
  have hcomm : ⁅V, V.conjBy d⁆ ≠ ⊥ := by
    intro hc
    apply hmove
    rw [← chosen_sylow_centralizer_eq_core_at h D structural]
    refine le_inf hVdT ?_
    rw [commutator_comm] at hc
    exact commutator_eq_bot_iff_le_centralizer.mp hc
  have he (a : normalizer (L : Set G)) (v : V) :
      (b (V.normalizerMonoidHom ⟨a.val, hMV.le a.property⟩ v)).toAdd =
        σ (ψ a) (b v).toAdd := by
    apply Multiplicative.ofAdd.injective
    apply b.symm.injective
    apply Subtype.ext
    change (b.symm (b (V.normalizerMonoidHom ⟨a.val, hMV.le a.property⟩ v)) : G) = _
    rw [b.symm_apply_apply, hψ]
    change _ = (a : G) * (b.symm (b v) : G) * (a : G)⁻¹
    rw [b.symm_apply_apply]
    rfl
  obtain ⟨_, hoff⟩ :=
    BinaryConjugationCoordinates.reciprocal_conjugate_offender_of_nonStrong
      (normalizer (L : Set G)) V hMV.le σ traceZeroAction_injective_binary
      ψ b he moved_weyl_not_strong d hAM hrecip hcomm
  rw [MonoidHom.range_comp, Subgroup.inclusion_range] at hoff
  refine ⟨hoff, ?_⟩
  change Nat.card (((V.conjBy d).subgroupOf (normalizer (L : Set G))).map ψ) = 8
  rw [hoff.1.card_eq_two_pow_rank,
    OrthogonalCover.BinaryOffenders.offender_rank _ hoff]
  rfl

/-- The source's actual odd moving conjugator supplies the order-eight
premise of the point-stabilizer centralizer theorem, with the same two
centralizer clauses and inverse-conjugation convention. -/
theorem exists_odd_moving_full_actor_offender_image
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (e : ActionEquiv D.quotientAction (OrthogonalCover.action F))
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G))
    (b : V ≃* Multiplicative W)
    (ψ : normalizer (L : Set G) →* Atlas.G2.Model F)
    (hψ : ∀ (r : normalizer (L : Set G)) (x : W),
      (b.symm (Multiplicative.ofAdd (σ (ψ r) x)) : G) =
        (r : G) * (b.symm (Multiplicative.ofAdd x) : G) * (r : G)⁻¹) :
    let C := (T : Subgroup G) ⊓ centralizer (L : Set G)
    IsElementaryAbelian 2 C ∧
      ∃ A : Subgroup G, A ≤ normalizer (T : Set G) ∧ Odd (Nat.card A) ∧
        ∃ d ∈ A, d ∉ normalizer (L : Set G) ∧
          ¬ V.map (MulAut.conj d⁻¹).toMonoidHom ≤
            (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          C ⊓ C.map (MulAut.conj d⁻¹).toMonoidHom = ⊥ ∧
          C.map (MulAut.conj d⁻¹).toMonoidHom ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          IsOffender σ (((V.map (MulAut.conj d⁻¹).toMonoidHom).subgroupOf
            (normalizer (L : Set G))).map ψ) ∧
          Nat.card (((V.map (MulAut.conj d⁻¹).toMonoidHom).subgroupOf
            (normalizer (L : Set G))).map ψ) = 8 := by
  obtain ⟨hC, A, hAN, ho, d, hd, hout, hmove, hdis, hCQ⟩ :=
    g2Two_source_movement_centralizer_of_weyl_model h D hne hescape e
  have hb := g2Two_block_of_weyl_model h D hescape e
  rw [← chosen_eq_blockU D hb.short] at hmove
  refine ⟨hC, A, hAN, ho, d, hd, hout, hmove, hdis, hCQ, ?_⟩
  exact moved_full_actor_offender_image h D structural e hne b ψ hψ
    ((normalizer (T : Set G)).inv_mem (hAN hd)) hmove

end CFSG.Quasithin.Chapter12.Section04.SmallFusion.G2Source
