module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.ReturningPlane.Quotient
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.StarQuotient
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalCubicOrder

/-!
# The original cyclic starred residual in the ordinary A₆ branch

The ordinary quotient L/O₂(L) has trivial center, so the prescribed
natural permutation map has a two-group kernel. Equivariance identifies
the literal L₁ image with the two-residual of the natural point stabilizer.
Its intrinsic two-core quotient has order three; the two-group kernel
preserves this quotient. Relative normality of L₁ in H identifies it with
the original starred image, giving L₁* ≃ C₃.

The final theorem supplies all of13.5.15(1) using the earlier seed identity
V₃=[V,L₁]. The ordinary quotient equivalence is the original ordinary-A₆
branch input of13.2.1/13.3, and the seed identity belongs to13.5.7(b).
No block, quaternion, IsType, or13.5.15 conclusion is used as a premise.

Source: Aschbacher–Smith,13.5.15(1), printed p.920.
-/

@[expose] public section
open Subgroup BinaryPermutation
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceStar
open Section08.SourceCompletion
open Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open PlaneGeometry.TwoBlocks
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)

include d

theorem local_kernel_two (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6)) :
    IsPGroup 2 (localMap d).ker := by
  have hz : center (D.L ⧸ pCore 2 D.L) = ⊥ := by
    apply card_eq_one.mp
    rw [Nat.card_congr (centerCongr e).toEquiv,
      alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 6)), card_bot]
  have hc : centralCore D.L = pCore 2 D.L := by
    change (center (D.L ⧸ pCore 2 D.L)).comap (QuotientGroup.mk' (pCore 2 D.L)) = _
    rw [hz]
    exact QuotientGroup.ker_mk' _
  have hk : (localMap d).ker = centralCore D.L := by
    ext l
    change ((d.local_quotient (QuotientGroup.mk' (centralCore D.L) l)) : Equiv.Perm (Fin 6)) = 1 ↔ _
    constructor
    · intro hh
      have hh' : d.local_quotient (QuotientGroup.mk' (centralCore D.L) l) = 1 := Subtype.ext hh
      exact (QuotientGroup.eq_one_iff l).mp (d.local_quotient.injective (hh'.trans (map_one _).symm))
    · intro hl
      have hh : QuotientGroup.mk' (centralCore D.L) l = 1 := (QuotientGroup.eq_one_iff l).mpr hl
      rw [hh, map_one]
      rfl
  rw [hk,hc]
  exact pCore_isPGroup

theorem original_residual_image (h : D.Hypothesis) :
    (D.L₁.subgroupOf D.L).map (localMap d) =
      let P := alternatingGroup (Fin 6) ⊓
        flagStabilizer (Section07.NaturalAction.image d D.V₁)
      (pResidual 2 P).map P.subtype := by
  let K := D.L ⊓ normalizer (D.V₁ : Set G)
  have he : D.L₁ = (pResidual 2 K).map K.subtype := by
    change (pResidual 2 (D.L ⊓ D.Gz : Subgroup G)).map _ = _
    have hK : D.L ⊓ D.Gz = K := congrArg (D.L ⊓ ·) h.normalizer_point_eq.symm
    rw [hK]
  have hsub : D.L₁.subgroupOf D.L =
      (pResidual 2 (K.subgroupOf D.L)).map (K.subgroupOf D.L).subtype := by
    rw [he]
    apply map_injective D.L.subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans inf_le_left),
      map_embedded_pResidual, map_subgroupOf_eq_of_le inf_le_left]
  rw [hsub,map_embedded_pResidual,
    ReturningPlane.localNormalizer_image d D.V₁ (h.point_lt.le.trans h.plus_le)]

theorem original_residual_quotient_card (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6)) :
    Nat.card (D.L₁ ⧸ pCore 2 D.L₁) = 3 := by
  let J := D.L₁.subgroupOf D.L
  let f := (localMap d).subgroupMap J
  have hk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap]
    exact (local_kernel_two d e).comap_subtype
  let eq₁ := Theory.GroupTheory.ComponentLocalCoreSection.quotientCoreEquiv 2 f
    ((localMap d).subgroupMap_surjective J) hk
  have hc : Nat.card (J ⧸ pCore 2 J) = 3 := by
    rw [Nat.card_congr eq₁.toEquiv]
    rw [show J.map (localMap d) = _ from original_residual_image d h]
    exact NaturalCubicOrder.point_residual_quotient_card (alternatingGroup (Fin 6)) le_rfl
      (Section07.NaturalAction.image d D.V₁)
      (Section07.NaturalAction.image_dim d D.V₁ (h.point_lt.le.trans h.plus_le) 1 d.line_card)
  let eq₂ := (subgroupOfEquivOfLe (show D.L₁ ≤ D.L from (map_subtype_le _).trans inf_le_left))
  let eq₃ := Theory.GroupTheory.ComponentLocalCoreSection.quotientCoreEquiv 2 eq₂.toMonoidHom
    eq₂.surjective (IsPGroup.ker_isPGroup_of_injective eq₂.injective)
  exact (Nat.card_congr eq₃.toEquiv).symm.trans hc

theorem original_star_cyclic (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hn : (D.L₁.subgroupOf D.H).Normal) :
    Nonempty (Section08.Source.starImage D.H D.L₁ ≃* C3) := by
  have hc : Nat.card (Section08.Source.starImage D.H D.L₁) = 3 :=
    (Nat.card_congr (localStarEquiv h hn).toEquiv).symm.trans
      (original_residual_quotient_card d h e)
  let : IsCyclic (Section08.Source.starImage D.H D.L₁) := isCyclic_of_prime_card hc
  exact ⟨mulEquivOfCyclicCardEq (by simpa only [Nat.card_eq_fintype_card,
    Fintype.card_multiplicative, ZMod.card] using hc)⟩

theorem source13_5_15_one (h : D.Hypothesis)
    (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
    (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal) :
    D.UH = ⁅D.UH,D.L₁⁆ ∧ D.UH ≤ D.L ∧
      Nonempty (Section08.Source.starImage D.H D.L₁ ≃* C3) := by
  have hh := closure_reduction h hseed hn
  exact ⟨hh.1,hh.2.2,original_star_cyclic d h e hn⟩

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceStar
end
