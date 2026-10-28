module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Inputs

/-!
# Transfer of natural-layer exhaustion to the entire intrinsic core

The source equality identifies [O₂(M),K] with the central-omega moved layer.
The existing ambient-to-intrinsic identity then places the entire blockU in
Ω₁Z(O₂(L)). The canonical moved-section equivalence identifies its quotient
by C_U(L) and intertwines the original conjugation action. All maps are the
literal subgroup and two-core quotient maps.

Both initial recognition and exhaustion remain explicit source inputs here.
This conditional assembly is not the unconditional C.1.32 natural branch.
Source: Aschbacher--Smith C.1.32(2), pp.135--136; MS93 (3.2)(vi), (3.6),
and Section 7, pp.932--933.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC ChapterB.QuasisimpleSource
namespace AlternatingSixReconstruction.Natural
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "Q" => pCore 2 M
local notation "X" => centralOmega L R

include h in
/-- Exhaustion controls the whole intrinsic core, including its central attachment. -/
theorem core_le_centralOmega_of_exhaustion
    (hex : ⁅Q, K⁆ = ⁅X, K⁆) : blockU L ≤ omegaCenterIn (pCore 2 L) := by
  have he : (blockU K).map (K).subtype = ⁅X, K⁆ :=
    h.ambient_commutator_eq_relative_core.symm.trans hex
  have hk : blockU K ≤ omegaCenterIn (pCore 2 K) := by
    intro x hx
    have hxX : (x : M) ∈ X := (commutator_le_left X K)
      (he ▸ mem_map_of_mem (K).subtype hx)
    obtain ⟨_, hc, hs⟩ := (mem_omegaCenterIn_iff Q (x : M)).mp hxX
    apply (mem_omegaCenterIn_iff _ _).mpr
    refine ⟨blockU_le_core hx, ?_, ?_⟩
    · intro y hy
      apply Subtype.ext
      exact hc y (pCoreIn_le_of_subnormal 2 h.component.subnormal
        (mem_map_of_mem (K).subtype hy))
    · exact Subtype.ext hs
  let f := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  have hf : (blockU K).map f.toMonoidHom = blockU L := by
    rw [blockU, blockU, map_commutator, pCore_map_iso,
      map_top_of_surjective _ f.surjective]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hf.symm ▸ hx
  obtain ⟨hyQ, hc, hs⟩ := (mem_omegaCenterIn_iff _ _).mp (hk hy)
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · rw [← pCore_map_iso 2 f]
    exact mem_map_of_mem f.toMonoidHom hyQ
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := (pCore_map_iso 2 f).symm ▸ hz
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg f (hc w hw)
  · simpa only [map_pow, map_one, MulEquiv.coe_toMonoidHom] using congrArg f hs

/-- The initial natural quotient becomes the literal block quotient after exhaustion. -/
theorem model_of_initial_and_exhaustion (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (hex : ⁅Q, K⁆ = ⁅X, K⁆) :
    IsLinearBlockModel L ((BinaryPermutation.naturalRepresentation (Fin 6)).comp
      (alternatingGroup (Fin 6)).subtype) := by
  let := h.relative_normal
  obtain ⟨E⟩ := hn
  have he : (blockU K).map (K).subtype = ⁅X, K⁆ :=
    h.ambient_commutator_eq_relative_core.symm.trans hex
  have hm := BlockMovingSection.model_of_moving X K (QuotientGroup.mk' Q)
    (QuotientGroup.mk'_surjective Q)
    ((QuotientGroup.ker_mk' Q).trans (centralOmega_centralizer h e hz).symm)
    he (cComponentTwoCoreQuotientEquiv h.component) (fun _ => rfl)
    ((BinaryPermutation.naturalRepresentation (Fin 6)).comp
      (alternatingGroup (Fin 6)).subtype) E
  exact hm.of_mulEquiv (subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left))

omit h in
/-- Actual assembly of the two independent source implications. Both must be
discharged before this yields the unconditional natural-core input. -/
theorem naturalCore_of_initial_and_exhaustion
    (hi : InitialRecognitionInput κ) (hx : CoreExhaustionInput κ) : NaturalCoreInput κ := by
  intro G _ _ L R h e hz
  have hn := hi G L R h e hz
  have hex := hx G L R h e hz hn
  have hu := core_le_centralOmega_of_exhaustion h hex
  refine ⟨IsElementaryAbelian.of_le hu, ?_, model_of_initial_and_exhaustion h e hz hn hex⟩
  intro x hx
  exact ((mem_omegaCenterIn_iff _ _).mp (hu hx)).2.1

end AlternatingSixReconstruction.Natural
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
