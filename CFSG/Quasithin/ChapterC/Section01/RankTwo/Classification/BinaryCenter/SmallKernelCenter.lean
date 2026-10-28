module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightSmallDisplacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCenter.DistanceEightCoefficients
public import Theory.GroupTheory.EmbeddedCenterMap
/-!
# The center commutator after a central quotient of order at most two

In an actual large-distance binary MS input, the center of the commutator
core is centralized by the original component two-core. Small central
displacement therefore makes the commutator of the quotient-center preimage
centralize that two-core. Two-perfect commutator idempotence proves that its
moved subgroup is exactly the original moved center.

This is the checked-center identity used in Aschbacher--Smith 13.6.22,
printed pp.932--933. It is derived directly from the MS93 source layers and
does not require any of the five C.1.34 classification alternatives.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS
local notation "sCenter" => fun (A : Subgroup _) => Subgroup.map (Subgroup.subtype A) (Subgroup.center A)
variable {J H : Type*} [Group J] [Group H] [Finite J]
omit [Finite J] in
private theorem centerIn_eq (D : Subgroup J) : sCenter D = D ⊓ centralizer (D : Set J) := by
  ext d
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, fun y hy => congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)⟩
  · rintro ⟨hd, hc⟩
    exact ⟨⟨d, hd⟩, mem_center_iff.mpr (fun y => Subtype.ext (hc y y.property)), rfl⟩

theorem center_preimage_commutator_of_small_displacement (hp : IsPPerfect 2 J)
    (f : J →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hc : sCenter (blockU J) ≤ centralizer (pCore 2 J : Set J))
    (hsmall : ∀ A : Subgroup J, A ≤ blockU J →
      ⁅A,blockU J⁆ ≤ f.ker → A ≤ centralizer (blockU J : Set J)) :
    ⁅(sCenter (pCore 2 H)).comap f, (⊤ : Subgroup J)⁆ =
      ⁅sCenter (pCore 2 J), (⊤ : Subgroup J)⁆ := by
  let : Finite H := Finite.of_surjective f hf
  let X := (sCenter (pCore 2 H)).comap f
  let M := ⁅X, (⊤ : Subgroup J)⁆
  have hcore : (pCore 2 H).comap f = pCore 2 J :=
    f.comap_pCore_of_ker_isPGroup hf hk
  have hmap : (pCore 2 J).map f = pCore 2 H := by
    rw [← hcore, map_comap_eq_self_of_surjective hf]
  have hXP : X ≤ pCore 2 J := by
    rw [← hcore]
    exact comap_mono (map_subtype_le _)
  have hnX : X.Normal := inferInstanceAs
    (((center (pCore 2 H)).map (pCore 2 H).subtype).comap f).Normal
  have hMX : M ≤ X := commutator_le_left _ _
  have hMQ : M ≤ blockU J := commutator_mono hXP le_rfl
  have hXPker : ⁅X, pCore 2 J⁆ ≤ f.ker := by
    rw [← Subgroup.map_eq_bot_iff, map_commutator, hmap]
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (map_comap_le _ _).trans ((centerIn_eq _).le.trans inf_le_right)
  have hMZQ : M ≤ sCenter (blockU J) := by
    rw [centerIn_eq]
    exact le_inf hMQ (hsmall M hMQ
      ((commutator_mono hMX blockU_le_core).trans hXPker))
  have hMZ : M ≤ sCenter (pCore 2 J) := by
    rw [centerIn_eq]
    exact le_inf (hMX.trans hXP) (hMZQ.trans hc)
  have hid : ⁅M, (⊤ : Subgroup J)⁆ = M :=
    commutator_isPPerfect_idempotent ⊤ X
      (hp.of_surjective (topEquiv (G := J)).symm.toMonoidHom
        (topEquiv (G := J)).symm.surjective)
      (pCore_isPGroup.to_le hXP) (by rw [normalizer_eq_top])
  apply le_antisymm (hid.symm.le.trans (commutator_mono hMZ le_rfl))
  apply commutator_mono _ le_rfl
  intro z hz
  change f z ∈ sCenter (pCore 2 H)
  rw [centerIn_eq] at hz ⊢
  refine ⟨?_, ?_⟩
  · rw [← hmap]
    exact mem_map_of_mem f hz.1
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (hmap.symm ▸ hx : x ∈ (pCore 2 J).map f)
    exact (map_mul f y z).symm.trans ((congrArg f (hz.2 y hy)).trans (map_mul f z y))
namespace MS93.InputSetup
variable {κ : GroupClass} {L R : Subgroup J} {h : Input κ L R}
  (t : InputSetup h)
  (common : CommonFacts t.reduction.radical t.source t.geometry)
  (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)

include t common earlier
/-- The full-center commutator identity in every actual large-distance input. -/
theorem large_center_preimage_commutator
    (f : L →* H) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hcard : Nat.card f.ker ≤ 2)
    (hn : f.ker.map L.subtype ≤ center J) :
    ⁅(sCenter (pCore 2 H)).comap f, (⊤ : Subgroup L)⁆ =
      ⁅sCenter (pCore 2 L), (⊤ : Subgroup L)⁆ := by
  have hp : IsPPerfect 2 L := by
    rw [← h.residual_eq]
    exact isPPerfect_pResidual 2
  apply center_preimage_commutator_of_small_displacement hp f hf hk
  · rintro z ⟨zC,hzC,rfl⟩ p hp
    exact mul_inv_eq_iff_eq_mul.mp
      (t.large_core_centralizes_center common earlier p hp ⟨zC,hzC⟩)
  · intro A hA hcomm
    let N := f.ker ⊓ blockU L
    have hN : N.map L.subtype ≤ commutatorCore L := by
      rw [h.commutatorCore_eq_internal]
      exact map_mono inf_le_right
    have hAc : A.map L.subtype ≤ commutatorCore L := by
      rw [h.commutatorCore_eq_internal]
      exact map_mono hA
    have hNc : N.map L.subtype ≤ center J := (map_mono inf_le_left).trans hn
    have hNc2 : Nat.card (N.map L.subtype) ≤ 2 := by
      rw [card_map_of_injective L.subtype_injective]
      exact (card_le_of_le (show N ≤ f.ker from inf_le_left)).trans hcard
    have hd : ⁅A.map L.subtype,commutatorCore L⁆ ≤ N.map L.subtype := by
      rw [h.commutatorCore_eq_internal,← map_commutator]
      apply map_mono
      exact le_inf hcomm (commutator_le_right _ _)
    have hc := t.large_core_small_displacement common earlier hAc hN hNc hNc2 hd
    intro a ha q hq
    apply L.subtype_injective
    exact hc (mem_map_of_mem L.subtype ha) (q : J)
      (h.commutatorCore_eq_internal.symm ▸ mem_map_of_mem L.subtype hq)
end MS93.InputSetup
end CFSG.Quasithin.ChapterC.BinaryMS
