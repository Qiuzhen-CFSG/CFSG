module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticSecondKernelOrder
public import Theory.GroupAction.FaithfulSixteen

/-!
# The original core interval over the full second kernel

The actual faithful order-sixteen quotient has a five-divisible actor.
Every H-invariant subgroup between its full kernel C and the full core is
therefore C or the full core.  The exact radical has order two or four.
These statements retain the original subgroups, without a bound on C or
an assumed model for the whole parabolic.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- Irreducibility of the actual quotient gives the original invariant
interval, together with the exact two possible commutator-radical orders. -/
theorem source_quintic_full_kernel_interval
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let UH := conjugateSpanBy (localModule T M) H
    let QH := H.pCoreIn 2
    let C := H ⊓ centralizer (UH : Set G)
    (Nat.card (UH ⊓ centralizer (QH : Set G) : Subgroup G) = 2 ∨
      Nat.card (UH ⊓ centralizer (QH : Set G) : Subgroup G) = 4) ∧
      ∀ D : Subgroup G, C ≤ D → D ≤ QH → H ≤ normalizer (D : Set G) →
        D = C ∨ D = QH := by
  classical
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  obtain ⟨_,hN,hE,hW,hdual⟩ := source_quintic_second_kernel_card_sixteen
    hG T hempty hM hu hmany hcard e H hH hi
  let := hN
  let := hE
  let W := Q ⧸ C.subgroupOf Q
  have hrad : Nat.card (U ⊓ centralizer (Q : Set G) : Subgroup G) = 2 ∨
      Nat.card (U ⊓ centralizer (Q : Set G) : Subgroup G) = 4 := by
    have hc := (Section02.SolvableAmalgam.source_index_five_closure_structure
      hG T hempty hM hu hmany hcard e H hH.1 hi).2
    change Nat.card U = 32 ∨ Nat.card U = 64 at hc
    change 16 * Nat.card (U ⊓ centralizer (Q : Set G) : Subgroup G) = Nat.card U at hdual
    omega
  refine ⟨hrad,?_⟩
  intro D hCD hDQ hnD
  obtain ⟨hCQ,hN',hE',α,hker,hnot,hbound,hα⟩ :=
    source_quintic_faithful_second_kernel_action hG T hempty hM hu hmany hcard e H hH hi
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have h5 : 5 ∣ Nat.card α.range := by
    have hh : Nat.card α.range = Nat.card (H ⧸ pCore 2 H) := by
      rw [←Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv,hker]
    rw [hh]
    rcases Section02.SolvableAmalgam.source_index_five_models
      hG T hempty hM hu hmany hcard e H hH.1 hi with hd | hs
    · rw [(Nat.card_congr hd.some.toEquiv).trans DihedralGroup.nat_card]; decide
    · rw [(Nat.card_congr hs.some.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card]; decide
  let π := QuotientGroup.mk' (C.subgroupOf Q)
  let R := (D.subgroupOf Q).map π
  have hforward (h : H) (w : W) (hw : w ∈ R) : α h w ∈ R := by
    obtain ⟨q,hq,rfl⟩ := hw
    rw [hα]
    apply mem_map_of_mem π
    exact (mem_normalizer_iff.mp (hnD h.property) q).mp hq
  have hinv (h : H) (w : W) : w ∈ R ↔ α h w ∈ R := by
    refine ⟨hforward h w,?_⟩
    intro hw
    have hh := hforward h⁻¹ (α h w) hw
    simpa only [map_inv,MulAut.inv_apply,MulEquiv.symm_apply_apply] using hh
  rcases Theory.GroupAction.invariant_eq_bot_or_top_of_image_five α h5 hW R hinv with he | he
  · left
    apply le_antisymm ?_ hCD
    have hh : D.subgroupOf Q ≤ π.ker := (Subgroup.map_eq_bot_iff _).mp he
    rw [QuotientGroup.ker_mk'] at hh
    intro d hd
    exact hh (show (⟨d,hDQ hd⟩ : Q) ∈ D.subgroupOf Q from hd)
  · right
    apply le_antisymm hDQ
    have he' : (D.subgroupOf Q).map π = ⊤ := he
    have hm : (⊤ : Subgroup Q).map π ≤ (D.subgroupOf Q).map π := by rw [he']; exact le_top
    have hh := map_le_map_iff.mp hm
    rw [QuotientGroup.ker_mk',sup_of_le_left (subgroupOf_mono Q hCD)] at hh
    intro q hq
    exact hh (mem_top (⟨q,hq⟩ : Q))

end CFSG.Quasithin.Chapter14.Section06
