module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Center.Placement.FixedQuotient.Contract
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Center.Placement.FixedQuotient.Calculation.Lifting
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# The natural-section fixed-preimage calculation

The small commutator hypothesis makes the radical equal to N. Generation
by T and Q identifies the moving preimage with N[H,T]. The full normalizer
of the order-four actor makes E cover the natural fixed space, using the
section’s own marking. Finally the split fixed/moving decomposition and
N ≤ E give the literal equality with (E ∩ [H,T])C_H(A mod N).

This discharges `NaturalFixedCalculation`, consumed by
`FixedQuotient.Reduction.seed_fixed_quotient_of_calculation`.
Source: Meierfrankenfeld–Stellmacher (1993), (4.6.7), p.904,
with the c(U) and relative-normalizer conventions on p.881.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement
open Escape

private theorem moving_eq {A : Type*} [Group A]
    {π : A →* SL} {Q T H N : Subgroup A}
    (s : SingleNaturalSection π Q T H N) (hgen : T ⊔ Q = ⊤) :
    movingPreimage Q H N = radicalPreimage Q H N ⊔ ⁅H, T⁆ := by
  let := s.normal_group
  let := s.radical_normal
  let D := radicalPreimage Q H N
  let q := QuotientGroup.mk' D
  have hqtop : (⊤ : Subgroup A).map q = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective D)
  have hcomm : ⁅H.map q, Q.map q⁆ = ⊥ := by
    rw [← map_commutator, Subgroup.map_eq_bot_iff]
    rw [show q.ker = D from QuotientGroup.ker_mk' D]
    exact le_sup_right
  have hgenq : Q.map q ⊔ T.map q = ⊤ := by
    rw [← Subgroup.map_sup, sup_comm, hgen, hqtop]
  have he := commutator_eq_of_centralizing_sup hgenq
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm))
    (show T.map q ≤ normalizer (H.map q : Set (A ⧸ D)) from le_normalizer_of_normal)
  have heq : ⁅H, T⁆.map q = ⁅H, (⊤ : Subgroup A)⁆.map q := by
    rw [map_commutator, map_commutator, hqtop]
    exact he
  have hh := congrArg (Subgroup.comap q) heq
  rw [comap_map_eq, comap_map_eq] at hh
  change D ⊔ ⁅H, (⊤ : Subgroup A)⁆ = D ⊔ ⁅H, T⁆
  simpa only [q, QuotientGroup.ker_mk', sup_comm] using hh.symm

/-- Every finite split natural section satisfies the fixed-preimage identity,
with no extra fixed-space or marking compatibility hypothesis. -/
theorem naturalFixedCalculation (A : Type*) [Group A] [Finite A] :
    NaturalFixedCalculation A := by
  intro π Q T H N E J s hgen hHQ hQJ hcard hNE hEH hfix hnorm hout
  let := s.normal_kernel
  let := s.normal_group
  have hrad : radicalPreimage Q H N = N := sup_eq_left.mpr hHQ
  let V := movingPreimage Q H N
  let C := centralizerModulo H ⊤ N
  have hmove : V = N ⊔ ⁅H, T⁆ := by
    change movingPreimage Q H N = _
    rw [moving_eq s hgen, hrad]
  have hdec : H = V ⊔ C := by simpa only [hrad] using s.decomposition
  let n : RankOnePairing.NaturalFactor π ⊤ V N := by
    simpa only [hrad] using s.natural
  let : V.Normal := normalizer_eq_top_iff.mp (top_unique n.normalized)
  have hcentral : centralizerModulo V J N ≤ E :=
    Calculation.natural_fixed_le n s.projection_surjective
      (s.projection_kernel ▸ hQJ) hcard hNE hfix hnorm (by rwa [hmove])
  have hNC : N ≤ C := by
    intro x hx
    exact inf_le_centralizerModulo H ⊤ N ⟨s.kernel_le hx, hx⟩
  have hCJ : C ≤ centralizerModulo H J N := by
    intro x hx
    obtain ⟨hxH, hx⟩ := mem_centralizerModulo_iff.mp hx
    exact mem_centralizerModulo_iff.mpr ⟨hxH, fun j _ => hx j (mem_top j)⟩
  apply le_antisymm
  · intro x hx
    have hxH := (mem_centralizerModulo_iff.mp hx).1
    rw [hdec] at hxH
    obtain ⟨v, hv, c, hc, rfl⟩ := mem_sup_of_normal_left.mp hxH
    have hvJ : v ∈ centralizerModulo H J N := by
      have hh := (centralizerModulo H J N).mul_mem hx
        ((centralizerModulo H J N).inv_mem (hCJ hc))
      simpa only [mul_inv_cancel_right] using hh
    have hvE : v ∈ E := hcentral (mem_centralizerModulo_iff.mpr
      ⟨hv, (mem_centralizerModulo_iff.mp hvJ).2⟩)
    rw [hmove] at hv
    obtain ⟨z, hz, d, hd, rfl⟩ := mem_sup_of_normal_left.mp hv
    have hdE : d ∈ E := by
      have hh := E.mul_mem (E.inv_mem (hNE hz)) hvE
      simpa only [inv_mul_cancel_left] using hh
    apply ((E ⊓ ⁅H, T⁆) ⊔ C).mul_mem
    · exact ((E ⊓ ⁅H, T⁆) ⊔ C).mul_mem (mem_sup_right (hNC hz))
        (mem_sup_left ⟨hdE, hd⟩)
    · exact mem_sup_right hc
  · apply sup_le _ hCJ
    intro x hx
    apply mem_centralizerModulo_iff.mpr
    refine ⟨hEH hx.1, ?_⟩
    intro j hj
    exact (commutator_comm E J ▸ hfix) (commutator_mem_commutator hj hx.1)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement
