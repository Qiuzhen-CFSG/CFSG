module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.ModuleSection

/-!
# Transferring dual fixation through the full natural section

Write H = W C modulo D = N[H,Q], where W is the moving preimage and C is
the fixed preimage. For an edge-fixed element w c, the factor c is fixed
by every actor modulo D, so w is edge-fixed too. Its dual coordinates
transfer fixation to the chosen actor, and multiplication by c recovers
fixation of the original element. No replacement of D by U is used.

Source: the section convention on p.881 and MS93 (4.3.2)(3), printed p.884.
-/

public section

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.RankOne.FixedSection
variable {G : Type*} [Group G] {π : G →* SL} {U W D : Subgroup G}

private theorem dual_coordinates_fixed_iff
    (u : RankOnePairing.NaturalFactor π ⊤ U ⊥)
    (d : RankOnePairing.DualFactor π ⊤ W D U u) (g : G) (w : W) :
    ⁅g, w.val⁆ ∈ D ↔
      ((u.marking (π g))⁻¹.val).transpose.mulVec (d.coordinates w).toAdd =
        (d.coordinates w).toAdd := by
  let y : W := ⟨g * w.val * g⁻¹,
    le_normalizer_iff.mp d.normalized g (mem_top g) w.val w.property⟩
  have ha := d.action g (mem_top g) w y rfl
  have hk : ⁅g, w.val⁆ ∈ D ↔ d.coordinates (y * w⁻¹) = 1 := by
    change (y * w⁻¹) ∈ D.subgroupOf W ↔ _
    rw [← d.kernel]
    rfl
  rw [hk, map_mul, map_inv, mul_inv_eq_one]
  exact (Multiplicative.toAdd.injective.eq_iff).symm.trans (by rw [ha])

/-- Transfer fixation across the moving coordinates while retaining the
full fixed summand and the original radical denominator. -/
theorem split_section_fixed_transfer
    {Q H N E : Subgroup G} (s : SingleNaturalSection π Q E H N)
    (u : RankOnePairing.NaturalFactor π ⊤ U ⊥)
    (d : RankOnePairing.DualFactor π ⊤ (movingPreimage Q H N)
      (radicalPreimage Q H N) U u)
    (A T K : Subgroup G) (hAH : A ≤ H)
    (hAT : ⁅A, T⁆ ≤ radicalPreimage Q H N)
    (hfixed : ∀ v : Fin 3 → ZMod 2,
      (∀ t ∈ T, ((u.marking (π t))⁻¹.val).transpose.mulVec v = v) →
      ∀ k ∈ K, ((u.marking (π k))⁻¹.val).transpose.mulVec v = v) :
    ⁅A, K⁆ ≤ radicalPreimage Q H N := by
  let := s.radical_normal
  let W := movingPreimage Q H N
  let D := radicalPreimage Q H N
  let C := centralizerModulo H ⊤ D
  let : W.Normal := normalizer_eq_top_iff.mp (top_unique d.normalized)
  have hWH : W ≤ H := by rw [s.decomposition]; exact le_sup_left
  have hCT (J : Subgroup G) : C ≤ centralizerModulo H J D := by
    intro c hc
    obtain ⟨hcH, hc⟩ := mem_centralizerModulo_iff.mp hc
    exact mem_centralizerModulo_iff.mpr ⟨hcH, fun j _ => hc j (mem_top j)⟩
  have hAK : A ≤ centralizerModulo H K D := by
    intro a ha
    have haH := hAH ha
    rw [s.decomposition] at haH
    obtain ⟨w, hw, c, hc, rfl⟩ := mem_sup_of_normal_left.mp haH
    have hx : w * c ∈ centralizerModulo H T D := by
      refine mem_centralizerModulo_iff.mpr ⟨hAH ha, ?_⟩
      intro t ht
      apply hAT
      rw [commutator_comm]
      exact commutator_mem_commutator ht ha
    have hwT : w ∈ centralizerModulo H T D := by
      have hh := (centralizerModulo H T D).mul_mem hx
        ((centralizerModulo H T D).inv_mem (hCT T hc))
      simpa only [mul_inv_cancel_right] using hh
    have hwK : w ∈ centralizerModulo H K D := by
      refine mem_centralizerModulo_iff.mpr ⟨hWH hw, ?_⟩
      intro k hk
      apply (dual_coordinates_fixed_iff u d k ⟨w, hw⟩).mpr
      apply hfixed _ _ k hk
      intro t ht
      exact (dual_coordinates_fixed_iff u d t ⟨w, hw⟩).mp
        ((mem_centralizerModulo_iff.mp hwT).2 t ht)
    exact (centralizerModulo H K D).mul_mem hwK (hCT K hc)
  rw [commutator_comm]
  apply commutator_le.mpr
  intro k hk a ha
  exact (mem_centralizerModulo_iff.mp (hAK ha)).2 k hk

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.FirstPairing.StepThree.RankOne.FixedSection
