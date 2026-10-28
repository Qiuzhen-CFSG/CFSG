module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCore
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreInvolutionFusion
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreCentralFour
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreIntersectionSeeds
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.PointCoreConjugation
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SeedConjugateTypes

/-!
# The actual cubic fixed subgroup of the marked point core

A fixed noncentral involution would give an original intersection seed
normalized by the cubic. The cubic fixed-point theorem on that seed rules
it out. The actual central cyclic four is fixed by an odd-order actor;
multiplication by its generator toggles the two possible squares in the
point core. Hence the full fixed core is precisely this cyclic four.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private theorem line_cases (h : TypeAt z V) (q : G) (hq : q ∈ zpowers z) : q = 1 ∨ q = z := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, h.involution] at hq
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hq
  have hn2 : n < 2 := Finset.mem_range.mp hn
  interval_cases n <;> simp

private theorem fixed_involution (h : TypeAt z V) (t : G)
    (ht : t ∈ involutionCentralizer z) (ht3 : orderOf t = 3)
    (q : G) (hq : q ∈ (involutionCentralizer z).pCoreIn 2)
    (hq2 : orderOf q = 2) (hqt : Commute q t) : q = z := by
  by_contra hqz
  obtain ⟨g, hg⟩ := h.point_core_intersection_seed q hq hq2 hqz
  let U := V.map (MulAut.conj (g : G)).toMonoidHom
  have hgz : (g : G) * z * (g : G)⁻¹ = z := by
    rw [mem_centralizer_singleton_iff.mp g.property, mul_inv_cancel_right]
  have hU : TypeAt z U := by
    have hh := h.conj (g : G)
    rwa [hgz] at hh
  have htU : t ∈ normalizer (U : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change U.map (MulAut.conj t).toMonoidHom = U
    change (V.map (MulAut.conj (g : G)).toMonoidHom).map (MulAut.conj t).toMonoidHom = _
    rw [← hg, map_inf _ _ _ (MulAut.conj t).injective, pointCore_conjugate, pointCore_conjugate]
    have htz : t * z * t⁻¹ = z := by rw [mem_centralizer_singleton_iff.mp ht, mul_inv_cancel_right]
    have htq : t * q * t⁻¹ = q := by rw [hqt.eq.symm, mul_inv_cancel_right]
    rw [htz, htq]
    exact hg
  obtain ⟨Vq, hqT⟩ := h.exists_typeAt_of_isConj q (h.centralizer_core_involution_isConj q hq hq2)
  have hqq : q ∈ (involutionCentralizer q).pCoreIn 2 := by
    have hh := hqT.seed_le_core hqT.involution_mem_seed
    rwa [hqT.centralizer_fitting] at hh
  have hqU : q ∈ U := by
    change q ∈ V.map (MulAut.conj (g : G)).toMonoidHom
    rw [← hg]
    exact ⟨hq, hqq⟩
  have hfix : q ∈ zpowers z := hU.cubic_seed_fixed t ⟨ht, htU⟩ ht3 ▸
    (show q ∈ U ⊓ centralizer ({t} : Set G) from
      ⟨hqU, mem_centralizer_singleton_iff.mpr hqt.eq⟩)
  rcases line_cases h q hfix with hq1 | he
  · simp [hq1] at hq2
  · exact hqz he

private theorem cubic_central_four (h : TypeAt z V) (t c : G)
    (ht : t ∈ involutionCentralizer z) (ht3 : orderOf t = 3)
    (hc4 : orderOf c = 4)
    (hcZ : c ∈ (center ((involutionCentralizer z).pCoreIn 2)).map
      ((involutionCentralizer z).pCoreIn 2).subtype) : Commute c t := by
  by_contra hct
  have hn : ¬ Commute t c := fun hh => hct hh.symm
  have hi := h.point_core_central_four_inverted c hc4 hcZ t ht hn
  let α := MulAut.conj t
  have hi' : α c = c⁻¹ := hi
  have ht3' : t ^ 3 = 1 := ht3 ▸ pow_orderOf_eq_one t
  have he : α (α (α c)) = c := by
    change t * (t * (t * c * t⁻¹) * t⁻¹) * t⁻¹ = c
    calc
      _ = t ^ 3 * c * (t ^ 3)⁻¹ := by simp only [pow_succ, pow_zero]; group
      _ = c := by rw [ht3']; simp
  have hi2 : α (α c) = c := by rw [hi', map_inv, hi', inv_inv]
  rw [hi2, hi'] at he
  have hc2 : c ^ 2 = 1 := by
    calc
      c ^ 2 = c⁻¹ * c := by rw [pow_two, he]
      _ = 1 := inv_mul_cancel c
  have hd := orderOf_dvd_of_pow_eq_one hc2
  rw [hc4] at hd
  norm_num at hd

/-- Every original point-centralizer cubic fixes exactly the central
cyclic four in its actual point core, with an original square root retained. -/
theorem TypeAt.cubic_point_core_fixed (h : TypeAt z V) (t : G)
    (ht : t ∈ involutionCentralizer z) (ht3 : orderOf t = 3) :
    ∃ c : G, orderOf c = 4 ∧ c ^ 2 = z ∧
      c ∈ (center ((involutionCentralizer z).pCoreIn 2)).map
        ((involutionCentralizer z).pCoreIn 2).subtype ∧
      (involutionCentralizer z).pCoreIn 2 ⊓ centralizer ({t} : Set G) = zpowers c := by
  obtain ⟨c, hc4, hc2, hcZ, _⟩ := h.exists_point_core_central_four
  have hct := cubic_central_four h t c ht ht3 hc4 hcZ
  obtain ⟨cQ, hcQ, hec⟩ := hcZ
  have hc : c ∈ (involutionCentralizer z).pCoreIn 2 := hec ▸ cQ.property
  have hcomm (q : G) (hq : q ∈ (involutionCentralizer z).pCoreIn 2) : Commute q c := by
    rw [← hec]
    exact congrArg Subtype.val (mem_center_iff.mp hcQ ⟨q, hq⟩)
  have hsmall (q : G) (hq : q ∈ (involutionCentralizer z).pCoreIn 2)
      (hqt : Commute q t) (hq2 : q ^ 2 = 1) : q ∈ zpowers c := by
    by_cases hq1 : q = 1
    · exact hq1 ▸ one_mem _
    rw [fixed_involution h t ht ht3 q hq (orderOf_eq_prime hq2 hq1) hqt, ← hc2]
    exact pow_mem (mem_zpowers c) 2
  refine ⟨c, hc4, hc2, ⟨cQ, hcQ, hec⟩, le_antisymm ?_ ?_⟩
  · rintro q ⟨hq, hqt⟩
    have hqt' : Commute q t := mem_centralizer_singleton_iff.mp hqt
    rcases line_cases h (q ^ 2) (h.centralizer_core_square_mem q hq) with hq1 | hqz
    · exact hsmall q hq hqt' hq1
    · have hd : q * c⁻¹ ∈ (involutionCentralizer z).pCoreIn 2 := mul_mem hq (inv_mem hc)
      have hdt : Commute (q * c⁻¹) t := hqt'.mul_left hct.inv_left
      have hd2 : (q * c⁻¹) ^ 2 = 1 := by
        rw [(hcomm q hq).inv_right.mul_pow, inv_pow, hqz, hc2, mul_inv_cancel]
      have hh := (zpowers c).mul_mem (hsmall (q * c⁻¹) hd hdt hd2) (mem_zpowers c)
      simpa only [inv_mul_cancel_right] using hh
  · exact zpowers_le.mpr ⟨hc, mem_centralizer_singleton_iff.mpr hct.eq⟩

end CFSG.Quasithin.HigmanSims
