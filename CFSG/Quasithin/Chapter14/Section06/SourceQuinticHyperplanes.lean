module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticReciprocity
public import CFSG.Quasithin.ChapterF.Section09.Intersections
public import Theory.GroupTheory.SubgroupPartitionCounting

/-!
# Reciprocal core hyperplanes in the original quintic source

The full quotient H/O₂(H) is D₁₀ or Sz(2), so an elementary two-subgroup
has image of order at most two. Critical escape makes that image nontrivial.
The same reverse endpoint restores every H-normalized label and transports
the index to the opposite intersection. Distinct point lines make these
two core intersections commute. Their orders are both sixteen or both
thirty-two, retaining both original closure sizes and the FullRee option.

Source: Aschbacher--Smith F.9.6(3), F.9.13--17, printed pp.320--324,
and14.2.21, printed p.988, in refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06

private theorem elementary_bound_of_cyclic_sylows
    {K : Type*} [Group K] [Finite K]
    (hcyc : ∀ P : Sylow 2 K, IsCyclic P)
    (E : Subgroup K) [IsElementaryAbelian 2 E] : Nat.card E ≤ 2 := by
  obtain ⟨P,hEP⟩ := (IsElementaryAbelian.isPGroup 2 E).exists_le_sylow
  let : IsCyclic P := hcyc P
  let : IsCyclic E := isCyclic_of_injective (inclusion hEP) (inclusion_injective hEP)
  apply Nat.le_of_dvd (by decide)
  rw [←IsCyclic.exponent_eq_card]
  exact IsElementaryAbelian.exponent_dvd_p 2 E

private theorem quintic_elementary_bound
    {K : Type*} [Group K] [Finite K]
    (hm : Nonempty (K ≃* DihedralGroup 5) ∨
      Nonempty (K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0))
    (E : Subgroup K) [IsElementaryAbelian 2 E] : Nat.card E ≤ 2 := by
  rcases hm with he | he
  · obtain ⟨e⟩ := he
    let B := E.map e.toMonoidHom
    let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
    have hc : Nat.card B ≤ 2 := by
      apply elementary_bound_of_cyclic_sylows
      intro P
      let R : Sylow 2 (DihedralGroup 5) := Sylow.ofCard
        (zpowers (DihedralGroup.sr 0)) (by
          rw [Nat.card_zpowers,DihedralGroup.orderOf_sr,DihedralGroup.nat_card]
          decide +kernel)
      let : IsCyclic R := inferInstanceAs (IsCyclic (zpowers (DihedralGroup.sr 0)))
      exact isCyclic_of_injective (P.equiv R).toMonoidHom (P.equiv R).injective
    exact (card_map_of_injective e.injective).symm.trans_le hc
  · obtain ⟨e⟩ := he
    let B := E.map e.toMonoidHom
    let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
    have hc : Nat.card B ≤ 2 := by
      apply elementary_bound_of_cyclic_sylows
      intro P
      let R : Sylow 2 (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) := Sylow.ofCard
        (zpowers BenderSuzuki.MatrixGroups.suzukiZeroRootGenerator) (by
          rw [Nat.card_zpowers,BenderSuzuki.MatrixGroups.suzukiZeroRootGenerator_order,
            BenderSuzuki.MatrixGroups.suzukiZero_card]
          decide +kernel)
      let : IsCyclic R := inferInstanceAs
        (IsCyclic (zpowers BenderSuzuki.MatrixGroups.suzukiZeroRootGenerator))
      exact isCyclic_of_injective (P.equiv R).toMonoidHom (P.equiv R).injective
    exact (card_map_of_injective e.injective).symm.trans_le hc

variable {G : Type*} [Group G] [Finite G]

private theorem quintic_critical_image
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH]
    (hm : Nonempty ((D.H ⧸ pCore 2 D.H) ≃* DihedralGroup 5) ∨
      Nonempty ((D.H ⧸ pCore 2 D.H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0))
    (hUV : D.UH = D.VH) (hb : 3 ≤ h.b) (i : h.CriticalEndpoint) :
    Nat.card (((i.conjugate D.UH).subgroupOf D.H).map (QuotientGroup.mk' (pCore 2 D.H))) = 2 ∧
      (i.conjugate D.UH ⊓ D.QH).relIndex (i.conjugate D.UH) = 2 := by
  let A := i.conjugate D.UH
  have hAH : A ≤ D.H := by simpa only [A,hUV] using i.large_le hb
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let B := A.subgroupOf D.H
  let q := QuotientGroup.mk' (pCore 2 D.H)
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAH
  let : IsElementaryAbelian 2 (B.map q) := IsElementaryAbelian.map q
  have hne : B.map q ≠ ⊥ := by
    intro hz
    have hBQ : B ≤ pCore 2 D.H := by
      rw [←QuotientGroup.ker_mk' (pCore 2 D.H)]
      exact (Subgroup.map_eq_bot_iff B).mp hz
    have hAQ : A ≤ D.QH := by
      intro x hx
      exact ⟨⟨x,hAH hx⟩,hBQ hx,rfl⟩
    exact ChapterF.Section09.Setup.Hypothesis.CriticalEndpoint.not_le_core_of_quintic
      h hm hUV i hb hAQ
  have hc : Nat.card (B.map q) = 2 := by
    have hbnd := quintic_elementary_bound hm (B.map q)
    have hp : 0 < Nat.card (B.map q) := Nat.card_pos
    have h1 : Nat.card (B.map q) ≠ 1 := fun hh => hne (card_eq_one.mp hh)
    omega
  refine ⟨hc,?_⟩
  have hi := relIndex_ker B q
  rw [QuotientGroup.ker_mk',hc] at hi
  have hh := relIndex_map_map_of_injective (pCore 2 D.H) B D.H.subtype_injective
  rw [map_subgroupOf_eq_of_le hAH] at hh
  change D.QH.relIndex A = (pCore 2 D.H).relIndex B at hh
  exact (inf_relIndex_left A D.QH).trans (hh.trans hi)

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

/-- Every original quintic critical endpoint has reciprocal commuting core
hyperplanes, each of order sixteen or each of order thirty-two. The one
reverse conjugator restores every original H-normalized subgroup. -/
theorem source_quintic_reciprocal_core_hyperplanes
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let D : ChapterF.Section09.Setup G :=
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
    let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH.1
    3 ≤ h.b ∧ Odd h.b ∧ Nonempty h.CriticalEndpoint ∧
    ∀ i : h.CriticalEndpoint, ∃ j : h.CriticalEndpoint,
      (∀ A : Subgroup G, H ≤ normalizer (A : Set G) →
        (i.conjugate A).map (MulAut.conj j.representative).toMonoidHom = A) ∧
      D.V₁ ≠ i.conjugate D.V₁ ∧
      Nat.card (((i.conjugate D.UH).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 2 ∧
      (D.UH ⊓ i.conjugate D.QH).relIndex D.UH = 2 ∧
      (i.conjugate D.UH ⊓ D.QH).relIndex (i.conjugate D.UH) = 2 ∧
      ⁅D.UH ⊓ i.conjugate D.QH,i.conjugate D.UH ⊓ D.QH⁆ = ⊥ ∧
      ((Nat.card (D.UH ⊓ i.conjugate D.QH : Subgroup G) = 16 ∧
        Nat.card (i.conjugate D.UH ⊓ D.QH : Subgroup G) = 16) ∨
       (Nat.card (D.UH ⊓ i.conjugate D.QH : Subgroup G) = 32 ∧
        Nat.card (i.conjugate D.UH ⊓ D.QH : Subgroup G) = 32)) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab H hH.1
  obtain ⟨hb,ho,hnon⟩ := source_rankTwo_critical_track_bounds hG T hempty hM hu hmany hcard e hab H hH.1
  obtain ⟨he,hsize⟩ := Section02.SolvableAmalgam.source_index_five_closure_structure
    hG T hempty hM hu hmany hcard e H hH.1 hi
  let : IsElementaryAbelian 2 D.UH := he
  have hm := Section02.SolvableAmalgam.source_index_five_models
    hG T hempty hM hu hmany hcard e H hH.1 hi
  change 3 ≤ h.b ∧ Odd h.b ∧ Nonempty h.CriticalEndpoint ∧ _
  refine ⟨hb,ho,hnon,?_⟩
  intro i
  have hescape := ChapterF.Section09.Setup.Hypothesis.CriticalEndpoint.not_le_core_of_quintic
    h hm rfl i hb
  obtain ⟨j,hj⟩ := i.reverse_labels hb hescape
  have hQN : H ≤ normalizer (D.QH : Set G) :=
    ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D := D)
  obtain ⟨himage,hiidx⟩ := quintic_critical_image h hm rfl hb i
  have hjidx := (quintic_critical_image h hm rfl hb j).2
  have hmap := relIndex_map_map_of_injective (f := (MulAut.conj j.representative).toMonoidHom)
    (D.UH ⊓ i.conjugate D.QH) D.UH (MulAut.conj j.representative).injective
  rw [map_inf _ _ _ (MulAut.conj j.representative).injective,hj D.QH hQN] at hmap
  have hiidx' : (D.UH ⊓ i.conjugate D.QH).relIndex D.UH = 2 := hmap.symm.trans hjidx
  obtain ⟨_,_,hMc,_⟩ := plane_ordering_and_overgroups
    hG T hempty hM hu hmany hcard h.point_card
  have hHMc : H ≤ Mc := h.H_centralizes.trans_eq hMc.symm
  have hpoint : D.V₁ ≠ i.conjugate D.V₁ := by
    intro hp
    have hg : i.representative ∈ Mc :=
      hMc.ge (normalizer_le_centralizer_of_card_two D.V₁ h.point_card
        (mem_normalizer_iff_map_conj_eq.mpr hp.symm))
    let W := conjugateSpanBy (localModule T M) Mc
    let : IsMulCommutative W := hab
    have hUW : D.UH ≤ W := conjugateSpanBy_mono le_rfl hHMc
    have hgW : i.conjugate D.UH ≤ W :=
      (map_mono (f := (MulAut.conj i.representative).toMonoidHom) hUW).trans
        (mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy _ _ hg)).le
    have hc : ⁅i.conjugate D.UH,D.V⁆ = ⊥ := by
      apply commutator_eq_bot_iff_le_centralizer.mpr
      exact hgW.trans ((le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (centralizer_le (show D.V ≤ W from le_conjugateSpanBy _ _)))
    exact i.noncentral (hc ▸ bot_le)
  have hcomm : ⁅D.UH ⊓ i.conjugate D.QH,i.conjugate D.UH ⊓ D.QH⁆ = ⊥ := by
    have hc := h.lemma_F_9_6_three (g := i.representative⁻¹) (by
      simpa only [ChapterF.Section09.Setup.conjugate,ChapterG.Section02.Setup.conjugate,
        inv_inv] using hpoint)
    simpa only [ChapterF.Section09.Setup.DH,ChapterF.Section09.Setup.DHg,
      ChapterF.Section09.Setup.conjugate,ChapterG.Section02.Setup.conjugate,inv_inv] using hc.2
  have hleft := relIndex_mul_card_of_le
    (show D.UH ⊓ i.conjugate D.QH ≤ D.UH from inf_le_left)
  have hright := relIndex_mul_card_of_le
    (show i.conjugate D.UH ⊓ D.QH ≤ i.conjugate D.UH from inf_le_left)
  rw [hiidx'] at hleft
  rw [hiidx,card_map_of_injective (MulAut.conj i.representative).injective] at hright
  refine ⟨j,hj,hpoint,himage,hiidx',hiidx,hcomm,?_⟩
  change Nat.card D.UH = 32 ∨ Nat.card D.UH = 64 at hsize
  rcases hsize with hs | hs
  · exact Or.inl ⟨Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (hleft.trans hs),
      Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (hright.trans hs)⟩
  · exact Or.inr ⟨Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (hleft.trans hs),
      Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (hright.trans hs)⟩

end CFSG.Quasithin.Chapter14.Section06
