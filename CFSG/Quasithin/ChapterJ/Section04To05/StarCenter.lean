module

public import CFSG.Quasithin.ChapterJ.Section04To05.Setup.Flag
public import Theory.SpecificGroups.SymmetricFiveSylow
public import Theory.GroupTheory.DihedralGeneratedFactor

/-!
# The center of the original Sylow image in J.4

The selected four-group has exactly two elements outside Z. The original
Q-action interchanges them, by the proved equality C_U(Q)=Z. Consequently
every T-star element has a lift centralizing the selected conjugate point.
These lifts normalize Uα; its order-two image is therefore centralized by
T-star. The dihedral Sylow center has order two, giving the exact center.
The actual chosen v has nontrivial image and generates that center.

Source: Aschbacher–Smith, J.4.1(1), printed p.440.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
noncomputable section
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} {p : Plane d}

private theorem complement_two_cases (A Z : Subgroup G) (hZA : Z ≤ A)
    (hA : Nat.card A = 4) (hZ : Nat.card Z = 2)
    (x y w : G) (hx : x ∈ A) (hy : y ∈ A) (hw : w ∈ A)
    (hxZ : x ∉ Z) (hyZ : y ∉ Z) (hwZ : w ∉ Z) (hxy : x ≠ y) :
    w = x ∨ w = y := by
  classical
  let X := {a : A // (a : G) ∉ Z}
  have hi : Nat.card {a : A // (a : G) ∈ Z} = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZA).toEquiv).trans hZ
  have hc : Nat.card X = 2 := by
    let := Fintype.ofFinite A
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
    rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,hA,hi]
  let a : X := ⟨⟨x,hx⟩,hxZ⟩
  let b : X := ⟨⟨y,hy⟩,hyZ⟩
  let c : X := ⟨⟨w,hw⟩,hwZ⟩
  obtain ⟨z,hzne,huniq⟩ := (Nat.card_eq_two_iff' a).mp hc
  have hb : b ≠ a := fun h => hxy (congrArg (fun t : X => (t.val : G)) h).symm
  by_cases he : c = a
  · exact Or.inl (congrArg (fun t : X => (t.val : G)) he)
  · exact Or.inr (congrArg (fun t : X => (t.val : G))
      ((huniq c he).trans (huniq b hb).symm))

private theorem Q_le_T (d : LocalSetup G) : d.toTypeRuSetup.Q ≤ (d.T : Subgroup G) := by
  have h := pCoreIn_le_sylow (p := 2) d.toTypeRuSetup.H (d.T.subtype d.toTypeRuSetup.T_le_H)
  change d.toTypeRuSetup.Q ≤
    ((d.T : Subgroup G).subgroupOf d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype at h
  rwa [map_subgroupOf_eq_of_le d.toTypeRuSetup.T_le_H] at h

private theorem conj_outside_Z (t : G) (ht : t ∈ d.toTypeRuSetup.H)
    (z : G) (hz : z ∉ d.toTypeRuSetup.Z) : t*z*t⁻¹ ∉ d.toTypeRuSetup.Z := by
  intro h
  have hcomm := ht (t*z*t⁻¹) h
  have he : t*z*t⁻¹ = z := by
    apply (MulAut.conj t).injective
    change t*(t*z*t⁻¹)*t⁻¹ = t*z*t⁻¹
    calc
      t*(t*z*t⁻¹)*t⁻¹ = (t*z*t⁻¹)*t*t⁻¹ := by rw [hcomm]
      _ = t*z*t⁻¹ := mul_inv_cancel_right _ _
  exact hz (he ▸ h)

/-- Every original Sylow-star element has a lift centralizing the selected point. -/
theorem SourceChoice.centralizer_lift (s : SourceChoice p) (t : d.toTypeRuSetup.H)
    (ht : (t : G) ∈ d.T) :
    ∃ c : d.toTypeRuSetup.H,
      (c : G) ∈ centralizer
        (d.toTypeRuSetup.Z.map (MulAut.conj s.g).toMonoidHom : Set G) ∧
      d.ru2.quotientMap c = d.ru2.quotientMap t := by
  obtain ⟨z,hzα,hzZ⟩ := Set.not_subset.mp s.conjugate_point_not_le
  have hzP := s.conjugate_point_le hzα
  have hzU := le_conjugateSpan d.toTypeRuSetup.H d.V (p.le_seed hzP)
  have hq : ∃ q ∈ d.toTypeRuSetup.Q, q*z ≠ z*q := by
    by_contra h
    push Not at h
    apply hzZ
    rw [← d.centralizer_Q_inf_U]
    exact ⟨hzU,h⟩
  obtain ⟨q,hq,hqne⟩ := hq
  have hqT := Q_le_T d hq
  have hqH := d.toTypeRuSetup.T_le_H hqT
  have hqP := (mem_normalizer_iff.mp (p.normalized hqT) z).mp hzP
  have hqZ := conj_outside_Z q hqH z hzZ
  have hqz : z ≠ q*z*q⁻¹ := by
    intro h
    exact hqne (mul_inv_eq_iff_eq_mul.mp h.symm)
  have htP := (mem_normalizer_iff.mp (p.normalized ht) z).mp hzP
  have htZ := conj_outside_Z (t : G) t.property z hzZ
  have hgen : zpowers z = d.toTypeRuSetup.Z.map (MulAut.conj s.g).toMonoidHom := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr hzα)
    have hn : Nontrivial (zpowers z) :=
      (nontrivial_iff_ne_bot _).mpr (fun h => hzZ (by
        have hz1 : z=1 := by simpa only [h,mem_bot] using mem_zpowers z
        rw [hz1]; exact one_mem _))
    rw [card_map_of_injective (MulAut.conj s.g).injective,d.card_Z]
    exact Nat.succ_le_of_lt (Finite.one_lt_card)
  have hcentral (c : G) (he : c*z*c⁻¹=z) :
      c ∈ centralizer
        (d.toTypeRuSetup.Z.map (MulAut.conj s.g).toMonoidHom : Set G) := by
    rw [← hgen,zpowers_eq_closure,centralizer_closure,mem_centralizer_singleton_iff]
    exact mul_inv_eq_iff_eq_mul.mp he
  rcases complement_two_cases p.group d.toTypeRuSetup.Z p.point_le p.card d.card_Z
    z (q*z*q⁻¹) ((t:G)*z*(t:G)⁻¹) hzP hqP htP hzZ hqZ htZ hqz with h | h
  · exact ⟨t,hcentral t h,rfl⟩
  · let c : d.toTypeRuSetup.H := ⟨q⁻¹*t,
      d.toTypeRuSetup.H.mul_mem (d.toTypeRuSetup.H.inv_mem hqH) t.property⟩
    refine ⟨c,hcentral c ?_,?_⟩
    · change (q⁻¹*(t:G))*z*(q⁻¹*(t:G))⁻¹=z
      calc
        (q⁻¹*(t:G))*z*(q⁻¹*(t:G))⁻¹ = q⁻¹*((t:G)*z*(t:G)⁻¹)*q := by group
        _ = z := by rw [h]; group
    · have hq1 : d.ru2.quotientMap ⟨q,hqH⟩ = 1 := by
        change (⟨q,hqH⟩ : d.toTypeRuSetup.H) ∈ d.ru2.quotientMap.ker
        rw [d.ru2.quotient_kernel]
        exact hq
      change d.ru2.quotientMap ((⟨q,hqH⟩ : d.toTypeRuSetup.H)⁻¹*t) = _
      rw [map_mul,map_inv,hq1,inv_one,one_mul]
def SourceChoice.starPoint (s : SourceChoice p) : Subgroup S5 :=
  ((d.toTypeRuSetup.U.map (MulAut.conj s.g).toMonoidHom).subgroupOf
    d.toTypeRuSetup.H).map d.ru2.quotientMap

def SourceChoice.starInvolution (s : SourceChoice p) : S5 :=
  d.ru2.quotientMap ⟨s.v,(s.conjugate_properties p).1 s.v_mem⟩

theorem SourceChoice.starPoint_eq_image (s : SourceChoice p) : s.starPoint =
    ((d.toTypeRuSetup.U.map (MulAut.conj s.g).toMonoidHom).subgroupOf
      d.toTypeRuSetup.H).map d.ru2.quotientMap := by rfl

theorem SourceChoice.starInvolution_eq (s : SourceChoice p) : s.starInvolution =
    d.ru2.quotientMap ⟨s.v,(s.conjugate_properties p).1 s.v_mem⟩ := by rfl

theorem SourceChoice.starPoint_card (s : SourceChoice p) : Nat.card s.starPoint = 2 :=
  (s.conjugate_properties p).2.1

theorem SourceChoice.starPoint_le_star (s : SourceChoice p) : s.starPoint ≤
    ((d.T : Subgroup G).subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap := by
  apply map_mono
  intro u hu
  exact d.S_le_T (ConjugateIntersections.conjugateU_le_S d s.g
    (p.L₂_le_L s.in_residual) hu)

theorem SourceChoice.star_normalizes_starPoint (s : SourceChoice p) :
    ((d.T : Subgroup G).subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap ≤
      normalizer (s.starPoint : Set S5) := by
  rintro x ⟨t,ht,rfl⟩
  obtain ⟨c,hc,he⟩ := s.centralizer_lift t ht
  rw [← he]
  apply le_normalizer_map d.ru2.quotientMap
  apply mem_map_of_mem
  apply le_normalizer_comap d.toTypeRuSetup.H.subtype
  exact ConjugateIntersections.conjugateU_normalized d s.g hc

theorem SourceChoice.starPoint_eq_center (s : SourceChoice p) : s.starPoint =
    centerIn (((d.T : Subgroup G).subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap) := by
  let P := (d.T.subtype d.toTypeRuSetup.T_le_H).mapSurjective d.ru2.quotient_surjective
  have hcoe : (P : Subgroup S5) =
      ((d.T : Subgroup G).subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap := rfl
  have hc : Nat.card (centerIn (P : Subgroup S5)) = 2 := by
    obtain ⟨e⟩ := Equiv.Perm.sylow_two_equiv_dihedral_five P
    rw [centerIn_eq_map_center,card_map_of_injective (P : Subgroup S5).subtype_injective]
    exact DihedralGroup.center_card_of_equiv (n := 2) (by decide) e
  apply eq_of_le_of_card_ge
  · apply le_inf s.starPoint_le_star
    apply le_centralizer_iff.mpr
    exact s.star_normalizes_starPoint.trans
      (normalizer_le_centralizer_of_card_two s.starPoint s.starPoint_card)
  · rw [← hcoe,hc,s.starPoint_card]

theorem SourceChoice.starInvolution_ne_one (s : SourceChoice p) :
    s.starInvolution ≠ 1 := by
  intro h
  have hm : (⟨s.v,(s.conjugate_properties p).1 s.v_mem⟩ : d.toTypeRuSetup.H) ∈
      d.ru2.quotientMap.ker := h
  rw [d.ru2.quotient_kernel] at hm
  exact s.v_not_Q hm

theorem SourceChoice.starInvolution_mem (s : SourceChoice p) :
    s.starInvolution ∈ s.starPoint :=
  ⟨⟨s.v,(s.conjugate_properties p).1 s.v_mem⟩,s.v_mem,rfl⟩

theorem SourceChoice.starInvolution_generates (s : SourceChoice p) :
    zpowers s.starInvolution = s.starPoint := by
  apply eq_of_le_of_card_ge (zpowers_le.mpr s.starInvolution_mem)
  have hn : Nontrivial (zpowers s.starInvolution) :=
    (nontrivial_iff_ne_bot _).mpr (fun h => s.starInvolution_ne_one (by
      simpa only [h,mem_bot] using mem_zpowers s.starInvolution))
  rw [s.starPoint_card]
  exact Nat.succ_le_of_lt Finite.one_lt_card

theorem SourceChoice.starInvolution_order (s : SourceChoice p) :
    orderOf s.starInvolution = 2 := by
  rw [← Nat.card_zpowers,s.starInvolution_generates,s.starPoint_card]

end
end CFSG.Quasithin.ChapterJ.RuSubgroup
