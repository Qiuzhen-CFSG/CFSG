module

public import Theory.SpecificGroups.Suzuki.InvolutionOrbit

/-!
# Root intersections at subgroup involution points

At a point fixed by an involution of `H`, the intersection of `H` with the
ambient root group is a Sylow 2-subgroup of `H`. Indeed, extend a 2-subgroup
containing that involution to an ambient Sylow group. Its unique fixed point
is the given point, so the ambient Sylow group is the root group there.

This is local geometry for the subgroup argument in Huppert--Blackburn,
*Finite Groups III*, XI.3.12(e). It does not assert that the root intersection
is transitive on the other subgroup involution points.
-/

namespace BenderSuzuki.MatrixGroups

private theorem map_conj_eq_of_inv_mul_mem_normalizer
    {G : Type*} [Group G] (U : Subgroup G) (k l : G)
    (hn : l⁻¹ * k ∈ Subgroup.normalizer U) :
    U.map (MulAut.conj k).toMonoidHom = U.map (MulAut.conj l).toMonoidHom := by
  have heq : U.map (MulAut.conj (l⁻¹ * k)).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hcomp : (MulAut.conj l).toMonoidHom.comp
      (MulAut.conj (l⁻¹ * k)).toMonoidHom = (MulAut.conj k).toMonoidHom := by
    apply MonoidHom.ext
    intro x
    change l * ((l⁻¹ * k) * x * (l⁻¹ * k)⁻¹) * l⁻¹ = k * x * k⁻¹
    group
  have h := congrArg (fun P : Subgroup G =>
    P.map (MulAut.conj l).toMonoidHom) heq
  rw [Subgroup.map_map] at h
  rw [hcomp] at h
  exact h

/-- A nonidentity conjugate root element fixes only the corresponding
conjugate of infinity. -/
public theorem suzukiRootSubgroup_conjugate_fixed_iff
    {m : ℕ} (hm : 0 < m) (k g : SuzukiMatrixGroup m)
    (hg : g ∈ (SuzukiRootSubgroup m).map (MulAut.conj k).toMonoidHom)
    (hgne : g ≠ 1) (a : SuzukiOvoid m) :
    g • a = a ↔ a = k • suzukiOvoidInfinity m := by
  obtain ⟨u, hu, heq⟩ := hg
  change k * u * k⁻¹ = g at heq
  have hune : u ≠ 1 := by
    rintro rfl
    apply hgne
    simpa using heq.symm
  constructor
  · intro ha
    have hfix : u • (k⁻¹ • a) = k⁻¹ • a := by
      rw [← heq] at ha
      have h := congrArg (fun x : SuzukiOvoid m => k⁻¹ • x) ha
      simpa only [mul_smul, inv_smul_smul] using h
    have h := (suzukiRootSubgroup_fixed_iff m hm u hu hune _).mp hfix
    exact (inv_smul_eq_iff.mp h)
  · rintro rfl
    rw [← heq]
    simp only [mul_smul, inv_smul_smul, suzukiRootSubgroup_fix_infinity m hm u hu]

/-- Conjugate root groups depend only on their distinguished fixed point. -/
public theorem suzukiRootSubgroup_conjugate_eq_of_smul_eq
    {m : ℕ} (hm : 0 < m) (k l : SuzukiMatrixGroup m)
    (hkl : k • suzukiOvoidInfinity m = l • suzukiOvoidInfinity m) :
    (SuzukiRootSubgroup m).map (MulAut.conj k).toMonoidHom =
      (SuzukiRootSubgroup m).map (MulAut.conj l).toMonoidHom := by
  apply map_conj_eq_of_inv_mul_mem_normalizer
  rw [suzukiRootSubgroup_normalizer m hm,
    suzukiBorelSubgroup_eq_stabilizer m hm, MulAction.mem_stabilizer_iff]
  rw [mul_smul, hkl, inv_smul_smul]

/-- A 2-subgroup containing an involution lies in the root group at that
involution's fixed point. -/
public theorem suzukiTwoSubgroup_le_conjugate_root
    {m : ℕ} (hm : 0 < m) (P : Subgroup (SuzukiMatrixGroup m))
    (hP : IsPGroup 2 P) (t : SuzukiMatrixGroup m) (htP : t ∈ P)
    (ht : orderOf t = 2) (a : SuzukiOvoid m) (hta : t • a = a)
    (k : SuzukiMatrixGroup m) (hk : k • suzukiOvoidInfinity m = a) :
    P ≤ (SuzukiRootSubgroup m).map (MulAut.conj k).toMonoidHom := by
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨U, hU⟩ := suzukiRootSubgroup_isSylow m hm
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq (SuzukiMatrixGroup m) U Q
  have hQl : (Q : Subgroup (SuzukiMatrixGroup m)) =
      (SuzukiRootSubgroup m).map (MulAut.conj l).toMonoidHom := by
    rw [← hl, ← hU]
    rfl
  have htl : t • (l • suzukiOvoidInfinity m) = l • suzukiOvoidInfinity m := by
    have hmem : t ∈ (SuzukiRootSubgroup m).map (MulAut.conj l).toMonoidHom :=
      hQl ▸ hPQ htP
    obtain ⟨u, hu, heq⟩ := hmem
    change l * u * l⁻¹ = t at heq
    rw [← heq]
    simp only [mul_smul, inv_smul_smul,
      suzukiRootSubgroup_fix_infinity m hm u hu]
  obtain ⟨b, _, hb⟩ := suzukiOvoid_involution_unique_fixed m hm t ht
  have hlk : l • suzukiOvoidInfinity m = k • suzukiOvoidInfinity m :=
    (hb _ htl).trans ((hb _ hta).symm.trans hk.symm)
  rw [← suzukiRootSubgroup_conjugate_eq_of_smul_eq hm l k hlk, ← hQl]
  exact hPQ

/-- At a subgroup involution point, the root intersection is a Sylow
2-subgroup of the subgroup. -/
public theorem suzukiSubgroup_root_intersection_isSylow
    {m : ℕ} (hm : 0 < m) (H : Subgroup (SuzukiMatrixGroup m))
    (a : suzukiInvolutionSubaction H) (k : SuzukiMatrixGroup m)
    (hk : k • suzukiOvoidInfinity m = a.val) :
    ∃ P : Sylow 2 H,
      (P : Subgroup H) =
        ((SuzukiRootSubgroup m).map (MulAut.conj k).toMonoidHom).subgroupOf H := by
  let R := ((SuzukiRootSubgroup m).map (MulAut.conj k).toMonoidHom).subgroupOf H
  obtain ⟨t, ht, hta⟩ := a.property
  have htG : orderOf (t : SuzukiMatrixGroup m) = 2 :=
    (Subgroup.orderOf_coe t).trans ht
  have htp : IsPGroup 2 (Subgroup.zpowers (t : SuzukiMatrixGroup m)) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    rw [Nat.card_zpowers, htG]
    exact dvd_refl 2
  have htR : t ∈ R :=
    suzukiTwoSubgroup_le_conjugate_root hm _ htp t
      (Subgroup.mem_zpowers _) htG a.val hta k hk (Subgroup.mem_zpowers _)
  have hR : IsPGroup 2 R :=
    ((suzukiRootSubgroup_isPGroup m hm).map
      (MulAut.conj k).toMonoidHom).comap_subtype
  obtain ⟨P, hRP⟩ := hR.exists_le_sylow
  refine ⟨P, le_antisymm ?_ hRP⟩
  intro u hu
  exact suzukiTwoSubgroup_le_conjugate_root hm
    ((P : Subgroup H).map H.subtype) (P.isPGroup'.map H.subtype) t
    ⟨t, hRP htR, rfl⟩ htG a.val hta k hk ⟨u, hu, rfl⟩

end BenderSuzuki.MatrixGroups
