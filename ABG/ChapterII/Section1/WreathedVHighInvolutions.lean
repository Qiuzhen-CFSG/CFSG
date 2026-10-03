module
public import ABG.ChapterII.Section1.WreathedQuaternionCore
public import Theory.GroupTheory.SpecificGroups.QuaternionEightAut
public import ABG.ChapterII.Section1.WreathedVNormalizerRestriction

/-!
# Fusion between the outer and base involutions at high V index

If the canonical quaternion central product has outer automizer index six
in a finite ambient group, its noncentral base involution x2 is conjugate
to the outer involution z. This is the N(V) involution-fusion assertion
in Alperin--Brauer--Gorenstein, Chapter II Section 1 Proposition 2,
article p.12, `refs/latex/alperin-brauer-gorenstein-pages/page-013.tex`.

The normalizer realizes every automorphism of the characteristic quaternion
core and fixes the cyclic Sylow center pointwise. Choose an automorphism
taking the quaternion rotation r^quarter to d, using transitivity on the
six quaternion elements of order four. Since x2=r^quarter*u^quarter,
the resulting normalizer element sends x2 to d*u^quarter. This is an
outer involution and hence is conjugate to z within the Sylow subgroup.
All group elements and normalizers retain their actual ambient inclusions.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

include P in
private theorem quarter_double : 2 ^ (n-2) * 2 = 2 ^ (n-1) := by
  rw [← pow_succ]
  congr 1
  have := P.height
  omega

private theorem rotation_mul_center :
    P.r ^ (2 ^ (n-2)) * P.u ^ (2 ^ (n-2)) = P.x₂ := by
  have hst : Commute P.s P.t := P.commute
  have hr : Commute P.r P.u := (P.u_commute P.r).symm
  rw [← hr.mul_pow]
  have he : P.r * P.u = P.s ^ 2 := by
    simp only [r,u,pow_two]
    rw [mul_assoc, ← mul_assoc P.t⁻¹, hst.inv_right.symm.eq]
    group
  rw [he, ← pow_mul, mul_comm 2, P.quarter_double]
  rfl

private theorem c₁_isConj_z : IsConj (P.d * P.u ^ (2 ^ (n-2))) P.z := by
  apply P.outer_involution_isConj
  · intro h
    have hu : P.u ^ (2 ^ (n-2)) ∈ P.U := by
      apply P.U.pow_mem
      exact P.U.mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
    have hd : P.d ∈ P.U := by simpa using P.U.mul_mem h (P.U.inv_mem hu)
    have hx : P.x₂ ∈ P.U := P.U.pow_mem (Subgroup.subset_closure (by simp)) _
    have hz := P.U.mul_mem (P.U.inv_mem hx) hd
    exact P.z_not_mem_U (by simpa [d] using hz)
  · have hdu : Commute P.d (P.u ^ (2 ^ (n-2))) := (P.u_commute P.d).symm.pow_right _
    rw [hdu.mul_pow, P.d_sq, P.r_half, ← pow_mul, P.quarter_double]
    change P.x * P.x = 1
    rw [← pow_two, ← P.x_orderOf, pow_orderOf_eq_one]

end ABG.Wreathed.Presentation

namespace ABG.Wreathed
variable {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) {n : ℕ}
    (P : Presentation S n)

omit [Finite G] in
private theorem fusion_of_restriction
    (hfull : ∀ a : MulAut (P.quaternionCore.map (S : Subgroup G).subtype),
      ∃ g : G, g ∈ Subgroup.normalizer (P.V.map (S : Subgroup G).subtype : Set G) ∧
      ∀ q : P.quaternionCore.map (S : Subgroup G).subtype,
        g * (q : G) * g⁻¹ = (a q : G))
    (hfix : Subgroup.normalizer (P.V.map (S : Subgroup G).subtype : Set G) ≤
      Subgroup.centralizer ((Subgroup.center S).map (S : Subgroup G).subtype : Set G)) :
    IsConj (P.x₂ : G) (P.z : G) := by
  let Q := P.quaternionCore.map (S : Subgroup G).subtype
  have hr : P.r ^ (2 ^ (n-2)) ∈ P.quaternionCore := Subgroup.subset_closure (by simp)
  have hd : P.d ∈ P.quaternionCore := Subgroup.subset_closure (by simp)
  let a : Q := ⟨(P.r ^ (2 ^ (n-2)) : S), ⟨_,hr,rfl⟩⟩
  let b : Q := ⟨(P.d : G), ⟨_,hd,rfl⟩⟩
  obtain ⟨e₀⟩ := P.quaternion_core_model.1
  let e : Q ≃* QuaternionGroup 2 :=
    (P.quaternionCore.equivMapOfInjective (S : Subgroup G).subtype
      (S : Subgroup G).subtype_injective).symm.trans e₀
  have ha4 : orderOf a = 4 := by
    rw [← Subgroup.orderOf_coe]
    exact (orderOf_injective (S : Subgroup G).subtype
      (S : Subgroup G).subtype_injective _).trans P.quaternion_rotation_order
  have hd4 : orderOf P.d = 4 := by
    have hs : orderOf (P.d ^ 2) = 2 := by rw [P.d_sq, P.r_half, P.x_orderOf]
    have h4 : P.d ^ 4 = 1 := by
      rw [show 4 = 2*2 from rfl, pow_mul, P.d_sq, P.r_half]
      simpa only [P.x_orderOf] using pow_orderOf_eq_one P.x
    have hne : P.d ^ 2 ≠ 1 := by intro h; rw [h,orderOf_one] at hs; omega
    change orderOf P.d = 2 ^ 2
    apply orderOf_eq_prime_pow
    · simpa using hne
    · exact h4
  have hb4 : orderOf b = 4 := by
    rw [← Subgroup.orderOf_coe]
    exact (orderOf_injective (S : Subgroup G).subtype
      (S : Subgroup G).subtype_injective _).trans hd4
  obtain ⟨f,hf⟩ := QuaternionGroup.exists_mulAut_eq_of_orderOf_eq_four (e a) (e b)
    ((e.orderOf_eq a).trans ha4) ((e.orderOf_eq b).trans hb4)
  let alpha : MulAut Q := (MulAut.congr e.symm) f
  have hab : alpha a = b := by
    change e.symm (f (e a)) = b
    rw [hf,e.symm_apply_apply]
  obtain ⟨g,hg,hact⟩ := hfull alpha
  have hga : g * (P.r ^ (2 ^ (n-2)) : G) * g⁻¹ = (P.d : G) := by
    have h := hact a
    rw [hab] at h
    exact h
  have hu : (P.u ^ (2 ^ (n-2)) : G) ∈
      (Subgroup.center S).map (S : Subgroup G).subtype :=
    Subgroup.mem_map_of_mem _ ((Subgroup.center S).pow_mem P.u_mem_center _)
  have hgc : g * (P.u ^ (2 ^ (n-2)) : G) * g⁻¹ = (P.u ^ (2 ^ (n-2)) : G) := by
    have h := hfix hg _ hu
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]
  have hxc : IsConj (P.x₂ : G) ((P.d * P.u ^ (2 ^ (n-2)) : S) : G) := by
    apply isConj_iff.mpr
    refine ⟨g, ?_⟩
    rw [← P.rotation_mul_center]
    change g * ((P.r ^ (2 ^ (n-2)) : G) * (P.u ^ (2 ^ (n-2)) : G)) * g⁻¹ =
      (P.d : G) * (P.u ^ (2 ^ (n-2)) : G)
    calc
      _ = (g * (P.r ^ (2 ^ (n-2)) : G) * g⁻¹) *
          (g * (P.u ^ (2 ^ (n-2)) : G) * g⁻¹) := by group
      _ = _ := by rw [hga,hgc]
  obtain ⟨s,hs⟩ := isConj_iff.mp P.c₁_isConj_z
  apply hxc.trans
  exact isConj_iff.mpr ⟨(s : G), congrArg Subtype.val hs⟩

/-- A full outer automizer of the central product fuses the two noncentral involution types. -/
public theorem v_high_involution_fusion
    (hindex : outerAutomizerIndex (P.V.map (S : Subgroup G).subtype) = 6) :
    IsConj (P.x₂ : G) (P.z : G) := by
  apply fusion_of_restriction S P
  · exact canonical_v_restriction_surjective S P hindex
  · exact (canonical_v_normalizer_structure S P).2.1

end ABG.Wreathed
