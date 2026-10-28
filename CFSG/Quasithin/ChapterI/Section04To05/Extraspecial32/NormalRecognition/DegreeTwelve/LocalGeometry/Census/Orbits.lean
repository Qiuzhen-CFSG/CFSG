module

public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.LocalData
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.Census.Orbits.CoreOrbit
public import Theory.GroupTheory.QuaternionCentralProductC2Rank
public import Theory.GroupTheory.NormalSubgroupInvolutionFiber

/-!
# The local involution orbit profile in the normal-quaternion case

Both actions of H/Q on the three nonzero points of a quaternion quotient
plane contain a cubic. Since H/Q is the actual symmetric group of degree
three, these actions are faithful. Thus an element outside Q acts outerly
on both quaternion factors. The quaternion cocycle calculation shows that
Q is transitive on the involutions in each outside coset. Conjugacy in the
symmetric-three quotient joins those cosets into one H-orbit.

Together with the complementary twelve-element core orbit, this constructs
the exact OrbitData used by the involution census. No ambient two-class
coverage or product count is assumed.

Source: M. Aschbacher, “A 2-local characterization of M12”, Illinois J.
Math. 47 (2003), 31–47, Lemmas 2.3 and 2.7(1)–(3).
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.Census
open Subgroup Theory.GroupTheory Subgroup.QuaternionCentralProductData
variable {G : Type*} [Group G] [Finite G] {z : G}

private theorem factorAction_injective (h : Hypotheses z) (hn : QuaternionSubgroupsNormal z)
    (q : QuaternionCentralProductData (Core z))
    (R : Subgroup (Core z)) (hR : R = q.left ∨ R = q.right) :
    Function.Injective (h.localOrbit_factorAction hn q R hR) := by
  let e := q.factorPointsEquivFin R hR
  let E := h.quotient_model.some
  let f := e.permCongrHom.toMonoidHom.comp (h.localOrbit_factorAction hn q R hR)
  obtain ⟨c, hc⟩ := Theory.GroupAction.SymmetricThreeDiagonalGrid.endomorphism_inner
    (f.comp E.symm.toMonoidHom) (by
      obtain ⟨a, ha⟩ := h.localOrbit_factorAction_three hn q R hR
      exact ⟨E a, by simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.symm_apply_apply, f] using (e.permCongrHom.orderOf_eq _).trans ha⟩)
  intro x y hxy
  apply E.injective
  apply (MulAut.conj c).injective
  change c * E x * c⁻¹ = c * E y * c⁻¹
  rw [← hc, ← hc]
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  exact congrArg e.permCongrHom hxy

/-- Every element outside the core acts outerly on each quaternion factor. -/
public theorem bothOuter_of_not_core (h : Hypotheses z) (hn : QuaternionSubgroupsNormal z)
    (q : QuaternionCentralProductData (Core z)) (t : Centralizer z) (ht : t ∉ Core z) :
    q.BothOuter (MulAut.conjNormal t) := by
  have hmaps := h.localOrbit_factor_preserved hn q t
  have hout (R : Subgroup (Core z)) (hR : R = q.left ∨ R = q.right) :
      ¬ ∃ b : R, ∀ x : R,
        MulAut.conjNormal t (x : Core z) = (b : Core z) * x * (b : Core z)⁻¹ := by
    rintro ⟨b, hb⟩
    let f := h.localOrbit_factorAction hn q R hR
    have he : f (QuotientGroup.mk' (Core z) t) = 1 := by
      ext v
      rw [h.localOrbit_factorAction_mk_val]
      obtain ⟨r, hr, her⟩ := v.val.property
      rw [← her, quotientAut_apply_mk, hb ⟨r, hr⟩]
      let _ := q.quotient_elementary
      let _ : CommGroup (Core z ⧸ center (Core z)) := IsMulCommutative.instCommGroup
      rw [map_mul, map_mul, map_inv, mul_comm (QuotientGroup.mk' (center (Core z)) (b : Core z)),
        mul_inv_cancel_right]
      exact her
    have ht1 : QuotientGroup.mk' (Core z) t = 1 :=
      factorAction_injective h hn q R hR (he.trans (map_one f).symm)
    exact ht ((QuotientGroup.eq_one_iff t).mp ht1)
  exact ⟨hmaps.1, hmaps.2, hout _ (Or.inl rfl), hout _ (Or.inr rfl)⟩

private theorem s3_involutions_conj : ∀ p q : Equiv.Perm (Fin 3),
    p ^ 2 = 1 → q ^ 2 = 1 → p ≠ 1 → q ≠ 1 →
      ∃ c : Equiv.Perm (Fin 3), c * p * c⁻¹ = q := by decide +kernel

/-- All outside-core involutions are conjugate within the literal centralizer. -/
public theorem outside_conjugate_of_quaternion_normal (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z)
    (u x : Centralizer z) (hu : orderOf u = 2) (hx : orderOf x = 2)
    (huQ : u ∉ Core z) (hxQ : x ∉ Core z) :
    ∃ c : Centralizer z, c * u * c⁻¹ = x := by
  obtain ⟨q⟩ := h.quaternionCentralProduct
  let π := QuotientGroup.mk' (Core z)
  let e := h.quotient_model.some
  have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  obtain ⟨c, hc⟩ := s3_involutions_conj (e (π u)) (e (π x))
    (by rw [← map_pow, ← map_pow, hu2, map_one, map_one])
    (by rw [← map_pow, ← map_pow, hx2, map_one, map_one])
    (by intro he; exact huQ ((QuotientGroup.eq_one_iff u).mp (e.injective (he.trans e.map_one.symm))))
    (by intro he; exact hxQ ((QuotientGroup.eq_one_iff x).mp (e.injective (he.trans e.map_one.symm))))
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (Core z) (e.symm c)
  have hconj : π (b * u * b⁻¹) = π x := by
    apply e.injective
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hb, e.apply_symm_apply]
    exact hc
  let v := b * u * b⁻¹
  have hv2 : v ^ 2 = 1 := by
    change (MulAut.conj b u)^2=1
    rw [← map_pow, hu2, map_one]
  have hvQ : v ∉ Core z := by
    intro hv
    apply huQ
    have hh := (inferInstance : (Core z).Normal).conj_mem v hv b⁻¹
    simpa [v, mul_assoc] using hh
  have ha := bothOuter_of_not_core h hn q v hvQ
  have ha2 : (MulAut.conjNormal v : MulAut (Core z)) ^ 2 = 1 := by
    rw [← map_pow, hv2, map_one]
  have hcycle := (quaternion_central_product_outer_involution q.left q.right q.left_model
    q.right_model q.span q.intersection_card q.commute (MulAut.conjNormal v) ha2
    ha.left_map ha.right_map ha.left_outer ha.right_outer).2.2
  have hcoset : x * v⁻¹ ∈ Core z := by
    apply (QuotientGroup.eq_one_iff _).mp
    change π (x * v⁻¹) = 1
    rw [map_mul, map_inv, hconj, mul_inv_cancel]
  obtain ⟨k, hk⟩ := normalConjThrough_involution_orbit (Core z) (MulEquiv.refl _) v hv2
    hcycle x hx2 hcoset
  refine ⟨(k : Centralizer z) * b, ?_⟩
  change (k : Centralizer z) * (b * u * b⁻¹) * (k : Centralizer z)⁻¹ = x at hk
  calc
    _ = (k : Centralizer z) * (b * u * b⁻¹) * (k : Centralizer z)⁻¹ := by group
    _ = x := hk
/-- The selected local configuration supplies the complete orbit input to the census. -/
public theorem orbitData_of_quaternion_normal (h : Hypotheses z)
    (hn : QuaternionSubgroupsNormal z) (d : FusionEightData z)
    (a : SelectedFusionData h) : OrbitData z a.u := by
  obtain ⟨hc, ht⟩ := core_orbit_of_quaternion_normal h hn d
  refine ⟨hc, ht, ?_⟩
  intro x hxH hxQ hx
  let uH : Centralizer z := ⟨a.u, a.u_centralizes⟩
  let xH : Centralizer z := ⟨x, hxH⟩
  obtain ⟨c, hc⟩ := outside_conjugate_of_quaternion_normal h hn uH xH
    ((Subgroup.orderOf_coe uH).symm.trans a.u_order)
    ((Subgroup.orderOf_coe xH).symm.trans hx)
    (fun hh => a.u_not_core (mem_map_of_mem (Centralizer z).subtype hh))
    (fun hh => hxQ (mem_map_of_mem (Centralizer z).subtype hh))
  exact ⟨c, congrArg Subtype.val hc⟩

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.Census
