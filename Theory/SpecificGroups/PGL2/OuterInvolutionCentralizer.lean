module

public import GorensteinWalter.PGL2LowReflectedToriCard
public import GorensteinWalter.PGL2CanonicalOuterInvolutionFusion
public import GorensteinWalter.DihedralOddRotationCentralizer
public import Theory.GroupTheory.SpecificGroups.CyclicInvertedDihedral
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# Centralizers of outer involutions in odd PGL₂

The actual canonical PSL₂ image intersects the centralizer of the outer
involution of the low reflected torus in its odd rotation subgroup extended
by the inner reflector. This gives an odd dihedral model, whose rotation
subgroup has order greater than one. Outer-involution fusion transports it
to every outer involution, using the original canonical PSL₂ inclusion.

The intersection calculation adapts the private proof in
`GorensteinWalter/Section2/Theorem26ComponentTransport.lean`. The application
is Aschbacher–Smith, proof of 2.5.21, printed p.567; the intrinsic torus
calculation is the existing Gorenstein–Walter PGL₂ development.
-/

public section

open Subgroup GorensteinWalter Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.PGL2
universe u
private theorem reflected_centralizer_intersection_eq_sup
    {K : Type u} [Field K] [Finite K]
    (P : Sylow 2 (PGL2 K)) {m : ℕ} (eP : P ≃* DihedralGroup (2 ^ m))
    (T : PGL2LowReflectedToriData K P eP) :
    let J : Subgroup (PGL2 K) := commutator (PGL2 K)
    J ⊓ Subgroup.centralizer ({T.s} : Set (PGL2 K)) =
      T.R ⊔ Subgroup.zpowers T.t := by
  classical
  intro J
  have hR : T.R = T.U ⊓ J := by simpa [J] using T.R_eq
  have hC : Subgroup.centralizer ({T.s} : Set (PGL2 K)) =
      T.U ⊔ Subgroup.zpowers T.w := T.centralizer_eq
  have htC : T.t ∈ Subgroup.centralizer ({T.s} : Set (PGL2 K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact T.t_commutes_s.eq
  have htJ : T.t ∈ J := by simpa [J] using T.t_mem_commutator
  apply le_antisymm
  · intro x hx
    have hxJ : x ∈ J := hx.1
    have hxC : x ∈ Subgroup.centralizer ({T.s} : Set (PGL2 K)) := hx.2
    rw [hC] at hxC
    rcases (mem_sup_zpowers_of_involution_inverts T.w_not_mem_U T.w_involution
        T.w_inverts_U).mp hxC with ⟨u, huU, hu | huw⟩
    · have huJ : u ∈ J := by simpa [hu] using hxJ
      have huR : u ∈ T.R := by
        rw [hR]
        exact ⟨huU, huJ⟩
      simpa [hu] using (Subgroup.mem_sup_left huR : u ∈ T.R ⊔ Subgroup.zpowers T.t)
    · by_cases hwJ : T.w ∈ J
      · have ht_eq : T.t = T.w := by
          rcases T.t_eq_w_or_ws with ht | hts
          · exact ht
          · exfalso
            have hsJ : T.s ∈ J := by
              have hwts : T.w⁻¹ * T.t = T.s := by
                calc
                  T.w⁻¹ * T.t = T.w⁻¹ * (T.w * T.s) := by rw [hts]
                  _ = T.s := by group
              have hwtJ : T.w⁻¹ * T.t ∈ J := J.mul_mem (J.inv_mem hwJ) htJ
              simpa [hwts] using hwtJ
            exact T.s_not_mem_commutator (by simpa [J] using hsJ)
        have huJ : u ∈ J := by
          have hxw : x * T.w⁻¹ ∈ J := J.mul_mem hxJ (J.inv_mem hwJ)
          have hu_eq : u = x * T.w⁻¹ := by
            calc
              u = (u * T.w) * T.w⁻¹ := by group
              _ = x * T.w⁻¹ := by rw [huw]
          simpa [hu_eq] using hxw
        have huR : u ∈ T.R := by
          rw [hR]
          exact ⟨huU, huJ⟩
        have hxeq : x = u * T.t := by rw [huw, ← ht_eq]
        simpa [hxeq] using (Subgroup.mul_mem_sup huR (Subgroup.mem_zpowers T.t))
      · have ht_eq : T.t = T.w * T.s := by
          rcases T.t_eq_w_or_ws with ht | hts
          · exfalso
            exact hwJ (by simpa [ht] using htJ)
          · exact hts
        have hws : T.w * T.s = T.s * T.w := by
          have h := T.w_inverts_U T.s T.s_mem_U
          have hsinv : T.s⁻¹ = T.s := by
            simpa [pow_two] using
              (inv_eq_of_mul_eq_one_right (by simpa [pow_two] using T.s_involution.right))
          rw [hsinv] at h
          calc
            T.w * T.s = (T.w * T.s * T.w⁻¹) * T.w := by group
            _ = T.s * T.w := by rw [h]
        have hxt : x * T.t⁻¹ ∈ J := J.mul_mem hxJ (J.inv_mem htJ)
        have htinv : T.t⁻¹ = T.w * T.s := by
          calc
            T.t⁻¹ = T.t := by
              simpa [pow_two] using
                (inv_eq_of_mul_eq_one_right (by simpa [pow_two] using T.t_involution.right))
            _ = T.w * T.s := ht_eq
        have hstep : x * T.t⁻¹ = u * T.s := by
          rw [huw, htinv]
          calc
            u * T.w * (T.w * T.s) = u * (T.w * T.w) * T.s := by group
            _ = u * T.s := by simp [T.w_involution]
        have husJ : u * T.s ∈ J := by
          simpa [hstep] using hxt
        have husU : u * T.s ∈ T.U := T.U.mul_mem huU T.s_mem_U
        have husR : u * T.s ∈ T.R := by
          rw [hR]
          exact ⟨husU, husJ⟩
        have hxeq : x = (u * T.s) * T.t := by
          rw [huw, ht_eq]
          calc
            u * T.w = u * T.w * (T.s * T.s) := by
              rw [← pow_two, T.s_involution.right]
              group
            _ = u * (T.w * T.s) * T.s := by group
            _ = u * (T.s * T.w) * T.s := by rw [hws]
            _ = (u * T.s) * (T.w * T.s) := by group
        simpa [hxeq] using (Subgroup.mul_mem_sup husR (Subgroup.mem_zpowers T.t))
  · apply sup_le
    · intro x hxR
      have hxJ : x ∈ J := by
        rw [hR] at hxR
        exact hxR.2
      exact ⟨hxJ, T.R_le_centralizer_s hxR⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨htJ, htC⟩

/-- The centralizer in the canonical PSL₂ image of an outer involution of
PGL₂ has an actual odd dihedral model with nontrivial rotation subgroup. -/
theorem outer_involution_centralizer_dihedral
    (F : Type u) [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (hc : 3 < Nat.card F)
    (a : PGL2 F) (ha : IsInvolution a)
    (hout : a ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range) :
    ∃ n : ℕ, Odd n ∧ 1 < n ∧ Nonempty
      (((Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ⊓
        centralizer ({a} : Set (PGL2 F)) : Subgroup (PGL2 F)) ≃* DihedralGroup n) := by
  classical
  let : Finite (PGL2 F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  let P : Sylow 2 (PGL2 F) := Classical.choice inferInstance
  obtain ⟨m, _, ⟨eP⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F hF P
  obtain ⟨T⟩ := pgl2_low_reflected_tori_card_four F hF hc P eP
  let J : Subgroup (PGL2 F) := commutator (PGL2 F)
  have hJ : J = (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three F hF hc
  have hcyc : IsCyclic T.R := by
    let : IsCyclic T.U := T.U_cyclic
    exact isCyclic_of_injective (inclusion (show T.R ≤ T.U from by rw [T.R_eq]; exact inf_le_left))
      (inclusion_injective _)
  obtain ⟨eD⟩ := nonempty_mulEquiv_dihedralGroup_of_cyclic_inverted T.R T.t hcyc
    T.t_involution.2 (fun ht => T.t_not_mem_U (by rw [T.R_eq] at ht; exact ht.1))
    (fun r hr => T.t_inverts_U r (by rw [T.R_eq] at hr; exact hr.1))
  have hsout : T.s ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
    rw [← hJ]
    exact T.s_not_mem_commutator
  obtain ⟨g, hg⟩ := isConj_iff.mp
    (pgl2_outer_involutions_conjugate_of_odd_prime_power F hF T.s_involution ha hsout hout)
  have he : (J ⊓ centralizer ({T.s} : Set (PGL2 F)) : Subgroup (PGL2 F)).map
      (MulAut.conj g).toMonoidHom = J ⊓ centralizer ({a} : Set (PGL2 F)) := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj g).injective, map_centralizer_equiv]
    have hjmap : J.map (MulAut.conj g).toMonoidHom = J :=
      Subgroup.Normal.map_conj_eq J g
    rw [hjmap]
    rw [Set.image_singleton]
    change J ⊓ centralizer ({g * T.s * g⁻¹} : Set (PGL2 F)) = _
    rw [hg]
  let eC := ((MulAut.conj g).subgroupMap
    (J ⊓ centralizer ({T.s} : Set (PGL2 F)))).trans (MulEquiv.subgroupCongr he)
  refine ⟨Nat.card T.R, T.R_card_odd, T.R_card_gt_one, ⟨?_⟩⟩
  rw [← hJ]
  exact eC.symm.trans ((MulEquiv.subgroupCongr
    (reflected_centralizer_intersection_eq_sup P eP T)).trans eD)

end Theory.PGL2

end
