module

public import Theory.SpecificGroups.SU3.SylowOmega
public import Theory.SpecificGroups.SU3.GraphFixedSylowCenters
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.GroupTheory.PerfectCentralCoverSylowRigidity

/-!
# Automorphisms fixing a unitary involution

For the actual SU₃ and PSU₃ carriers over a field of order q², q = 2ⁿ and
n ≥ 2, an automorphism squaring to one and fixing an involution in a Sylow
two-subgroup fixes that Sylow subgroup's entire first omega subgroup.

The root group's regular action away from its isotropic point forces the
centralizer of each nonidentity root element to normalize the root group.
Together with Ω₁(P) = Z(P), this proves uniqueness of the Sylow subgroup
containing an involution. Inner automorphisms follow from centerlessness.
For the graph automorphism, a Sylow subgroup of its fixed group is an entire
ambient Sylow center. Uniqueness identifies the required ambient Sylow, and
arbitrary outer involutions follow by the proved automorphism conjugacy.

For SU₃, automorphisms descend through the scalar projection, whose kernel
is exactly the center. Two involutions with equal images differ by a central
element of exponent dividing both two and three, hence coincide. This lifts
pointwise fixation without identifying a Sylow subgroup with its full preimage.

Source: GLS, Volume 4, Chapter 4, Lemma 3.4(f), with 3.2(b) and 3.4(a,c),
used in Chapter 2, Lemmas 16.2–16.4 and Proposition 16.5. The natural action
is Huppert II.10.12. Both field cardinalities and the actual projection are
retained; no Sylow preservation or specified graph action is assumed.
-/

open Subgroup BenderSuzuki BenderSuzuki.MatrixGroups
open scoped Pointwise
namespace BenderSuzuki.MatrixGroups.HermitianForm.SylowFixedInvolutions

private theorem centralizer_le_normalizer_of_regular
    {G X : Type*} [Group G] (rho : G →* Equiv.Perm X)
    (S : Subgroup G) (p : X)
    (hSfix : ∀ s ∈ S, rho s p = p)
    (hN : ∀ g, rho g p = p → g ∈ normalizer (S : Set G))
    (hreg : ∀ x y : X, x ≠ p → y ≠ p → ∃! s : S, rho s.val x = y)
    (z : G) (hz : z ∈ S) (hne : z ≠ 1) :
    centralizer ({z} : Set G) ≤ normalizer (S : Set G) := by
  have hfix : rho z p = p := hSfix z hz
  have huniq (x : X) (hx : rho z x = x) : x = p := by
    by_contra hxp
    obtain ⟨s, hs, hu⟩ := hreg x x hxp hxp
    have he : (⟨z, hz⟩ : S) = 1 :=
      (hu ⟨z, hz⟩ hx).trans (hu 1 (by simp)).symm
    exact hne (congrArg Subtype.val he)
  intro g hg
  apply hN g
  apply huniq
  have hc := congrArg (fun t : G => rho t p) (mem_centralizer_singleton_iff.mp hg)
  simpa only [map_mul, Equiv.Perm.mul_apply, hfix] using hc.symm

private theorem transport_centralizer_normalizer {G : Type*} [Group G]
    (S : Subgroup G)
    (hS : ∀ z ∈ S, z ≠ 1 → centralizer ({z} : Set G) ≤ normalizer (S : Set G))
    (e : MulAut G) (z : G) (hz : z ∈ S.map e.toMonoidHom) (hne : z ≠ 1) :
    centralizer ({z} : Set G) ≤ normalizer (S.map e.toMonoidHom : Set G) := by
  obtain ⟨w, hw, rfl⟩ := hz
  have hnw : w ≠ 1 := fun h => hne (h ▸ map_one e)
  intro x hx
  have hc : e.symm x ∈ centralizer ({w} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    have h : x * e w = e w * x := mem_centralizer_singleton_iff.mp hx
    simpa only [map_mul, e.apply_symm_apply] using h
  exact S.le_normalizer_map e.toMonoidHom ⟨e.symm x, hS w hw hnw hc, e.apply_symm_apply x⟩

private theorem pgroup_le_sylow_of_normalizes {G : Type*} [Group G]
    (P : Sylow 2 G) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hN : Q ≤ normalizer (P : Set G)) : Q ≤ P := by
  exact (sup_le_iff.mp (P.is_maximal'
    (P.isPGroup'.to_sup_of_normal_left' hQ hN) le_sup_left).le).2

variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2 ^ n)

private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

include hn hJ hcard hfixed in
/-- The centralizer of a nonidentity Sylow element normalizes that Sylow subgroup. -/
public theorem projective_centralizer_le_normalizer
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (z : ProjectiveSpecialUnitaryMatrixGroup J) (hz : z ∈ P) (hne : z ≠ 1) :
    centralizer ({z} : Set _) ≤ normalizer (P : Set _) := by
  obtain ⟨_, rho, p, _, _, _, hroot, _⟩ :=
    External.huppert_II_10_12 J (2 ^ n) hcard hfixed hJ
  obtain ⟨R, _, hRfix, _, hRnorm, _, _, _, _, _, _, _, hreg,
    ⟨coord, hcoord⟩, _⟩ := hroot
  have hcoord_eq (w : External.hermitianUnipotentCoord J) :
      (coord w).val = External.hermitianUnipotentPSU J hJ w := by
    obtain ⟨M, hM, heq⟩ := hcoord w
    have hM' : M = External.hermitianUnipotentGL J w := Units.ext hM
    apply Subtype.ext
    simpa only [hM', External.hermitianUnipotentPSU_val] using heq
  have hR : R = HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage.rootGroup J hJ := by
    apply le_antisymm
    · intro r hr
      obtain ⟨w, hw⟩ := coord.surjective ⟨r, hr⟩
      exact ⟨w, (hcoord_eq w).symm.trans (congrArg Subtype.val hw)⟩
    · rintro r ⟨w, rfl⟩
      rw [← hcoord_eq w]
      exact (coord w).property
  subst R
  let S := HermitianForm.EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hcard hfixed
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) S P
  exact transport_centralizer_normalizer (S : Subgroup _)
    (centralizer_le_normalizer_of_regular rho _ p hRfix (fun _ hg => hRnorm hg) hreg)
    (MulAut.conj g) z hz hne

include hn hJ hcard hfixed in
/-- An involution belongs to a unique projective Sylow two-subgroup. -/
public theorem projective_sylow_eq_of_common_involution
    (P Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (z : ProjectiveSpecialUnitaryMatrixGroup J) (hzP : z ∈ P) (hzQ : z ∈ Q)
    (hne : z ≠ 1) (hz2 : z ^ 2 = 1) : P = Q := by
  have hzO : z ∈ omegaOneAmbient (Q : Subgroup _) :=
    (omegaOneAmbient_le_iff _ _).mp le_rfl z hzQ hz2
  rw [(HermitianForm.SylowOmega.projective_sylow_omega J hn hcard hfixed hJ Q).1] at hzO
  obtain ⟨zQ, hzC, hzv⟩ := hzO
  have hQ : (Q : Subgroup _) ≤ centralizer ({z} : Set _) := by
    intro q hq
    apply mem_centralizer_singleton_iff.mpr
    rw [← hzv]
    exact congrArg Subtype.val (mem_center_iff.mp hzC ⟨q, hq⟩)
  apply Sylow.ext
  exact (Q.is_maximal' P.isPGroup' (pgroup_le_sylow_of_normalizes P Q Q.isPGroup'
    (hQ.trans (projective_centralizer_le_normalizer J hn hJ hcard hfixed P z hzP hne))))

include hn hcard hfixed in
private theorem psu_center_eq_bot : center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
  have hq : 2 < 2 ^ n := by
    have := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2) hn
    norm_num at this
    omega
  let := J.projective_isPerfect_of_fixed_card hq hcard hfixed
  let := External.huppert_II_10_13 J (2 ^ n) hq hcard hfixed
  rcases (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top
      with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h)).elim

include hn hJ hcard hfixed in
private theorem inner_omega_fixed
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (z : ProjectiveSpecialUnitaryMatrixGroup J) (hz : z ∈ P) (hne : z ≠ 1)
    (b : ProjectiveSpecialUnitaryMatrixGroup J)
    (ha : (MulAut.conj b) ^ 2 = 1) (hfix : MulAut.conj b z = z) :
    omegaOneAmbient (P : Subgroup _) ≤ (MulAut.conj b).fixedSubgroup := by
  have hb2 : b ^ 2 = 1 := by
    have hc : MulAut.conj (b ^ 2) = 1 := by rwa [map_pow]
    have hmem : b ^ 2 ∈ center (ProjectiveSpecialUnitaryMatrixGroup J) := by
      rw [mem_center_iff]
      intro x
      have hx := congrArg (fun f : MulAut (ProjectiveSpecialUnitaryMatrixGroup J) => f x) hc
      change b ^ 2 * x * (b ^ 2)⁻¹ = x at hx
      exact (mul_inv_eq_iff_eq_mul.mp hx).symm
    simpa only [psu_center_eq_bot J hn hcard hfixed, mem_bot] using hmem
  have hbN : b ∈ normalizer (P : Set _) :=
    projective_centralizer_le_normalizer J hn hJ hcard hfixed P z hz hne
      (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix))
  have hbP : b ∈ P := by
    have hp : IsPGroup 2 (zpowers b) := IsPGroup.of_card_dvd_pow (n := 1) (by
      simpa only [Nat.card_zpowers, pow_one] using orderOf_dvd_of_pow_eq_one hb2)
    exact pgroup_le_sylow_of_normalizes P _ hp (zpowers_le.mpr hbN) (mem_zpowers b)
  rw [(HermitianForm.SylowOmega.projective_sylow_omega J hn hcard hfixed hJ P).1]
  rintro x ⟨xP, hxC, rfl⟩
  rw [MulAut.mem_fixedSubgroup]
  change b * xP.val * b⁻¹ = xP.val
  rw [mul_inv_eq_iff_eq_mul]
  exact congrArg Subtype.val (mem_center_iff.mp hxC ⟨b, hbP⟩)

include hn hJ hcard hfixed in
private theorem graph_omega_fixed [CharP E 2]
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (z : ProjectiveSpecialUnitaryMatrixGroup J) (hz : z ∈ P) (hne : z ≠ 1)
    (hz2 : z ^ 2 = 1) (hfix : J.projectiveGraphAut hJ z = z) :
    omegaOneAmbient (P : Subgroup _) ≤ (J.projectiveGraphAut hJ).fixedSubgroup := by
  let W := (J.projectiveGraphAut hJ).fixedSubgroup
  let zW : W := ⟨z, (MulAut.mem_fixedSubgroup _ _).mpr hfix⟩
  have hp : IsPGroup 2 (zpowers zW) := IsPGroup.of_card_dvd_pow (n := 1) (by
    simpa only [Nat.card_zpowers, pow_one] using
      orderOf_dvd_of_pow_eq_one (show zW ^ 2 = 1 from Subtype.ext hz2))
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  obtain ⟨Q, hQ⟩ := HermitianForm.GraphFixedSylowCenters.exists_sylow_center_eq
    J hJ hn hcard hfixed S
  have hzQ : z ∈ Q := by
    have hm : z ∈ (center Q).map (Q : Subgroup _).subtype := by
      rw [hQ]
      exact ⟨zW, hS (mem_zpowers _), rfl⟩
    obtain ⟨x, _, rfl⟩ := hm
    exact x.property
  have heq := projective_sylow_eq_of_common_involution J hn hJ hcard hfixed P Q z hz hzQ hne hz2
  rw [heq, (HermitianForm.SylowOmega.projective_sylow_omega J hn hcard hfixed hJ Q).1, hQ]
  exact map_subtype_le _

include hn hJ hcard hfixed in
/-- GLS 3.4(f) for PSU₃: fixing one involution fixes its entire Sylow omega subgroup. -/
public theorem projective_omega_le_fixed
    (P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (z : ProjectiveSpecialUnitaryMatrixGroup J) (hz : z ∈ P) (hne : z ≠ 1)
    (hz2 : z ^ 2 = 1)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (ha : a ^ 2 = 1) (hfix : a z = z) :
    omegaOneAmbient (P : Subgroup _) ≤ a.fixedSubgroup := by
  classical
  by_cases hi : ∃ b, a = MulAut.conj b
  · obtain ⟨b, rfl⟩ := hi
    exact inner_omega_fixed J hn hJ hcard hfixed P z hz hne b ha hfix
  let := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2)
    (by simpa only [← Nat.card_eq_fintype_card, pow_mul] using hcard)
  obtain ⟨c, hc⟩ := J.outer_involution_conjugate n hn hJ hcard hfixed
    (J.projectiveGraphAut_isEntrywiseConjugation hJ) a ha hi
  let Q := P.mapSurjective (f := c.symm.toMonoidHom) c.symm.surjective
  have hcz : J.projectiveGraphAut hJ (c.symm z) = c.symm z := by
    apply c.injective
    rw [c.apply_symm_apply]
    change MulAut.congr c (J.projectiveGraphAut hJ) z = z
    rw [hc, hfix]
  have hQfix := graph_omega_fixed J hn hJ hcard hfixed Q (c.symm z)
    (mem_map_of_mem c.symm.toMonoidHom hz)
    (fun he => hne (c.symm.injective (he.trans (map_one _).symm)))
    (by rw [← map_pow, hz2, map_one]) hcz
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro x hx hx2
  have hcx := (omegaOneAmbient_le_iff _ _).mp hQfix (c.symm x)
    (mem_map_of_mem c.symm.toMonoidHom hx) (by rw [← map_pow, hx2, map_one])
  rw [MulAut.mem_fixedSubgroup] at hcx ⊢
  rw [← hc]
  change c (J.projectiveGraphAut hJ (c.symm x)) = x
  rw [hcx, c.apply_symm_apply]

omit [Finite E] in
/-- Involutions with the same projective image coincide, by the odd central scalar kernel. -/
public theorem special_involution_eq_of_projection_eq
    (x y : J.specialSubgroup) (hx : x ^ 2 = 1) (hy : y ^ 2 = 1)
    (hxy : J.specialToProjective x = J.specialToProjective y) : x = y := by
  let d : J.specialToProjective.ker := ⟨x * y⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]⟩
  have hdc : Commute (d : J.specialSubgroup) y :=
    (mem_center_iff.mp (J.specialToProjective_ker_le_center d.property) y).symm
  have hd2 : (d : J.specialSubgroup) ^ 2 = 1 := by
    have hh := hdc.mul_pow 2
    have hdy : (d : J.specialSubgroup) * y = x := by simp [d]
    rw [hdy, hx, hy, mul_one] at hh
    exact hh.symm
  have hd3 : (d : J.specialSubgroup) ^ 3 = 1 :=
    congrArg Subtype.val (J.specialToProjective_ker_cube d)
  rw [pow_succ, hd2, one_mul] at hd3
  exact mul_inv_eq_one.mp hd3

include hn hcard hfixed in
/-- An automorphism squaring to one descends through the literal scalar projection. -/
public theorem special_descended_involution
    (a : MulAut J.specialSubgroup) (ha : a ^ 2 = 1) :
    ∃ b : MulAut (ProjectiveSpecialUnitaryMatrixGroup J), b ^ 2 = 1 ∧
      ∀ x, b (J.specialToProjective x) = J.specialToProjective (a x) := by
  have hq : 2 < 2 ^ n := by
    change 2 ^ 1 < 2 ^ n
    exact Nat.pow_lt_pow_right (by decide) (by omega)
  let f : PerfectCentralCovering.Cover J.specialSubgroup
      (ProjectiveSpecialUnitaryMatrixGroup J) := {
    toMonoidHom := J.specialToProjective
    surjective := J.specialToProjective_surjective
    isPerfect := J.special_isPerfect_of_fixed_card hq hcard hfixed
    ker_le_center := J.specialToProjective_ker_le_center }
  obtain ⟨b, hb⟩ := f.exists_descended_aut
    (J.specialToProjective_ker_eq_center (psu_center_eq_bot J hn hcard hfixed)) a
  change ∀ x, b (J.specialToProjective x) = J.specialToProjective (a x) at hb
  refine ⟨b, ?_, hb⟩
  apply MulEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := J.specialToProjective_surjective x
  change b (b (J.specialToProjective y)) = J.specialToProjective y
  rw [hb, hb]
  have hay := congrArg (fun f : MulAut J.specialSubgroup => f y) ha
  change a (a y) = y at hay
  rw [hay]

include hn hJ hcard hfixed in
/-- The fixed-involution implication for SU₃, including its possible nontrivial center. -/
public theorem special_omega_le_fixed
    (P : Sylow 2 J.specialSubgroup)
    (z : J.specialSubgroup) (hz : z ∈ P) (hne : z ≠ 1) (hz2 : z ^ 2 = 1)
    (a : MulAut J.specialSubgroup) (ha : a ^ 2 = 1) (hfix : a z = z) :
    omegaOneAmbient (P : Subgroup _) ≤ a.fixedSubgroup := by
  obtain ⟨b, hb2, hb⟩ := special_descended_involution J hn hcard hfixed a ha
  let Q := P.mapSurjective J.specialToProjective_surjective
  have hzne : J.specialToProjective z ≠ 1 := by
    intro he
    apply hne
    apply congrArg Subtype.val (HermitianForm.SylowOmega.specialProjection_injective_on_sylow
      J P (a₁ := ⟨z, hz⟩) (a₂ := 1) ?_)
    exact he.trans (map_one _).symm
  have hQ := projective_omega_le_fixed J hn hJ hcard hfixed Q (J.specialToProjective z)
    (mem_map_of_mem J.specialToProjective hz) hzne
    (by rw [← map_pow, hz2, map_one]) b hb2 (by rw [hb, hfix])
  apply (omegaOneAmbient_le_iff _ _).mpr
  intro x hx hx2
  have hbfix := (omegaOneAmbient_le_iff _ _).mp hQ (J.specialToProjective x)
    (mem_map_of_mem J.specialToProjective hx) (by rw [← map_pow, hx2, map_one])
  rw [MulAut.mem_fixedSubgroup] at hbfix ⊢
  apply special_involution_eq_of_projection_eq J (a x) x
    (by rw [← map_pow, hx2, map_one]) hx2
  rw [← hb, hbfix]
end BenderSuzuki.MatrixGroups.HermitianForm.SylowFixedInvolutions
