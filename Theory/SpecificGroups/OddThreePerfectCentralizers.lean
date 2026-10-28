module
public import Theory.SpecificGroups.GL2.CubeKernelInvolutions
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.CharacteristicTwo
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.ScalarKernel
public import Theory.SpecificGroups.SU3.InnerInvolutionThreeRank.FormTransport
public import Theory.SpecificGroups.SU3.InvolutionConjugacy

/-!
# Perfect subgroups of odd ternary involution centralizers

The full projective centralizer is a quotient of a degree-two linear group
through a central kernel of exponent three. Its perfect subgroups have at
most one involution, hence two-rank at most one. The special linear group
has a literal GL₂ centralizer; the special unitary group retains the same
obstruction on centerless perfect subgroups through its scalar quotient.

Source: Aschbacher–Smith A.3.21(a), p.55, used in A.3.12(9) and C.5.12.
-/

public section
open Subgroup Matrix

namespace Matrix.GeneralLinearGroup.CubeKernel

theorem perfect_two_rank_le_one {G H K F : Type*} [Group G] [Group H] [Group K]
    [Finite K] [Group.IsPerfect K] [Field F]
    (hF : (2 : F) ≠ 0) (f : G →* H) (hf : Function.Surjective f)
    (hker : ∀ g ∈ f.ker, g ^ 3 = 1)
    (ρ : G →* GL (Fin 2) F) (hρ : Function.Injective ρ)
    (j : K →* H) (hj : Function.Injective j) : primeRank 2 K ≤ 1 := by
  classical
  apply (primeRank_le_iff_elementary_card_le K).mpr
  intro A hA
  have hpow (a : A) : (a : K) ^ 2 = 1 :=
    congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p a)
  by_cases he : ∃ a : A, (a : K) ≠ 1
  · obtain ⟨a, ha⟩ := he
    have hset : (A : Set K) ⊆ {1, (a : K)} := by
      intro b hb
      by_cases hb1 : b = 1
      · exact Or.inl hb1
      · exact Or.inr (perfect_involutions_eq hF f hf hker ρ hρ j hj
          (hpow ⟨b,hb⟩) hb1 (hpow a) ha)
    have hc := Set.ncard_le_ncard hset
    rw [Set.ncard_pair (Ne.symm ha)] at hc
    have he : Nat.card A = (A : Set K).ncard := by
      rw [← Nat.card_coe_set_eq]
      exact Nat.card_congr (Equiv.refl A)
    simpa only [he, pow_one] using hc
  · have hb : A = ⊥ := by
      apply eq_bot_iff.mpr
      intro a ha
      exact mem_bot.mpr (by by_contra hn; exact he ⟨⟨a,ha⟩,hn⟩)
    simp only [hb, card_bot]
    norm_num
end Matrix.GeneralLinearGroup.CubeKernel

namespace Theory.SpecificGroups.OddThreePerfectCentralizers
open Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups

variable {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]

/-- Odd PSL₃ involution centralizers have no perfect subgroup of two-rank two. -/
theorem projective_linear_rank {F : Type*} [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) (t : PSL(3,F)) (ht : orderOf t = 2)
    (j : K →* centralizer ({t} : Set PSL(3,F))) (hj : Function.Injective j) :
    primeRank 2 K ≤ 1 := by
  obtain ⟨f,hf,_,hker⟩ := PSL3.OddInvolutionFixed.exists_gl2_cubic_central_surjection t ht h2
  exact GeneralLinearGroup.CubeKernel.perfect_two_rank_le_one h2 f hf hker
    (MonoidHom.id _) Function.injective_id j hj

private theorem prime_conj (n p : ℕ) [Fact p.Prime]
    (x : GaloisField p (2 * 1)) :
    (ABG.unitaryForm n p 1 one_ne_zero).conj x = x ^ p := by
  simp only [ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]

/-- The standard odd PSU₃ centralizer retains the determinant-one involution. -/
theorem standard_projective_unitary_rank (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (t : ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 p 1 one_ne_zero))
    (ht : orderOf t = 2)
    (j : K →* centralizer ({t} : Set
      (ProjectiveSpecialUnitaryMatrixGroup (ABG.unitaryForm 3 p 1 one_ne_zero))))
    (hj : Function.Injective j) : primeRank 2 K ≤ 1 := by
  let J3 := ABG.unitaryForm 3 p 1 one_ne_zero
  let J2 := ABG.unitaryForm 2 p 1 one_ne_zero
  let q := J3.specialToProjective
  have hcube : ∀ x ∈ q.ker, x ^ 3 = 1 := by
    intro x hx
    exact congrArg Subtype.val (J3.specialToProjective_ker_cube ⟨x, hx⟩)
  obtain ⟨z, hz, rfl⟩ := SU3.InnerThreeRank.exists_involution_lift_of_cube_kernel q
    J3.specialToProjective_surjective hcube t ht
  let C := centralizer ({z} : Set J3.specialSubgroup)
  have hmap : C.map q = centralizer ({q z} : Set (ProjectiveSpecialUnitaryMatrixGroup J3)) :=
    SU3.InnerThreeRank.map_centralizer_of_central_cube_kernel q J3.specialToProjective_surjective
      J3.specialToProjective_ker_le_center hcube z (by simpa only [hz] using pow_orderOf_eq_one z)
  let ep := MulEquiv.subgroupCongr hmap
  let f := ep.toMonoidHom.comp (q.subgroupMap C)
  have hf : Function.Surjective f := ep.surjective.comp (q.subgroupMap_surjective C)
  have hker : ∀ g ∈ f.ker, g ^ 3 = 1 := by
    intro g hg
    apply Subtype.ext
    apply hcube
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hg)
  have hp2 : p ≠ 2 := by have := Nat.odd_iff.mp hp; omega
  let ec : C ≃* J2.unitarySubgroup :=
    (SU3.involutionCentralizerEquiv hp2 (GaloisField.card p (2 * 1) (by decide))
      J3 J2 rfl rfl (prime_conj 3 p) (prime_conj 2 p) z hz).symm
  let ρ := J2.unitarySubgroup.subtype.comp ec.toMonoidHom
  have hρ : Function.Injective ρ := Subtype.val_injective.comp ec.injective
  exact GeneralLinearGroup.CubeKernel.perfect_two_rank_le_one
    (CharP.cast_ne_zero_of_ne_of_prime (GaloisField p (2 * 1)) Nat.prime_two hp2)
    f hf hker ρ hρ j hj

/-- The bound holds for every stored nondegenerate ternary Hermitian form. -/
theorem projective_unitary_rank (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (E : Type*) [Field E] [Finite E] (J : HermitianForm 3 E)
    (hcard : Nat.card E = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (ht : orderOf t = 2)
    (j : K →* centralizer ({t} : Set (ProjectiveSpecialUnitaryMatrixGroup J)))
    (hj : Function.Injective j) : primeRank 2 K ≤ 1 := by
  obtain ⟨a⟩ := SU3.InnerThreeRank.exists_projective_equiv_standard p E J hcard hc
  let c := SU3.InnerThreeRank.centralizerEquiv a t
  exact standard_projective_unitary_rank p hp (a t) ((a.orderOf_eq t).trans ht)
    (c.toMonoidHom.comp j) (c.injective.comp hj)

omit [Finite K] [Group.IsPerfect K] in
/-- A centerless subgroup remains faithful through a central quotient. -/
theorem injective_comp_of_center_eq_bot {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hc : f.ker ≤ center G) (i : K →* G)
    (hi : Function.Injective i) (hz : center K = ⊥) :
    Function.Injective (f.comp i) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have hix : i x ∈ center G := hc hx
  have hxz : x ∈ center K := mem_center_iff.mpr fun y => hi (by
    simpa only [map_mul] using mem_center_iff.mp hix (i y))
  simpa only [hz, mem_bot] using hxz

omit [Finite K] [Group.IsPerfect K] in
/-- A cubic central quotient preserves the centralizer obstruction for a
centerless perfect smaller subgroup. -/
theorem rank_of_central_cube_projection {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hc : f.ker ≤ center G) (hker : ∀ g ∈ f.ker, g ^ 3 = 1)
    (hz : center K = ⊥)
    (hH : ∀ (t : H), orderOf t = 2 →
      ∀ (j : K →* centralizer ({t} : Set H)), Function.Injective j → primeRank 2 K ≤ 1)
    (t : G) (ht : orderOf t = 2)
    (j : K →* centralizer ({t} : Set G)) (hj : Function.Injective j) :
    primeRank 2 K ≤ 1 := by
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have hft : orderOf (f t) = 2 := by
    apply orderOf_eq_prime (by rw [← map_pow,ht2,map_one])
    intro he
    have h3 := hker t he
    rw [pow_succ,ht2,one_mul] at h3
    rw [h3,orderOf_one] at ht
    omega
  let i := (centralizer ({t} : Set G)).subtype.comp j
  have hi : Function.Injective i := Subtype.val_injective.comp hj
  let a : K →* centralizer ({f t} : Set H) := (f.comp i).codRestrict _ (by
    intro x
    apply mem_centralizer_singleton_iff.mpr
    simpa only [i, MonoidHom.comp_apply, Subgroup.subtype_apply, map_mul] using
      congrArg f (mem_centralizer_singleton_iff.mp (j x).property))
  exact hH (f t) hft a (fun x y he =>
    injective_comp_of_center_eq_bot f hc i hi hz (congrArg Subtype.val he))

/-- The special linear centralizer itself is GL₂. -/
theorem special_linear_rank {F : Type*} [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) (t : SL(3,F)) (ht : orderOf t = 2)
    (j : K →* centralizer ({t} : Set SL(3,F))) (hj : Function.Injective j) :
    primeRank 2 K ≤ 1 := by
  let e := SL3.involutionCentralizerEquiv F t ht h2
  exact GeneralLinearGroup.CubeKernel.perfect_two_rank_le_one h2
    (MonoidHom.id _) Function.surjective_id (fun g hg => by
      have hg : g = 1 := hg
      simp only [hg,one_pow]) e.toMonoidHom e.injective j hj

/-- The special unitary centralizer has the same obstruction for centerless
perfect subgroups; the actual scalar kernel has exponent three. -/
theorem special_unitary_rank (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (E : Type*) [Field E] [Finite E] (J : HermitianForm 3 E)
    (hcard : Nat.card E = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (hz : center K = ⊥) (t : J.specialSubgroup) (ht : orderOf t = 2)
    (j : K →* centralizer ({t} : Set J.specialSubgroup))
    (hj : Function.Injective j) : primeRank 2 K ≤ 1 := by
  apply rank_of_central_cube_projection J.specialToProjective
    J.specialToProjective_ker_le_center (fun x hx =>
      congrArg Subtype.val (J.specialToProjective_ker_cube ⟨x,hx⟩)) hz
    (fun t ht j hj => projective_unitary_rank p hp E J hcard hc t ht j hj) t ht j hj

end Theory.SpecificGroups.OddThreePerfectCentralizers
