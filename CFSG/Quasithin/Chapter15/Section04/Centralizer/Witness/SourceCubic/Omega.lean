module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Witness.TernaryLine
public import Theory.GroupTheory.MinimalNormalPCore
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.Fitting.Centralizer

/-!
# The literal odd omega-center in the centralizer quotient

For a solvable {2,3}-overgroup H of the ambient Sylow two-subgroup T,
H≠T forces O₃(H/O₂(H))≠1. Its central first omega subgroup is normal
and elementary. The original three-rank bound on H bounds its order by
nine using elementary-subgroup lifting through the coprime two-core
kernel, rather than rank monotonicity for arbitrary quotients.

Source: Aschbacher--Smith 15.4.9, printed p.1159.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SourceCubic
open FamilySource
variable {G : Type*} [Group G] [Finite G]

/-- The actual Ω₁(Z(O₃(H/O₂(H)))), embedded into the original quotient. -/
@[expose] def omegaCandidate (H : Subgroup G) : Subgroup (CoreQuotient H) :=
  ((omega₁ (center (pCore 3 (CoreQuotient H))) (p := 3)).map
    (center (pCore 3 (CoreQuotient H))).subtype).map (pCore 3 (CoreQuotient H)).subtype

omit [Finite G] in
/-- The candidate is normal in the actual two-core quotient. -/
theorem omegaCandidate_normal (H : Subgroup G) : (omegaCandidate H).Normal := by
  let : (omega₁ (center (pCore 3 (CoreQuotient H))) (p := 3)).Characteristic :=
    omega₁_characteristic _
  unfold omegaCandidate
  exact inferInstance

omit [Finite G] in
/-- The candidate is an elementary abelian three-group. -/
theorem omegaCandidate_elementary (H : Subgroup G) : IsElementaryAbelian 3 (omegaCandidate H) := by
  let : IsElementaryAbelian 3 (omega₁ (center (pCore 3 (CoreQuotient H))) (p := 3)) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian 3 ((omega₁ (center (pCore 3 (CoreQuotient H))) (p := 3)).map
      (center (pCore 3 (CoreQuotient H))).subtype) := IsElementaryAbelian.map_subtype
  exact IsElementaryAbelian.map_subtype

/-- The quotient has nontrivial three-core as soon as H is a proper Sylow overgroup. -/
theorem quotient_threeCore_ne_bot (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hne : H ≠ (T : Subgroup G))
    (hs : Group.IsSolvable H)
    (hp : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3) :
    pCore 3 (CoreQuotient H) ≠ ⊥ := by
  let Q := CoreQuotient H
  let q := quotientMap H
  let : Group.IsSolvable H := hs
  have hqs : Group.IsSolvable Q := inferInstance
  have hqp : ∀ p : ℕ, p.Prime → p ∣ Nat.card Q → p = 2 ∨ p = 3 := by
    intro p hprime hd
    exact hp p hprime (hd.trans (Subgroup.index_dvd_card (pCore 2 H)))
  intro hthree
  have htwo : pCore 2 Q = ⊥ := by
    have hk : IsPGroup 2 q.ker := by
      change IsPGroup 2 (QuotientGroup.mk' (pCore 2 H)).ker
      rw [QuotientGroup.ker_mk']
      exact pCore_isPGroup
    have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
    have he := q.comap_pCore_of_ker_isPGroup hq hk
    have hm := congrArg (Subgroup.map q) he
    rw [map_comap_eq_self_of_surjective hq] at hm
    exact hm.trans ((Subgroup.map_eq_bot_iff _).mpr (by
      change pCore 2 H ≤ (QuotientGroup.mk' (pCore 2 H)).ker
      rw [QuotientGroup.ker_mk']))
  have hf : fittingSubgroup Q = ⊥ := by
    rw [fitting_eq_sup_pCore]
    apply le_bot_iff.mp
    refine iSup_le fun p => ?_
    rcases hqp p.val.val (Nat.prime_of_mem_primeFactors p.val.property)
      (Nat.dvd_of_mem_primeFactors p.val.property) with h | h
    · rw [h, htwo]
    · rw [h, hthree]
  have hall : (⊤ : Subgroup Q) ≤ ⊥ := by
    have hc := centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hqs
    rw [hf] at hc
    intro x _
    apply hc
    intro y hy
    have hy1 : y = 1 := hy
    simp [hy1]
  have hc : pCore 2 H = ⊤ := by
    apply top_unique
    intro x _
    have he : q x = 1 := hall (mem_top _)
    exact (QuotientGroup.eq_one_iff x).mp he
  let e : pCore 2 H ≃* H := (MulEquiv.subgroupCongr hc).trans Subgroup.topEquiv
  have hH : IsPGroup 2 H := (pCore_isPGroup (p := 2) (G := H)).of_surjective e.toMonoidHom e.surjective
  exact hne (T.is_maximal' hH hTH)

/-- The original three-rank bound gives order three or nine for the literal candidate. -/
theorem omegaCandidate_card (T : Sylow 2 G) (H : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hne : H ≠ (T : Subgroup G))
    (hs : Group.IsSolvable H)
    (hp : ∀ p : ℕ, p.Prime → p ∣ Nat.card H → p = 2 ∨ p = 3)
    (hr : primeRank 3 H ≤ 2) : Nat.card (omegaCandidate H) = 3 ∨ Nat.card (omegaCandidate H) = 9 := by
  let Q := CoreQuotient H
  let C := pCore 3 Q
  let : Nontrivial C := (nontrivial_iff_ne_bot C).mpr (quotient_threeCore_ne_bot T H hTH hne hs hp)
  have hPne : omegaCandidate H ≠ ⊥ := by
    intro he
    exact omega_center_ne_bot (G := C) pCore_isPGroup
      ((Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).mp he)
  let : IsElementaryAbelian 3 (omegaCandidate H) := omegaCandidate_elementary H
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3)).mp
    (IsElementaryAbelian.isPGroup (p := 3) (G := omegaCandidate H))
  have hk : Nat.Coprime 3 (Nat.card (quotientMap H).ker) := by
    rw [quotientMap, QuotientGroup.ker_mk']
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).mp (pCore_isPGroup (p := 2) (G := H))
    rw [hm]
    exact (by decide : Nat.Coprime 3 2).pow_right m
  have hnle : n ≤ 2 := (IsElementaryAbelian.primeRank_ge_of_coprime_quotient
    (quotientMap H) (QuotientGroup.mk'_surjective _) hk (omegaCandidate H) hn).trans hr
  have hnpos : 0 < n := by
    have hcard := (Subgroup.one_lt_card_iff_ne_bot (omegaCandidate H)).mpr hPne
    by_contra h
    have : n = 0 := by omega
    simp only [this, pow_zero] at hn
    omega
  have hncase : n = 1 ∨ n = 2 := by omega
  rcases hncase with rfl | rfl
  · exact Or.inl (by simpa using hn)
  · exact Or.inr (by simpa using hn)

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness.SourceCubic
