module

public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveFixedCyclic
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticFiveResidualDerived
public import Theory.GroupTheory.AbelianQuotientFixedSubgroup
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Involutions in the original residual under its low derived alternative

An involution outside the index-two residual would supplement it to Q.
Each elementary commutator with that involution is inverted, hence fixed,
by the involution. If the residual derived subgroup lies in the original
central line, the involution consequently centralizes the whole Q-derived
span U. It then belongs to the full kernel C. The original nine-path has
already proved Omega1(C)=U, forcing the involution back into the residual.
This is an implication from the actual low derived alternative, not an
assertion that the residual is extraspecial or a model recognition.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- If the actual residual derived subgroup is contained in the original
central line, every square-one element of Q already lies in that residual. -/
theorem source_quintic_large_five_involutions_mem_residual_of_derived_central
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlarge : Nat.card (H.pCoreIn 2) = 1024)
    (A : Subgroup G) (hAH : A ≤ H) (hA : Nat.card A = 5)
    (hlow : ⁅⁅H.pCoreIn 2,A⁆,⁅H.pCoreIn 2,A⁆⁆ ≤ centralInvolutions T) :
    ∀ x ∈ H.pCoreIn 2, x ^ 2 = 1 → x ∈ ⁅H.pCoreIn 2,A⁆ := by
  classical
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let R := ⁅Q,A⁆
  let Z := centralInvolutions T
  let C := H ⊓ centralizer (U : Set G)
  change ⁅R,R⁆ ≤ Z at hlow
  obtain ⟨_, _, _, _, hRcard, hUR, _, _⟩ := source_quintic_large_five_residual
    hG T hempty hM hu hmany hcard e H hH hi hlarge A hAH hA
  have hAQ : A ≤ normalizer (Q : Set G) := hAH.trans
    (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hRQ : R ≤ Q := le_normalizer_iff_commutator_le_left.mp hAQ
  have hderived : ⁅Q,Q⁆ = U := (source_quintic_full_core_layers
    hG T hempty hM hu hmany hcard e H hH hi).1
  have hUQ : U ≤ Q := hderived.ge.trans (commutator_le_self Q)
  have hQU : Q ≤ normalizer (U : Set G) := (pCoreIn_le 2 H).trans
    (le_normalizer_conjugateSpanBy _ _)
  have hHZ : H ≤ centralizer (Z : Set G) :=
    (Section02.source_lemma_14_2_3
      hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hZQ : Z ≤ centralizer (Q : Set G) :=
    le_centralizer_iff.mp ((pCoreIn_le 2 H).trans hHZ)
  have hZU : Z ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 U := (Section02.SolvableAmalgam.source_index_five_closure_structure
    hG T hempty hM hu hmany hcard e H hH.1 hi).1
  have hiRQ : R.relIndex Q = 2 := by
    have hh := relIndex_mul_card_of_le hRQ
    rw [hRcard, hlarge] at hh
    omega
  intro x hxQ hx2
  by_contra hxR
  have hxne : x ≠ 1 := fun hx => hxR (hx ▸ R.one_mem)
  have hxorder : orderOf x = 2 := orderOf_eq_prime hx2 hxne
  let X := zpowers x
  have hXQ : X ≤ Q := zpowers_le.mpr hxQ
  have hgen : R ⊔ X = Q := by
    apply le_antisymm (sup_le hRQ hXQ)
    intro q hq
    by_cases hqR : q ∈ R
    · exact (show R ≤ R ⊔ X from le_sup_left) hqR
    have hqx : q * x⁻¹ ∈ R := by
      have hh := (R.subgroupOf Q).mul_mem_iff_of_index_two hiRQ
        (a := ⟨q,hq⟩) (b := ⟨x⁻¹,Q.inv_mem hxQ⟩)
      apply hh.mpr
      change q ∈ R ↔ x⁻¹ ∈ R
      rw [R.inv_mem_iff]
      exact iff_of_false hqR hxR
    simpa only [inv_mul_cancel_right] using (R ⊔ X).mul_mem
      ((show R ≤ R ⊔ X from le_sup_left) hqx)
      ((show X ≤ R ⊔ X from le_sup_right) (mem_zpowers x))
  let D := U ⊓ centralizer ({x} : Set G)
  have hQD : Q ≤ normalizer (D : Set G) :=
    abelian_quotient_preserves_fixed Q U hQU hderived.le x hxQ
  have hRR : ⁅R,R⁆ ≤ D := le_inf (hlow.trans hZU) (by
    intro d hd
    exact mem_centralizer_singleton_iff.mpr ((hZQ (hlow hd)) x hxQ).symm)
  have hRX : ⁅R,X⁆ ≤ D := by
    apply commutator_le.mpr
    intro r hr y hy
    have hycases : y = 1 ∨ y = x := by
      change y ∈ zpowers x at hy
      rw [mem_zpowers_iff_mem_range_orderOf, hxorder] at hy
      obtain ⟨n,hn,hy⟩ := Finset.mem_image.mp hy
      have hn2 : n < 2 := Finset.mem_range.mp hn
      interval_cases n <;> simp_all
    rcases hycases with hy1 | hyx
    · rw [hy1]; simp
    subst y
    have hdU : ⁅r,x⁆ ∈ U := hderived.le
      (commutator_mem_commutator (hRQ hr) hxQ)
    have hxx : x⁻¹ = x := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hx2)
    have hdd : ⁅r,x⁆⁻¹ = ⁅r,x⁆ := inv_eq_of_mul_eq_one_left
      (by simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) ⁅r,x⁆ hdU)
    have hdx : ⁅r,x⁆ * x = x * ⁅r,x⁆ := by
      have hh := commutatorElement_inv_right r x
      rw [hxx, ← commutatorElement_inv r x, hdd] at hh
      have hh' := congrArg (fun z => z * x) hh
      have hxx' : x * x = 1 := by simpa only [pow_two] using hx2
      simpa only [mul_assoc, hxx', mul_one] using hh'
    exact ⟨hdU, mem_centralizer_singleton_iff.mpr hdx⟩
  have hXX : ⁅X,X⁆ ≤ D := by
    rw [commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative X)]
    exact bot_le
  have hQR : ⁅Q,R⁆ ≤ D := by
    rw [← hgen]
    exact commutator_sup_le_of_relative_normal Q R X R D hQD hRQ hXQ hRR
      (by rw [commutator_comm]; exact hRX)
  have hQX : ⁅Q,X⁆ ≤ D := by
    rw [← hgen]
    exact commutator_sup_le_of_relative_normal Q R X X D hQD hRQ hXQ hRX hXX
  have hQQ : ⁅Q,Q⁆ ≤ D := by
    conv_lhs => lhs; rw [← hgen]
    exact commutator_sup_le_of_relative_normal Q R X Q D hQD hRQ hXQ
      (by rw [commutator_comm]; exact hQR)
      (by rw [commutator_comm]; exact hQX)
  have hxC : x ∈ C := ⟨(pCoreIn_le 2 H) hxQ, by
    intro u hu
    exact mem_centralizer_singleton_iff.mp ((hQQ (hderived.ge hu)).2)⟩
  have hxOmega : x ∈ omegaOneAmbient C :=
    (omegaOneAmbient_le_iff C (omegaOneAmbient C)).mp le_rfl x hxC hx2
  have hOmega : omegaOneAmbient C = U := source_quintic_full_kernel_omega
    hG T hempty hM hu hmany hcard e H hH hi
  rw [hOmega] at hxOmega
  exact hxR (hUR hxOmega)

end CFSG.Quasithin.Chapter14.Section06
