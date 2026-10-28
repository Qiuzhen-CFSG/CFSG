module

public import Theory.Mathieu.SchurMultipliers.M23TwoKernelSource.Squares
public import Theory.Alternating.proposition_5_2_7_8
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Lifting the marked heptad A₇ complement

The derived subgroup of the complement's central preimage is a perfect
cover of A₇. If its kernel had order two, a double transposition would
have a lift with nonidentity square, by Schur's proved lift formula.
The native M₂₃ fusion argument excludes that possibility, so the derived
projection is an isomorphism and gives the required marked section.
-/

public section
noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open GLS3.Chapter5 GLS3.Chapter5.SchurPresentation
namespace Sporadic.Mathieu.SchurMultipliers.M23TwoKernelSource
open M23Geometry

private theorem no_alternating_double_small {D : Type} [Group D] [Finite D]
    [IsQuasisimple D] (q : Covering D (alternatingGroup (Fin 7)))
    (hcard : Nat.card q.toMonoidHom.ker = 2)
    (hsq : ∀ x : D, orderOf (q x) = 2 → x ^ 2 = 1) : False := by
  let t : alternatingGroup (Fin 7) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
      simp [Equiv.Perm.mem_alternatingGroup, map_mul]⟩
  have ht : orderOf t = 2 := orderOf_eq_prime_iff.mpr
    ⟨by decide +kernel, by decide +kernel⟩
  have hs : t.val.support.card = 4 * 1 := by decide +kernel
  obtain ⟨x, hx⟩ := q.surjective t
  change q x = t at hx
  have h := doubleCoverInvolutionLift_sq_of_support_card 2 q hcard
    1 (by decide) t ht hs x hx
  have hx2 : x ^ 2 = 1 := hsq x (by rw [hx]; exact ht)
  have hz : ((DoubleCoverUniqueness.kernelInvolution q.toMonoidHom hcard :
      q.toMonoidHom.ker) : D) = 1 := by simpa only [hx2, pow_one] using h.symm
  exact DoubleCoverUniqueness.kernelInvolution_ne_one q.toMonoidHom hcard (Subtype.ext hz)

private theorem no_alternating_double {D : Type*} [Group D] [Finite D]
    [IsQuasisimple D] (q : Covering D (alternatingGroup (Fin 7)))
    (hcard : Nat.card q.toMonoidHom.ker = 2)
    (hsq : ∀ x : D, orderOf (q x) = 2 → x ^ 2 = 1) : False := by
  obtain ⟨U, iU, finU, ⟨s⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv.{_, 0} D
  let := iU
  let := finU
  let : IsQuasisimple U := IsQuasisimple.of_mulEquiv s
  let qU := q.comp (Covering.ofMulEquiv s.symm)
  have hcU : Nat.card qU.toMonoidHom.ker = 2 := by
    have he : qU.toMonoidHom.ker ≃ q.toMonoidHom.ker := {
      toFun := fun x => ⟨s.symm x, x.property⟩
      invFun := fun x => ⟨s x, by
        change q (s.symm (s x)) = 1
        rw [s.symm_apply_apply]
        exact x.property⟩
      left_inv := fun x => Subtype.ext (s.apply_symm_apply x)
      right_inv := fun x => Subtype.ext (s.symm_apply_apply x) }
    exact (Nat.card_congr he).trans hcard
  apply no_alternating_double_small qU hcU
  intro x hx
  apply s.symm.injective
  simpa only [map_pow, map_one] using hsq (s.symm x) hx

/-- The actual alternating complement has a section in every central
double cover of native M₂₃, preserving its original inclusion. -/
theorem exists_alternating_section {E : Type*} [Group E] [Finite E]
    (f : Cover E M23) (hcard : Nat.card f.toMonoidHom.ker = 2) :
    ∃ s : alternatingGroup (Fin 7) →* E,
      f.toMonoidHom.comp s = heptadStabilizer.subtype.comp AlternatingSection.s := by
  let j := heptadStabilizer.subtype.comp AlternatingSection.s
  let P : Subgroup (E × alternatingGroup (Fin 7)) := {
    carrier := {z | f.toMonoidHom z.1 = j z.2}
    one_mem' := by simp
    mul_mem' := by
      intro x y hx hy
      change f.toMonoidHom x.1 = j x.2 at hx
      change f.toMonoidHom y.1 = j y.2 at hy
      change f.toMonoidHom (x.1 * y.1) = j (x.2 * y.2)
      rw [map_mul, map_mul, hx, hy]
    inv_mem' := by
      intro x hx
      change f.toMonoidHom x.1 = j x.2 at hx
      change f.toMonoidHom x.1⁻¹ = j x.2⁻¹
      rw [map_inv, map_inv, hx] }
  let q : P →* alternatingGroup (Fin 7) := (MonoidHom.snd E _).comp P.subtype
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨x, hx⟩ := f.surjective (j a)
    exact ⟨⟨(x, a), hx⟩, rfl⟩
  have hqc : q.ker ≤ center P := by
    intro x hx
    have hx2 : x.val.2 = 1 := hx
    have hx1 : x.val.1 ∈ f.toMonoidHom.ker := by
      change f.toMonoidHom x.val.1 = 1
      rw [x.property, hx2, map_one]
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    apply Prod.ext
    · exact mem_center_iff.mp (f.ker_le_center hx1) y.val.1
    · change y.val.2 * x.val.2 = x.val.2 * y.val.2
      rw [hx2, mul_one, one_mul]
  let eker : q.ker ≃* f.toMonoidHom.ker := {
    toFun := fun x => ⟨x.val.val.1, by
      change f.toMonoidHom x.val.val.1 = 1
      rw [x.val.property]
      change j (q x.val) = 1
      rw [x.property, map_one]⟩
    invFun := fun x => ⟨⟨(x.val, 1), by
      change f.toMonoidHom x.val = j 1
      rw [map_one]
      exact x.property⟩, rfl⟩
    left_inv := by
      intro x
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · exact x.property.symm
    right_inv := by intro x; rfl
    map_mul' := by intro x y; rfl }
  have hqcard : Nat.card q.ker = 2 := (Nat.card_congr eker.toEquiv).trans hcard
  let D := commutator P
  let qD : D →* alternatingGroup (Fin 7) := q.comp D.subtype
  have hDs : Function.Surjective qD := by
    have hm : D.map q = ⊤ := by
      change (commutator P).map q = ⊤
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hq]
      exact Group.IsPerfect.commutator_eq_top
    intro a
    obtain ⟨x, hx, hxa⟩ := (show a ∈ D.map q by rw [hm]; trivial)
    exact ⟨⟨x, hx⟩, hxa⟩
  let : Group.IsPerfect D :=
    PerfectCentralCovering.commutator_isPerfect_of_surjective_of_ker_le_center q hq hqc
  let d : Cover D (alternatingGroup (Fin 7)) := {
    toMonoidHom := qD
    surjective := hDs
    isPerfect := inferInstance
    ker_le_center := by
      intro x hx
      rw [mem_center_iff]
      intro y
      apply Subtype.ext
      exact mem_center_iff.mp (hqc hx) y.val }
  let : IsQuasisimple D := d.isQuasisimple
  have hdcard : Nat.card qD.ker ∣ 2 := by
    rw [← hqcard]
    exact q.ker.card_comap_dvd_of_injective D.subtype D.subtype_injective
  have hd1 : Nat.card qD.ker = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdcard with h | h
    · exact h
    · exfalso
      apply no_alternating_double d.toCovering h
      intro x hx
      change orderOf (qD x) = 2 at hx
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · apply involution_lift_square f hcard
        have hmap : f.toMonoidHom x.val.val.1 = j (qD x) := x.val.property
        rw [hmap, ← map_pow, (orderOf_eq_prime_iff.mp hx).1, map_one]
      · exact (orderOf_eq_prime_iff.mp hx).1
  let eD : D ≃* alternatingGroup (Fin 7) := MulEquiv.ofBijective qD
    ⟨qD.ker_eq_bot_iff.mp (qD.ker.eq_bot_of_card_eq hd1), hDs⟩
  let s : alternatingGroup (Fin 7) →* E :=
    (MonoidHom.fst E _).comp (P.subtype.comp (D.subtype.comp eD.symm.toMonoidHom))
  refine ⟨s, ?_⟩
  apply MonoidHom.ext
  intro a
  change f.toMonoidHom (eD.symm a).val.val.1 = j a
  rw [(eD.symm a).val.property]
  change j (eD (eD.symm a)) = j a
  rw [eD.apply_symm_apply]

end Sporadic.Mathieu.SchurMultipliers.M23TwoKernelSource
