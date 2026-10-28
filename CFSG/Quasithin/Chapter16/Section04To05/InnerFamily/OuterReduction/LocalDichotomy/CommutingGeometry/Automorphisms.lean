module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OuterReduction.LocalDichotomy.CommutingGeometry.AlternatingSix
public import Theory.GroupTheory.NilpotentCommutingConjugate
public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Fixed involutory displacements of outer involutions

An involution fixes some Sylow two-subgroup setwise. If its action on that
Sylow subgroup is nontrivial, normalizer growth in the holomorph gives a
distinct commuting conjugate. Otherwise 16.1.6 gives the actual A₆ model,
where the finite permutation calculation supplies the same witness.

The output a(q)q⁻¹ is intrinsic. It can therefore be used both on L and
on the actual quotient L/O₂(L), without asserting that quotient fixed points
lift to fixed points in L. The exact earlier 16.1.6 alternative remains an
explicit premise; this module does not prove that classification theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.1172 and 1190, the paragraph immediately after (+).
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise

namespace CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy.CommutingGeometry
variable {H : Type*} [Group H] [Finite H]

/-- Apply two-group normalizer growth in the holomorph to an involution
acting nontrivially on an invariant two-subgroup. The resulting displacement
is an involution fixed by the original automorphism. -/
theorem exists_fixed_displacement_of_noncentral_two_subgroup (a : MulAut H) (ha : orderOf a = 2)
    (P : Subgroup H) (hP : IsPGroup 2 P)
    (hst : ∀ q ∈ P, a q ∈ P) (hnc : ¬ ∀ q ∈ P, a q = q) :
    ∃ q : H, orderOf (a q * q⁻¹) = 2 ∧ a (a q * q⁻¹) = a q * q⁻¹ := by
  let φ : MulAut H →* MulAut H := MonoidHom.id _
  let E := H ⋊[φ] MulAut H
  let : Finite E := Finite.of_equiv (H × MulAut H) SemidirectProduct.equivProd.symm
  let f : H →* E := SemidirectProduct.inl
  let r : E := SemidirectProduct.inr a
  let Q : Subgroup E := P.map f
  have hOne : (1 : MulAut H).symm = 1 := rfl
  have haa (q : H) : a (a q) = q := by
    have he := congrArg (fun b : MulAut H => b q) (ha ▸ pow_orderOf_eq_one a)
    exact he
  have hr2 : orderOf r = 2 :=
    (orderOf_injective SemidirectProduct.inr SemidirectProduct.inr_injective a).trans ha
  have heq (q : H) : MulAut.conj r (f q) = f (a q) := by
    dsimp [f, r, E, MulAut.conj_apply]
    rw [← map_inv]
    exact (SemidirectProduct.inl_aut (φ := φ) a q).symm
  have hrN : r ∈ normalizer (Q : Set E) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨a q, hst q hq, (heq q).symm⟩
    · intro hx
      obtain ⟨q, hq, hqe⟩ := hx
      refine ⟨a q, hst q hq, ?_⟩
      have hh := congrArg (MulAut.conj r) hqe
      rw [heq] at hh
      have hrr : MulAut.conj r (MulAut.conj r x) = x := by
        change (MulAut.conj r * MulAut.conj r) x = x
        rw [← map_mul, show r * r = 1 by simpa only [pow_two, hr2] using pow_orderOf_eq_one r,
          map_one]
        rfl
      exact hh.trans hrr
  have hrC : r ∉ centralizer (Q : Set E) := by
    intro hc
    apply hnc
    intro q hq
    apply (show Function.Injective f from SemidirectProduct.inl_injective)
    rw [← heq, MulAut.conj_apply]
    rw [← hc (f q) ⟨q, hq, rfl⟩, mul_inv_cancel_right]
  obtain ⟨l, ⟨q, hq, rfl⟩, hne, hc⟩ :=
    exists_distinct_commuting_conjugate_in_two_subgroup Q (hP.map f) hr2 hrN hrC
  have hv : a q * q⁻¹ = q * (a q)⁻¹ := by
    have hh := congrArg SemidirectProduct.left hc.eq
    dsimp [f, r, φ, E, MulAut.conj_apply] at hh
    simpa [haa, hOne] using hh
  refine ⟨q, orderOf_eq_prime ?_ ?_, ?_⟩
  · rw [pow_two]
    calc
      (a q * q⁻¹) * (a q * q⁻¹) = (a q * q⁻¹) * (q * (a q)⁻¹) := by rw [← hv]
      _ = 1 := by group
  · intro hv1
    apply hne
    have haq : a q = q := mul_inv_eq_one.mp hv1
    apply SemidirectProduct.ext
    · dsimp [f, r, φ, E, MulAut.conj_apply]
      simp [haq, hOne]
    · dsimp [f, r, φ, E, MulAut.conj_apply]
      simp
  · rw [map_mul, map_inv, haa, hv]

private theorem invariant_sylow (a : MulAut H) (ha : orderOf a = 2) :
    ∃ P : Sylow 2 H, ∀ q ∈ P, a q ∈ P := by
  have hp : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨P, hP⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 H)
    (not_dvd_card_sylow 2 H)
  refine ⟨P, ?_⟩
  intro q hq
  have he : (⟨a, mem_zpowers a⟩ : zpowers a) • P = P := hP ⟨a, mem_zpowers a⟩
  have he' := congrArg (fun S : Sylow 2 H => (S : Subgroup H)) he
  change a q ∈ (P : Subgroup H)
  rw [← he']
  exact ⟨q, hq, rfl⟩

/-- The precise earlier alternative used here from 16.1.6. The exceptional
branch includes an actual A₆ equivalence and an implementing S₆ permutation. -/
@[expose] def SylowCentralizingAlternative (a : MulAut H) : Prop :=
  ∀ P : Sylow 2 H, (∀ q ∈ P, a q = q) →
    (∃ q : H, a = MulAut.conj q) ∨
      ∃ e : H ≃* alternatingGroup (Fin 6), ∃ σ : Equiv.Perm (Fin 6),
        ∀ q, e (a q) = AlternatingSix.ShadowLocal.permutationAction σ (e q)

/-- The intrinsic form of the paragraph after (+): an outer involution has
an involutory fixed displacement, conditional only on the earlier 16.1.6
alternative. A fixed Sylow exists because the Sylow count is odd. -/
theorem exists_fixed_displacement (a : MulAut H) (ha : orderOf a = 2)
    (hout : ¬ ∃ q : H, a = MulAut.conj q)
    (hearlier : SylowCentralizingAlternative a) :
    ∃ q : H, orderOf (a q * q⁻¹) = 2 ∧ a (a q * q⁻¹) = a q * q⁻¹ := by
  obtain ⟨P, hP⟩ := invariant_sylow a ha
  by_cases hfix : ∀ q ∈ P, a q = q
  · rcases hearlier P hfix with hi | ⟨e, σ, he⟩
    · exact (hout hi).elim
    · exact exists_fixed_displacement_of_alternatingSix a ha e σ he
  · exact exists_fixed_displacement_of_noncentral_two_subgroup a ha P P.isPGroup' hP hfix

end CFSG.Quasithin.Chapter16.Intersections.OuterReduction.LocalDichotomy.CommutingGeometry
