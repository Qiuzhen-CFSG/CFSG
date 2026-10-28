module

public import Theory.SpecificGroups.SymmetricFive.StarCenterGeometry
public import Theory.SpecificGroups.SymmetricFive.PentagonNormalizer
public import Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups
public import Theory.GroupTheory.PrimeSubgroupInvolution

/-!
# Four-cycles and their squares have the same pentagon normalizers

An involution normalizing a five-subgroup of S5 inverts it, since the
five-centralizer has odd order. A small five-letter certificate handles
one standard four-cycle; cycle-type conjugacy transports the result to
every four-cycle. Thus the four-cycle and its square normalize exactly
the same two Sylow five-subgroups. The certificate tests only individual
permutations, never subgroup lattices.

Source application: the two original parabolics E(z) on printed p.443
of Aschbacher--Smith, before J.4.8. The square-root implication places the
actual order-four actor in the index-two overgroup of a source parabolic.
-/

public section

noncomputable section
namespace Theory.SpecificGroups.SymmetricFive.SquareNormalizer
open Subgroup
local notation "D" => Equiv.Perm (Fin 5)
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private def q0 : D := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3
private theorem four_type : ∀q:D,q^4=1 → q^2≠1 → q.cycleType={4} := by
  decide +kernel
private theorem standard_certificate : ∀x:D,x^5=1 → x≠1 →
    q0^2*x*(q0^2)⁻¹=x⁻¹ → ∃k:Fin 5,q0*x*q0⁻¹=x^k.val := by
  decide +kernel

private theorem root_power (q x:D) (hq:orderOf q=4) (hx:x^5=1) (hn:x≠1)
    (hi:q^2*x*(q^2)⁻¹=x⁻¹) : ∃k:Fin 5,q*x*q⁻¹=x^k.val := by
  have hq4:q^4=1 := by simpa only [hq] using pow_orderOf_eq_one q
  have hq2:q^2≠1 := by
    intro h
    have hh:=orderOf_dvd_of_pow_eq_one h
    rw [hq] at hh
    contradiction
  have htype0:q0.cycleType={4} := by decide +kernel
  obtain ⟨c,hc⟩ := isConj_iff.mp (Equiv.Perm.isConj_of_cycleType_eq
    ((four_type q hq4 hq2).trans htype0.symm))
  let a:=MulAut.conj c
  have haq:a q=q0 := hc
  have hax:(a x)^5=1 := by rw [←map_pow,hx,map_one]
  have han:a x≠1 := by intro h;apply hn;exact a.injective (h.trans a.map_one.symm)
  have hai:q0^2*a x*(q0^2)⁻¹=(a x)⁻¹ := by
    have hh:=congrArg a hi
    simpa only [map_mul,map_inv,map_pow,haq] using hh
  obtain ⟨k,hk⟩:=standard_certificate (a x) hax han hai
  refine ⟨k,a.injective ?_⟩
  simpa only [map_mul,map_inv,map_pow,haq] using hk

/-- A four-cycle normalizes every five-subgroup normalized by its square. -/
theorem square_normalizer (P:Subgroup D) (hP:Nat.card P=5) (q:D) (hq:orderOf q=4)
    (hn:q^2∈normalizer (P:Set D)) : q∈normalizer (P:Set D) := by
  have hv:orderOf (q^2)=2 := by rw [orderOf_pow,hq];decide
  have hinv:∀x∈P,q^2*x*(q^2)⁻¹=x⁻¹ := by
    rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one P
      (by rw [hP];decide) (q^2) ((orderOf_eq_prime_iff.mp hv).1) hn with hc|hi
    · have hvc:q^2∈centralizer (P:Set D) := by
        intro x hx
        exact (hc x hx).eq.symm
      have hh:=orderOf_dvd_natCard (⟨q^2,hvc⟩:centralizer (P:Set D))
      rw [←orderOf_coe,hv,Equiv.Perm.five_subgroup_centralizer_card P hP] at hh
      contradiction
    · exact hi
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro y ⟨x,hx,rfl⟩
    by_cases h:x=1
    · simp [h]
    have hp:x^5=1 := by
      have hh:=pow_card_eq_one' (x:=(⟨x,hx⟩:P))
      rw [hP] at hh
      exact congrArg Subtype.val hh
    obtain ⟨k,hk⟩:=root_power q x hq hp h (hinv x hx)
    change q*x*q⁻¹∈P
    rw [hk]
    exact pow_mem hx _
  · rw [card_map_of_injective (MulAut.conj q).injective]

/-- A four-cycle and its square normalize exactly the same five-subgroups. -/
theorem normalizer_square_iff (P:Subgroup D) (hP:Nat.card P=5) (q:D) (hq:orderOf q=4) :
    q^2∈normalizer (P:Set D) ↔ q∈normalizer (P:Set D) :=
  ⟨square_normalizer P hP q hq,fun h => pow_mem h 2⟩

private theorem involution_normalizer_iff (P:Subgroup D) (hP:Nat.card P=5)
    (v:D) (hv:orderOf v=2) :
    v∈normalizer (P:Set D) ↔ ∀x∈P,v*x*v⁻¹=x⁻¹ := by
  constructor
  · intro hn
    rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one P
      (by rw [hP];decide) v ((orderOf_eq_prime_iff.mp hv).1) hn with hc|hi
    · have hvc:v∈centralizer (P:Set D) := by
        intro x hx
        exact (hc x hx).eq.symm
      have hh:=orderOf_dvd_natCard (⟨v,hvc⟩:centralizer (P:Set D))
      rw [←orderOf_coe,hv,Equiv.Perm.five_subgroup_centralizer_card P hP] at hh
      contradiction
    · exact hi
  · intro hi
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro x ⟨y,hy,rfl⟩
      change v*y*v⁻¹∈P
      rw [hi y hy]
      exact inv_mem hy
    · rw [card_map_of_injective (MulAut.conj v).injective]

/-- Exactly two five-normalizers contain a given four-cycle. -/
theorem sylow_normalizer_count (q:D) (hq:orderOf q=4) :
    Nat.card {P:Sylow 5 D // q∈normalizer ((P:Subgroup D):Set D)}=2 := by
  have hv:orderOf (q^2)=2 := by rw [orderOf_pow,hq];decide
  have he:q^2∈alternatingGroup (Fin 5) := by
    apply Equiv.Perm.mem_alternatingGroup.mpr
    rw [map_pow,Int.units_sq]
  let e := Equiv.subtypeEquiv (Equiv.refl (Sylow 5 D))
    (p:=fun P:Sylow 5 D => q∈normalizer ((P:Subgroup D):Set D))
    (q:=fun P:Sylow 5 D => ∀x∈(P:Subgroup D),q^2*x*(q^2)⁻¹=x⁻¹)
    (fun P => (normalizer_square_iff P (FiveNormalizerOvergroups.card_sylow P) q hq).symm.trans
      (involution_normalizer_iff P (FiveNormalizerOvergroups.card_sylow P) (q^2) hv))
  exact (Nat.card_congr e).trans (StarCenterGeometry.inverted_sylow_count (q^2) hv he)

/-- The same two five-normalizers contain the square of a given four-cycle. -/
theorem sylow_square_normalizer_count (q:D) (hq:orderOf q=4) :
    Nat.card {P:Sylow 5 D // q^2∈normalizer ((P:Subgroup D):Set D)}=2 := by
  let e := Equiv.subtypeEquiv (Equiv.refl (Sylow 5 D))
    (p:=fun P:Sylow 5 D => q^2∈normalizer ((P:Subgroup D):Set D))
    (q:=fun P:Sylow 5 D => q∈normalizer ((P:Subgroup D):Set D))
    (fun P => normalizer_square_iff P (FiveNormalizerOvergroups.card_sylow P) q hq)
  exact (Nat.card_congr e).trans (sylow_normalizer_count q hq)

end Theory.SpecificGroups.SymmetricFive.SquareNormalizer
