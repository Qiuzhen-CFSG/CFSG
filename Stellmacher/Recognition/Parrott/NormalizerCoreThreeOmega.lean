module

public import Stellmacher.Recognition.Parrott.NormalizerCoreOmegaQuotient
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Sylow-three fixed points lie in the omega subgroup

In the actual quotient N/Ω₁(K)≃S₄, a nonidentity element of the supplied
Sylow three-subgroup has a centralizer of exponent three. A fixed element
of K has two-power order, so its image in that quotient is trivial.
This places C_K(Q) inside Ω₁(K), retaining the supplied action and Q.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
p.677, the deductions following N/U≃S₄.
-/

open Subgroup
namespace Stellmacher.Recognition.ParrottSecondElementaryData
variable {G : Type*} [Group G] [Finite G] {z : G}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem perm_four_three_centralizer :
    ∀ r a : Equiv.Perm (Fin 4), r ^ 3 = 1 → r ≠ 1 →
    a * r = r * a → a ^ 3 = 1 := by
  decide +kernel

/-- Every element of the actual two-core centralizing the supplied Sylow
three-subgroup lies in the ambient image of its omega subgroup. -/
public theorem normalizer_three_centralizer_le_omega (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let U := omega₁ K (p := 2)
    let X := K.map N.subtype
    let A := (Q : Subgroup N).map N.subtype
    X ⊓ centralizer (A : Set G) ≤ U.map (N.subtype.comp K.subtype) := by
  intro N K U X A
  let V := U.map K.subtype
  let : U.Characteristic := omega₁_characteristic K
  let : V.Normal := ConjAct.normal_of_characteristic_of_normal
  obtain ⟨e⟩ := d.normalizer_omega_quotient h hN hproper
  let f : N →* Equiv.Perm (Fin 4) := e.toMonoidHom.comp (QuotientGroup.mk' V)
  have hker : f.ker = V := by
    ext n
    change e (QuotientGroup.mk' V n) = 1 ↔ n ∈ V
    rw [← map_one e, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff n
  have hQcard : Nat.card Q = 3 := d.normalizer_three_card h hN hproper Q
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := Q) 3 (by simp [hQcard])
  have hq3 : (q : N) ^ 3 = 1 := by
    exact congrArg (Q : Subgroup N).subtype (hq ▸ pow_orderOf_eq_one q)
  have hqr : f (q : N) ≠ 1 := by
    intro hh
    have hqV : (q : N) ∈ V := by
      rw [← hker]
      exact hh
    have hcV : Nat.card V = 256 :=
      (card_map_of_injective K.subtype_injective).trans
        (d.normalizer_core_omega_structure h hN hproper).1
    have horder : orderOf (⟨(q : N), hqV⟩ : V) = 3 :=
      (orderOf_injective V.subtype V.subtype_injective _).symm.trans
        ((orderOf_injective (Q : Subgroup N).subtype (Q : Subgroup N).subtype_injective q).trans hq)
    have hd := orderOf_dvd_natCard (⟨(q : N), hqV⟩ : V)
    rw [horder, hcV] at hd
    norm_num at hd
  rintro x ⟨hxX, hxC⟩
  obtain ⟨k, hk, rfl⟩ := hxX
  have hx3 : (f k) ^ 3 = 1 := perm_four_three_centralizer (f (q : N)) (f k)
    (by rw [← map_pow, hq3, map_one]) hqr (by
      have hh := hxC ((q : N) : G) (mem_map_of_mem N.subtype q.property)
      have hn : k * (q : N) = (q : N) * k := by
        apply Subtype.ext
        exact hh.symm
      simpa only [map_mul] using congrArg f hn)
  have hx1024 : (f k) ^ 1024 = 1 := by
    have hp := pow_card_eq_one' (x := (⟨k, hk⟩ : K))
    rw [(d.normalizer_core_order h hN hproper).2.1] at hp
    have hp' : k ^ 1024 = 1 := congrArg Subtype.val hp
    simpa only [map_pow, map_one] using congrArg f hp'
  have hxker : k ∈ f.ker := by
    apply orderOf_eq_one_iff.mp
    exact Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 3 1024)
      (orderOf_dvd_of_pow_eq_one hx3) (orderOf_dvd_of_pow_eq_one hx1024)
  rw [hker] at hxker
  have hh := mem_map_of_mem N.subtype hxker
  simpa only [V, map_map] using hh
/-- The literal conjugation action of the supplied Q on the intrinsic core,
with its fixed subgroup contained in the intrinsic omega subgroup. -/
public theorem exists_normalizer_three_core_action_fixed_le_omega (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    ∃ action : Q →* MulAut K,
      (∀ q : Q, ∀ k : K,
        (((action q k : K) : N) : G) =
          ((q : N) : G) * ((k : N) : G) * ((q : N) : G)⁻¹) ∧
      letI : MulDistribMulAction Q K := MulDistribMulAction.compHom K action
      FixedPoints.subgroup Q K ≤ omega₁ K (p := 2) := by
  intro N K
  have hQK : (Q : Subgroup N) ≤ normalizer (K : Set N) := by
    rw [show normalizer (K : Set N) = ⊤ from normalizer_eq_top K]
    exact le_top
  let action : Q →* MulAut K := K.normalizerMonoidHom.comp (inclusion hQK)
  refine ⟨action, ?_, ?_⟩
  · intro q k
    rfl
  · let : MulDistribMulAction Q K := MulDistribMulAction.compHom K action
    let i := N.subtype.comp K.subtype
    intro k hk
    have hC : i k ∈ centralizer ((Q : Subgroup N).map N.subtype : Set G) := by
      rintro a ⟨q, hq, rfl⟩
      have heq := congrArg i (hk ⟨q, hq⟩)
      change (q : G) * i k * (q : G)⁻¹ = i k at heq
      exact mul_inv_eq_iff_eq_mul.mp heq
    have hm := d.normalizer_three_centralizer_le_omega h hN hproper Q
      (show i k ∈ K.map N.subtype ⊓
        centralizer ((Q : Subgroup N).map N.subtype : Set G) from
        ⟨mem_map_of_mem N.subtype k.property, hC⟩)
    obtain ⟨u, hu, heq⟩ := hm
    exact ((N.subtype_injective.comp K.subtype_injective) heq) ▸ hu


end Stellmacher.Recognition.ParrottSecondElementaryData
