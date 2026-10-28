module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PairedEndpointConstruction
public import Theory.GroupTheory.PrimeCyclicCoverage

/-!
# Actual endpoint reflections inverting the chosen common cubic

The native diagonal cubic and Weyl involution lie in the actual complement.
Sylow conjugacy transports their inversion relation to any specified cubic
of the same endpoint. The common subgroup has a normal two-subgroup of
index three, so none of these inverting involutions lies in the intersection.
This constructs the reflections in the original group. Their product
centralizes the chosen cubic; its order is a separate source obligation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.HigmanSims
open Representation.SL2FourNatural
open Representation.SL2FourNatural.PointCommutator
open Representation.SL2FourNatural.BorelFactors
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

private def nativeReflection : SL := ⟨!![0, 1; 1, 0], by decide +kernel⟩

private theorem native_relations : nativeReflection ^ 2 = 1 ∧ nativeReflection ≠ 1 ∧
    cubic ^ 3 = 1 ∧ cubic ≠ 1 ∧ nativeReflection * cubic * nativeReflection⁻¹ = cubic⁻¹ := by
  decide +kernel

/-- Every specified cubic of the constructed endpoint is inverted by an
actual involution of that endpoint. -/
theorem NaturalEndpointData.cubic_inverting_involution
    {A : Subgroup G} [IsElementaryAbelian 2 A] (d : NaturalEndpointData A)
    (t : G) (ht : t ∈ d.carrier) (ht3 : orderOf t = 3) :
    ∃ r : G, r ∈ d.carrier ∧ orderOf r = 2 ∧ r * t * r⁻¹ = t⁻¹ := by
  let j : SL →* d.carrier := (inclusion d.complement_le).comp d.complement_equiv.symm.toMonoidHom
  have hj : Function.Injective j := (inclusion_injective d.complement_le).comp
    d.complement_equiv.symm.injective
  have hc3 : orderOf (j cubic) = 3 :=
    (orderOf_injective j hj cubic).trans (orderOf_eq_prime native_relations.2.2.1 native_relations.2.2.2.1)
  have hr2 : orderOf (j nativeReflection) = 2 :=
    (orderOf_injective j hj nativeReflection).trans (orderOf_eq_prime native_relations.1 native_relations.2.1)
  let T : d.carrier := ⟨t, ht⟩
  have hT : orderOf T = 3 := (orderOf_coe T).symm.trans ht3
  obtain ⟨k, g, hg⟩ := PrimeCyclicCoverage.exists_conjugate_pow_of_prime_sq_not_dvd
    (by decide : Nat.Prime 3) (by rw [d.carrier_card]; decide) hc3 hT
  let a := MulAut.conj g
  have hT' : T = a ((j cubic) ^ k) := hg
  have hi : j nativeReflection * j cubic * (j nativeReflection)⁻¹ = (j cubic)⁻¹ := by
    simpa only [map_mul, map_inv] using congrArg j native_relations.2.2.2.2
  have hik : j nativeReflection * (j cubic)^k * (j nativeReflection)⁻¹ = ((j cubic)^k)⁻¹ := by
    rw [← conj_pow, hi, inv_pow]
  have hir : a (j nativeReflection) * T * (a (j nativeReflection))⁻¹ = T⁻¹ := by
    rw [hT', ← map_inv, ← map_mul, ← map_mul, hik, map_inv]
  refine ⟨a (j nativeReflection), (a (j nativeReflection)).property, ?_, congrArg Subtype.val hir⟩
  exact (orderOf_coe _).trans ((a.orderOf_eq _).trans hr2)

omit [Finite G] in
private theorem inverting_not_in_common
    (S J : Subgroup G) (hSJ : S ≤ J) (hJN : J ≤ normalizer (S : Set G))
    (hS : Nat.card S = 64) (hJ : Nat.card J = 192)
    (t : G) (ht : t ∈ J) (ht3 : orderOf t = 3)
    (r : G) (hr2 : orderOf r = 2) (hi : r * t * r⁻¹ = t⁻¹) : r ∉ J := by
  intro hr
  let N := S.subgroupOf J
  let : N.Normal := (normal_subgroupOf_iff_le_normalizer hSJ).mpr hJN
  have hN : Nat.card N = 64 := (Nat.card_congr (subgroupOfEquivOfLe hSJ).toEquiv).trans hS
  have hQ : Nat.card (J ⧸ N) = 3 := by
    have hc := card_eq_card_quotient_mul_card_subgroup N
    rw [hJ, hN] at hc
    omega
  let q := QuotientGroup.mk' N
  let R : J := ⟨r, hr⟩
  let T : J := ⟨t, ht⟩
  have hR : orderOf R = 2 := (orderOf_coe R).symm.trans hr2
  have hT : orderOf T = 3 := (orderOf_coe T).symm.trans ht3
  have hqR : q R = 1 := orderOf_eq_one_iff.mp <| Nat.eq_one_of_dvd_coprimes
    (by decide : Nat.Coprime 2 3)
    (hR ▸ orderOf_map_dvd q R) (hQ ▸ orderOf_dvd_natCard (q R))
  have hi' : R * T * R⁻¹ = T⁻¹ := Subtype.ext hi
  have he := congrArg q hi'
  simp only [map_mul, map_inv, hqR, one_mul, inv_one, mul_one] at he
  have htwo : (q T)^2 = 1 := by
    calc
      (q T)^2 = (q T)⁻¹ * q T := by simpa only [pow_two] using congrArg (fun x => x * q T) he
      _ = 1 := inv_mul_cancel _
  have hqT : q T = 1 := orderOf_eq_one_iff.mp <| Nat.eq_one_of_dvd_coprimes
    (by decide : Nat.Coprime 2 3) (orderOf_dvd_of_pow_eq_one htwo)
    (hT ▸ orderOf_map_dvd q T)
  have htS : t ∈ S := (QuotientGroup.eq_one_iff T).mp hqT
  have hd : 3 ∣ 64 := by
    have hh := orderOf_dvd_natCard (⟨t, htS⟩ : S)
    rwa [← orderOf_coe, ht3, hS] at hh
  norm_num at hd

/-- Original HS data construct actual endpoint involutions outside the
whole intersection. They both invert the same original cubic, so their
product centralizes it. No order for that product is assumed or asserted. -/
theorem TypeAt.exists_paired_cubic_reflections (h : TypeAt z V) :
    ∃ (W A B : Subgroup G) (p t : G) (hAE : IsElementaryAbelian 2 A)
      (hBE : IsElementaryAbelian 2 B),
      letI := hAE
      letI := hBE
      W ≤ V ∧ Nat.card W = 4 ∧ Nat.card A = 16 ∧ Nat.card B = 16 ∧
      p ∈ (normalizer (V : Set G)).pCoreIn 2 ∧ p ^ 2 ∉ W ∧
      B = A.map (MulAut.conj p).toMonoidHom ∧ A ⊓ B = W ∧
      Nat.card (A ⊔ B : Subgroup G) = 64 ∧ orderOf t = 3 ∧
      ∃ (dA : NaturalEndpointData A) (dB : NaturalEndpointData B),
        B ≤ dA.carrier ∧ A ≤ dB.carrier ∧ t ∈ dA.carrier ⊓ dB.carrier ∧
        dA.carrier ⊓ dB.carrier = (A ⊔ B) ⊔ zpowers t ∧
        Nat.card (dA.carrier ⊓ dB.carrier : Subgroup G) = 192 ∧
        ∃ r s : G, r ∈ dA.carrier ∧ s ∈ dB.carrier ∧
          r ∉ dA.carrier ⊓ dB.carrier ∧ s ∉ dA.carrier ⊓ dB.carrier ∧
          orderOf r = 2 ∧ orderOf s = 2 ∧
          r * t * r⁻¹ = t⁻¹ ∧ s * t * s⁻¹ = t⁻¹ ∧
          r * s ∈ centralizer ({t} : Set G) ∧ r * s ≠ 1 := by
  obtain ⟨W,A,B,p,t,hAE,hBE,hAB,hBA,hWV,hW4,hA16,hB16,hp,hpW,hB,
    _,_,_,_,hi,_,h64,_,_,_,_,_,ht3,_,_,h192,dA,dB,hBdA,hAdB,htd,hI,_,_⟩ :=
    h.exists_paired_natural_endpoints
  let := hAE
  let := hBE
  let S := A ⊔ B
  let J := dA.carrier ⊓ dB.carrier
  have hSJ : S ≤ J := sup_le (le_inf dA.kernel_le hAdB) (le_inf hBdA dB.kernel_le)
  have hJN : J ≤ normalizer (S : Set G) := by
    apply le_trans (le_inf (inf_le_left.trans dA.normalizes) (inf_le_right.trans dB.normalizes))
    exact normalizer_inf_normalizer_le_normalizer_sup A B
  have hJ : Nat.card J = 192 := by change Nat.card (dA.carrier ⊓ dB.carrier : Subgroup G) = 192; rw [hI]; exact h192
  obtain ⟨r,hr,hr2,hrt⟩ := dA.cubic_inverting_involution t htd.1 ht3
  obtain ⟨s,hs,hs2,hst⟩ := dB.cubic_inverting_involution t htd.2 ht3
  have hrJ : r ∉ J := inverting_not_in_common S J hSJ hJN h64 hJ t htd ht3 r hr2 hrt
  have hsJ : s ∉ J := inverting_not_in_common S J hSJ hJN h64 hJ t htd ht3 s hs2 hst
  have hc : (r*s) * t * (r*s)⁻¹ = t := by
    calc
      (r*s) * t * (r*s)⁻¹ = r * (s*t*s⁻¹) * r⁻¹ := by group
      _ = r * t⁻¹ * r⁻¹ := by rw [hst]
      _ = (r*t*r⁻¹)⁻¹ := by group
      _ = t := by rw [hrt, inv_inv]
  have hcentral : r*s ∈ centralizer ({t} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg (fun x => x*(r*s)) hc
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh
  have hne : r*s ≠ 1 := by
    intro he
    have hrB : r ∈ dB.carrier := (eq_inv_of_mul_eq_one_left he) ▸ dB.carrier.inv_mem hs
    exact hrJ ⟨hr,hrB⟩
  exact ⟨W,A,B,p,t,hAE,hBE,hWV,hW4,hA16,hB16,hp,hpW,hB,hi,h64,ht3,
    dA,dB,hBdA,hAdB,htd,hI,hJ,r,s,hr,hs,hrJ,hsJ,hr2,hs2,hrt,hst,hcentral,hne⟩

end CFSG.Quasithin.HigmanSims
