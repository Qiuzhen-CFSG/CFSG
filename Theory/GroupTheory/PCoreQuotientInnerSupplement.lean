module

public import Theory.GroupTheory.PCoreQuotientJoinAction
public import Theory.GroupTheory.SylowNormalizedSupIndex
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupAction.InnerSylow
/-!
# Factoring a prime-group supplement with inner quotient action

Suppose a prime-group R normalizes K, contains the ambient image of a
Sylow subgroup S of K, and acts inner on the centerless quotient K/O_p(K).
The inner image of S is Sylow in the inner automorphism group. It follows
that every R-action is supplied by S. The remaining factor is in the
literal quotient-action kernel, which is O_p(KR).

Thus R=S O_p(KR), with no splitting assumption. Source application:
Aschbacher–Smith 13.7.4(1), printed p.937.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Inner quotient action factors the original supplement through its embedded Sylow. -/
theorem sup_core_factor_of_inner_action (K R : Subgroup G)
    (hRK : R ≤ normalizer (K : Set G)) (hR : IsPGroup p R)
    (hc : center (K ⧸ pCore p K) = ⊥) (S : Sylow p K)
    (hSR : (S : Subgroup K).map K.subtype ≤ R)
    (hi : ∀ r : R, pCoreJoinAction p hRK (inclusion le_sup_right r) ∈
      MulAut.innerSubgroup (K ⧸ pCore p K)) :
    R = (S : Subgroup K).map K.subtype ⊔ (K ⊔ R).pCoreIn p := by
  let X := K ⊔ R
  let a := pCoreJoinAction p hRK
  let q := QuotientGroup.mk' (pCore p K)
  let S' := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let A := (R.subgroupOf X).map a
  have hA : IsPGroup p A := hR.comap_subtype.map a
  have hSA : (S' : Subgroup (K ⧸ pCore p K)).map MulAut.conj ≤ A := by
    rintro _ ⟨u,hu,rfl⟩
    obtain ⟨k,hk,rfl⟩ := hu
    refine ⟨inclusion le_sup_left k,?_,?_⟩
    · exact hSR (mem_map_of_mem K.subtype hk)
    · exact pCoreJoinAction_on_component p hRK k
  have haKer : a.ker = pCore p X := pCoreJoinAction_kernel p hRK hR hc
  apply le_antisymm
  · intro r hr
    let r' : X := ⟨r,mem_sup_right hr⟩
    have har : a r' ∈ A := mem_map_of_mem a hr
    have hir : a r' ∈ MulAut.innerSubgroup (K ⧸ pCore p K) := hi ⟨r,hr⟩
    obtain ⟨u,hu,heu⟩ := MulAut.mem_innerSylow_of_mem_inner S' A hA hSA har hir
    obtain ⟨k,hk,hku⟩ := hu
    let k' : X := inclusion le_sup_left k
    have hka : a k' = a r' := by
      rw [show a k' = MulAut.conj (q k) from pCoreJoinAction_on_component p hRK k]
      exact hku ▸ heu
    have hck : k'⁻¹ * r' ∈ pCore p X := by
      rw [←haKer,MonoidHom.mem_ker,map_mul,map_inv,hka,inv_mul_cancel]
    have hcG : (k : G)⁻¹ * r ∈ X.pCoreIn p := mem_map_of_mem X.subtype hck
    have hkG : (k : G) ∈ (S : Subgroup K).map K.subtype := mem_map_of_mem _ hk
    have hh := (mem_sup_left hkG : (k : G) ∈
      (S : Subgroup K).map K.subtype ⊔ X.pCoreIn p)
    have hh' := (mem_sup_right hcG : (k : G)⁻¹ * r ∈
      (S : Subgroup K).map K.subtype ⊔ X.pCoreIn p)
    simpa only [mul_inv_cancel_left] using mul_mem hh hh'
  · apply sup_le hSR
    obtain ⟨U,hU⟩ := IsPGroup.exists_sylow_sup_of_coprime_index K R hR hRK
      (S : Subgroup K) S.not_dvd_index hSR
    exact (pCoreIn_le_sylow X U).trans_eq hU

end Subgroup
