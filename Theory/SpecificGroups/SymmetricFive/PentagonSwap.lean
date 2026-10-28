module
public import Theory.SpecificGroups.SymmetricFive.EvenInvolutions
public import Theory.SpecificGroups.SymmetricFive.StarCenterGeometry
public import Mathlib.Tactic
public import Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups

/-!
# Commuting involutions exchange the two inverted pentagons

An even involution in S₅ inverts exactly two Sylow five-subgroups. A distinct
commuting involution fixes neither. Conjugate the first to (01)(23), then check
the possible images of one five-cycle in the five-letter permutation carrier.
The established two-element count upgrades nonfixing to the exact exchange.
No parity condition on the second involution is needed.

The certificate was measured on a representative full check at 23 seconds and
1.99 GiB, using default limits. It enumerates individual permutations and five
powers, not subgroups or a generated multiplication table.

Source application: Aschbacher–Smith J.4.7, printed p.444, in the literal
S₅ quotient of the original involution centralizer.
-/

public section
noncomputable section
namespace Theory.SpecificGroups.SymmetricFive.PentagonSwap
open Subgroup
open scoped Pointwise
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev D:=Equiv.Perm (Fin 5)
private def z:D:=Equiv.swap 0 1 * Equiv.swap 2 3
private theorem standard_non_normalization : ∀ w:D,
    w^2=1 → w≠1 → w≠z → z*w=w*z →
    ∀x:D,x^5=1 → x≠1 → z*x*z⁻¹=x⁻¹ →
    ∀k:Fin 5,w*x*w⁻¹≠x^k.val := by
  decide +kernel

private theorem nonpower (a b x:D) (ha:a^2=1) (ha1:a≠1) (hae:a.sign=1)
    (hb:b^2=1) (hb1:b≠1) (hba:b≠a) (hc:a*b=b*a)
    (hx:x^5=1) (hx1:x≠1) (hi:a*x*a⁻¹=x⁻¹) (k:Fin 5) :
    b*x*b⁻¹≠x^k.val := by
  have hz:z∈alternatingGroup (Fin 5) ∧ z^2=1 ∧ z≠1 := by
    refine ⟨Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel),?_,?_⟩ <;> decide +kernel
  obtain ⟨g,hg⟩:=isConj_iff.mp (Equiv.Perm.even_involutions_five_isConj a z
    ⟨Equiv.Perm.mem_alternatingGroup.mpr hae,ha,ha1⟩ hz)
  let f:=MulAut.conj g
  have hfa:f a=z := hg
  have hfb:(f b)^2=1 := by rw [←map_pow,hb,map_one]
  have hfb1:f b≠1 := fun h => hb1 (f.injective (h.trans f.map_one.symm))
  have hfba:f b≠z := fun h => hba (f.injective (h.trans hfa.symm))
  have hfc:z*f b=f b*z := by
    have h:=congrArg f hc
    simpa only [map_mul,hfa] using h
  have hfx:(f x)^5=1 := by rw [←map_pow,hx,map_one]
  have hfx1:f x≠1 := fun h => hx1 (f.injective (h.trans f.map_one.symm))
  have hfi:z*f x*z⁻¹=(f x)⁻¹ := by
    have h:=congrArg f hi
    simpa only [map_mul,map_inv,hfa] using h
  intro heq
  have h:=congrArg f heq
  apply standard_non_normalization (f b) hfb hfb1 hfba hfc (f x) hfx hfx1 hfi k
  simpa only [map_mul,map_inv,map_pow] using h

/-- A distinct commuting involution moves every five-subgroup inverted by the first. -/
theorem not_normalizes_inverted (a b:Equiv.Perm (Fin 5))
    (ha:orderOf a=2) (hae:a∈alternatingGroup (Fin 5))
    (hb:orderOf b=2) (hne:b≠a) (hc:Commute a b)
    (P:Subgroup (Equiv.Perm (Fin 5))) (hP:Nat.card P=5)
    (hi:∀x∈P,a*x*a⁻¹=x⁻¹) : b∉normalizer (P:Set _) := by
  classical
  obtain ⟨x,hx⟩:=exists_prime_orderOf_dvd_card' (G:=P) 5 (by rw [hP])
  have hxo:orderOf (x:D)=5 := (orderOf_coe x).trans hx
  have hxp:zpowers (x:D)=P := eq_of_le_of_card_ge (zpowers_le.mpr x.property)
    (by rw [Nat.card_zpowers,hxo,hP])
  intro hn
  have hm:b*(x:D)*b⁻¹∈P := (mem_normalizer_iff.mp hn x).mp x.property
  have hm' := hxp.ge hm
  rw [mem_zpowers_iff_mem_range_orderOf] at hm'
  obtain ⟨k,hk,hkeq⟩:=Finset.mem_image.mp hm'
  have hk5:k<5 := by simpa only [Finset.mem_range,hxo] using hk
  have ha':=orderOf_eq_prime_iff.mp ha
  have hb':=orderOf_eq_prime_iff.mp hb
  exact nonpower a b x ha'.1 ha'.2 (Equiv.Perm.mem_alternatingGroup.mp hae)
    hb'.1 hb'.2 hne hc.eq
    (by simpa only [hxo] using pow_orderOf_eq_one (x:D))
    (by intro h;simp [h] at hxo) (hi x x.property) ⟨k,hk5⟩ hkeq.symm


/-- The actual conjugation action on Sylow fives has no fixed point on the inverted pair. -/
theorem moves_inverted_sylow (a b:Equiv.Perm (Fin 5))
    (ha:orderOf a=2) (hae:a∈alternatingGroup (Fin 5))
    (hb:orderOf b=2) (hne:b≠a) (hc:Commute a b)
    (P:Sylow 5 (Equiv.Perm (Fin 5)))
    (hi:∀x∈(P:Subgroup _),a*x*a⁻¹=x⁻¹) : b • P≠P := by
  intro h
  exact not_normalizes_inverted a b ha hae hb hne hc P
    (FiveNormalizerOvergroups.card_sylow P) hi (Sylow.smul_eq_iff_mem_normalizer.mp h)

/-- Conjugation preserves the family inverted by an actor it centralizes. -/
theorem inverts_conjugate (a b:Equiv.Perm (Fin 5)) (hc:Commute a b)
    (P:Sylow 5 (Equiv.Perm (Fin 5)))
    (hi:∀x∈(P:Subgroup _),a*x*a⁻¹=x⁻¹) :
    ∀x∈((b • P:Sylow 5 _):Subgroup _),a*x*a⁻¹=x⁻¹ := by
  have hab:b*a*b⁻¹=a := by rw [hc.symm.eq];group
  rw [Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def]
  rintro x ⟨y,hy,rfl⟩
  change a*(b*y*b⁻¹)*a⁻¹=(b*y*b⁻¹)⁻¹
  have h:=congrArg (MulAut.conj b) (hi y hy)
  simpa only [map_mul,map_inv,MulAut.conj_apply,hab] using h

/-- The second involution exchanges the exact two inverted pentagons. -/
theorem swaps_inverted_pair (a b:Equiv.Perm (Fin 5))
    (ha:orderOf a=2) (hae:a∈alternatingGroup (Fin 5))
    (hb:orderOf b=2) (hne:b≠a) (hc:Commute a b)
    (P Q:Sylow 5 (Equiv.Perm (Fin 5))) (hPQ:P≠Q)
    (hP:∀x∈(P:Subgroup _),a*x*a⁻¹=x⁻¹)
    (hQ:∀x∈(Q:Subgroup _),a*x*a⁻¹=x⁻¹) : b • P=Q ∧ b • Q=P := by
  classical
  let W:Type:={R:Sylow 5 (Equiv.Perm (Fin 5)) // ∀x∈(R:Subgroup _),a*x*a⁻¹=x⁻¹}
  have hcard:Nat.card W=2 := StarCenterGeometry.inverted_sylow_count a ha hae
  have he:∀R S:Sylow 5 (Equiv.Perm (Fin 5)), R≠S →
      (∀x∈(R:Subgroup _),a*x*a⁻¹=x⁻¹) →
      (∀x∈(S:Subgroup _),a*x*a⁻¹=x⁻¹) → b•R=S := by
    intro R S hRS hR hS
    have hmove:=moves_inverted_sylow a b ha hae hb hne hc R hR
    let r:W:=⟨R,hR⟩
    let s:W:=⟨S,hS⟩
    let t:W:=⟨b•R,inverts_conjugate a b hc R hR⟩
    have hs:s≠r := fun h=>hRS (congrArg Subtype.val h).symm
    have ht:t≠r := fun h=>hmove (congrArg Subtype.val h)
    obtain ⟨w,hw,huniq⟩:=(Nat.card_eq_two_iff' r).mp hcard
    exact congrArg Subtype.val ((huniq t ht).trans (huniq s hs).symm)
  exact ⟨he P Q hPQ hP hQ,he Q P hPQ.symm hQ hP⟩

end Theory.SpecificGroups.SymmetricFive.PentagonSwap
