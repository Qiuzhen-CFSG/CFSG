module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldInvolutionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.InvolutionSource
/-!
# Fusion of all involutions in S minus R

The cyclic section S/R has a unique involution. Every involution outside
R thus lies in the marked field-involution coset, where the proved core
orbit supplies its literal conjugator. This removes a separate same-coset
hypothesis in the centralizer-order comparison and odd-field transfer.
Source: Aschbacher–Smith 2.4.12(2) and 2.4.23(4), printed pp.532 and537.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_field_involution_sylow_fusion
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n)
    (s : G) (hs : s ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall:Set G))
    (hs2 : orderOf s=2)
    (hsR : s ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype))
    (t : G) (ht : t ∈ (d.S : Subgroup d.H).map d.H.subtype) (ht2 : orderOf t=2)
    (htR : t ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    ∃ r ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype),
      r*s*r⁻¹=t := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  have hRS : R≤S := sSup_le fun _ h=>h.1
  let : (R.subgroupOf S).Normal := (normal_subgroupOf_iff_le_normalizer hRS).mpr
    (S.le_normalizer.trans (Stellmacher.normalizer_le_normalizer_elementaryAbelianMaxJ S))
  let : IsCyclic (S ⧸ R.subgroupOf S) := c.sylow_quotient_cyclic
  let q := QuotientGroup.mk' (R.subgroupOf S)
  have hord (u:S) (hu : orderOf (u:G)=2) (hne : (u:G)∉R) : orderOf (q u)=2 := by
    apply orderOf_eq_prime
    · rw [←map_pow]
      have hp : u^2=1 := Subtype.ext (by simpa only [Subgroup.coe_pow,Subgroup.coe_one,hu] using pow_orderOf_eq_one (u:G))
      rw [hp,map_one]
    · exact fun he=>hne ((QuotientGroup.eq_one_iff (N:=R.subgroupOf S) u).mp he)
  have he : q ⟨t,ht⟩ = q ⟨s,hs.1⟩ :=
    IsCyclic.eq_of_orderOf_eq_two (hord ⟨t,ht⟩ ht2 htR) (hord ⟨s,hs.1⟩ hs2 hsR)
  have hcos : t*s⁻¹∈R := by
    have hh : (⟨t,ht⟩:S)*(⟨s,hs.1⟩:S)⁻¹ ∈ R.subgroupOf S :=
      (QuotientGroup.eq_one_iff _).mp (by change q (_*_)=1;rw [map_mul,map_inv,he,mul_inv_cancel])
    exact hh
  exact source_field_involution_coset_fusion d hG T hST hsingle hL hM hTM hu c s hs hs2
    t (hST.le ht) ht2 hcos
end CFSG.Quasithin.Chapter2.LinearShadows.Single
