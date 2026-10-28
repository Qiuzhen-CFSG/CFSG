module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterFieldKernelSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterPairSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.DerivedSource
public import Theory.GroupTheory.CentralQuotientAutomorphismFixedDerived

/-!
# Faithful original torus action on the Thompson central quotient

The original absorbed Sylow subgroup has center contained in its derived
group. An actor trivial modulo that center consequently fixes the distinguished
elementary subgroup. Its normalizer and centralizer source identities place
the actor in the Thompson subgroup, whose intersection with the original torus
complement is trivial. Thus the literal complement acts faithfully on the
central quotient, with no automorphism marking assumed.

Source: Aschbacher–Smith 2.4.17–18 and the noncentral case of 2.4.24(2).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_thompson_center_le_derived
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0=d.block) {n:ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀ N, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)
    center R≤commutator R := by
  let R := Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)
  change center R≤commutator R
  have hRL := (source_core_absorption d hG T hST hsingle hL hM hTM hu).1
  have hRP := (source_thompson_decomposition d hG T hST hsingle hL).2.1
  rw [inf_eq_left.mpr hRL] at hRP
  have hc := source_sylow_center_le_derived d hG T hST hsingle hL
  rw [←hRP] at hc
  intro z hz
  have hm : (z:G)∈⁅R,R⁆ := hc ⟨z.property,by
    intro r hr
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨r,hr⟩)⟩
  rw [←map_subtype_commutator] at hm
  exact (mem_map_iff_mem R.subtype_injective).mp hm

theorem source_torus_faithful_thompson_quotient
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0=d.block) {n:ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀ N, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M)
    (c : CyclicTorusSetup d T n) (hZ : center (d.block.map d.H.subtype)≠⊥) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)
    let A := (normalizer (c.hall:Set G)).subgroupOf (T:Subgroup G)
    ∃ α:A→*MulAut R,
      (∀ (a:A) (r:R), (α a r:G)=(a:T)*(r:G)*(a:T)⁻¹) ∧
      Function.Injective ((quotientAut (center R)).comp α) := by
  let S := (d.S:Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let A := (normalizer (c.hall:Set G)).subgroupOf (T:Subgroup G)
  have hK := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hTR := (d.lemma_2_4_8_1 hG T hST hsingle hK).2.2
  let ι : A→*normalizer (R:Set G) :=
    ((T:Subgroup G).subtype.comp A.subtype).codRestrict _ (fun a=>hTR a.val.property)
  let α : A→*MulAut R := R.normalizerMonoidHom.comp ι
  refine ⟨α,(fun _ _=>rfl),?_⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro a ha
  have hα : quotientAut (center R) (α a)=1 := ha
  have hzfix := (source_thompson_center_le_derived d hG T hST hsingle hL hM hTM hu).trans
    ((α a).fixes_commutator_of_quotientCenter_eq_one hα)
  have hb := source_distinguished_elementary d hG T hST hsingle hL hM hTM hu
  have haZ : ((a:T):G)∈centralizer (distinguishedZ d:Set G) := by
    intro z hz
    have hzR : z∈R := (hb.2.2.1 hz).1
    have hzC : (⟨z,hzR⟩:R)∈center R := by
      apply mem_center_iff.mpr
      intro r
      exact Subtype.ext ((hb.2.2.1 hz).2 r r.property)
    have hf := hzfix hzC
    rw [MulAut.mem_fixedSubgroup] at hf
    have hf' := congrArg Subtype.val hf
    change ((a:T):G)*z*((a:T):G)⁻¹=z at hf'
    exact (mul_inv_eq_iff_eq_mul.mp hf').symm
  have haS : ((a:T):G)∈S := by
    change ((a:T):G)∈(d.S:Subgroup d.H).map d.H.subtype
    rw [←source_distinguished_normalizer_in_sylow d hG T hST hsingle hL hM hTM hu hZ]
    exact ⟨a.val.property,Subgroup.centralizer_le_normalizer _ haZ⟩
  have haR : ((a:T):G)∈R := by
    change ((a:T):G)∈Stellmacher.elementaryAbelianMaxJ ((d.S:Subgroup d.H).map d.H.subtype)
    rw [←source_noncenterless_sylow_centralizer_eq d hG T hST hsingle hL hM hTM hu c hZ]
    exact ⟨haS,haZ⟩
  have ha1 : (a:T)=1 := disjoint_def.mp c.split_ambient.disjoint haR a.property
  exact mem_bot.mpr (Subtype.ext ha1)
end CFSG.Quasithin.Chapter2.LinearShadows.Single
