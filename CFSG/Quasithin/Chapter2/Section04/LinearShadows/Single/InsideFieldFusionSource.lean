module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldInvolutionSource

/-!
# Every inside involution is conjugate to a marked field involution

The actual split extension S=RF gives an involution in F in the same
R-coset as each involution of S outside R. The proved field coset-fusion
theorem then supplies an R-conjugator, with the original ambient embedding.

Source: Aschbacher–Smith, Lemma 2.4.12(2), used in 2.4.21 on printed p.536.
-/

public section
open Subgroup
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_inside_involution_conj_field
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (a : G)
    (haS : a ∈ (d.S : Subgroup d.H).map d.H.subtype) (ha2 : orderOf a = 2)
    (haR : a ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    ∃ s ∈ ((d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G) : Subgroup G),
      orderOf s = 2 ∧ ∃ r ∈ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype),
        r*s*r⁻¹=a := by
  let S := (d.S : Subgroup d.H).map d.H.subtype
  let R := Stellmacher.elementaryAbelianMaxJ S
  let F := S ⊓ normalizer (c.hall : Set G)
  let N := R.subgroupOf S
  have hRS : R ≤ S := sSup_le fun _ h => h.1
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (show S ≤ normalizer (R : Set G) from fun a ha => source_field_actor_normalizes_thompson d a ha)
  let q := QuotientGroup.mk' N
  obtain ⟨⟨r,f⟩,he⟩ := c.split_sylow.2 (⟨a,haS⟩ : S)
  have heG : ((r:S):G)*((f:S):G)=a := congrArg Subtype.val he
  have hqr : q (r:S)=1 := (QuotientGroup.eq_one_iff _).mpr r.property
  have hqf : q (f:S)=q (⟨a,haS⟩:S) := by
    rw [←he,map_mul,hqr,one_mul]
  have hf2N : (f:S)^2∈N := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ((f:S)^2)=1
    rw [map_pow,hqf,←map_pow]
    have ha : (⟨a,haS⟩:S)^2=1 := by
      apply Subtype.ext
      change a^2=1
      simpa only [ha2] using pow_orderOf_eq_one a
    rw [ha,map_one]
  have hf2 : ((f:S):G)^2=1 := congrArg Subtype.val
    (disjoint_def.mp c.split_sylow.disjoint hf2N ((F.subgroupOf S).pow_mem f.property 2))
  have hf1 : ((f:S):G)≠1 := by
    intro hh
    rw [hh,mul_one] at heG
    exact haR (heG ▸ r.property)
  have hfo : orderOf ((f:S):G)=2 := orderOf_eq_prime hf2 hf1
  refine ⟨((f:S):G),f.property,hfo,?_⟩
  apply source_field_involution_coset_fusion d hG T hST hsingle hL hM hTM hunique c
    ((f:S):G) f.property hfo a (hST.le haS) ha2
  have hcoset : a*((f:S):G)⁻¹=((r:S):G) := by rw [←heG,mul_inv_cancel_right]
  rw [hcoset]
  exact r.property


end CFSG.Quasithin.Chapter2.LinearShadows.Single
