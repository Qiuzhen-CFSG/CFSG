module
public import Theory.Alternating.FivePairPrimeSupport
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductQuotient
public import CFSG.Quasithin.Chapter10.SourceA5FiveResidual
public import CFSG.Quasithin.Chapter4.Section01.Maximality
public import Theory.GroupTheory.NormalizerQuotientOuterPair

/-!
# Faithful odd actors lie in the original A₅ orbit

The literal action on L₀/O₂(L₀) embeds a faithful odd subgroup B into
Aut(A₅ × A₅), so |B| has prime divisors only three and five. The original
cubic and five residual identities say that M/L₀ has neither prime divisor.
The image of B in that quotient is therefore trivial. No replacement of the
ambient subgroup B or of the full two-core is made.

Source: Aschbacher–Smith, 10.1.3 and 10.2.3(2), printed pp.742 and745.
Faithfulness remains the preceding source obligation of the assembly owner.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter4
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02

private theorem section_action_injective {G : Type*} [Group G] (R B : Subgroup G)
    (hB : B ≤ normalizer (R : Set G))
    (hfaith : B ⊓ sectionCentralizer R = ⊥) :
    Function.Injective ((normalizerPCoreQuotientAction R).comp (inclusion hB)) := by
  let f := (normalizerPCoreQuotientAction R).comp (inclusion hB)
  have hk : f.ker.map B.subtype ≤ sectionCentralizer R := by
    apply (le_sectionCentralizer_iff _ _).mpr
    refine ⟨(map_subtype_le _).trans hB,commutator_le.mpr ?_⟩
    rintro _ ⟨b,hb,rfl⟩ r hr
    have hbr := DFunLike.congr_fun (show f b = 1 from hb)
      (QuotientGroup.mk' (pCore 2 R) ⟨r,hr⟩)
    change quotientAut (pCore 2 R) _ _ = _ at hbr
    rw [quotientAut_apply_mk] at hbr
    let r' : R := ⟨r,hr⟩
    let br := R.normalizerMonoidHom (inclusion hB b) r'
    have hh : br * r'⁻¹ ∈ pCore 2 R := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (pCore 2 R) (br * r'⁻¹) = 1
      rw [map_mul,map_inv]
      change QuotientGroup.mk' (pCore 2 R) br = QuotientGroup.mk' (pCore 2 R) r' at hbr
      rw [hbr,mul_inv_cancel]
    exact ⟨br * r'⁻¹,hh,rfl⟩
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro b hb
  apply mem_bot.mpr
  apply Subtype.ext
  have hh : (b : G) ∈ B ⊓ sectionCentralizer R :=
    ⟨b.property,hk (mem_map_of_mem B.subtype hb)⟩
  exact mem_bot.mp (hfaith ▸ hh)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
include D e

/-- The original faithful odd actor is contained in L₀ itself. -/
theorem source_a5_faithful_odd_subgroup_le_orbit
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBM : B ≤ D.maximalLocal) (hodd : Odd (Nat.card B))
    (hfaith : B ⊓ sectionCentralizer (localOrbit T L) = ⊥) :
    B ≤ localOrbit T L := by
  let R := localOrbit T L
  let M := D.maximalLocal
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp hn
  obtain ⟨q,hq,hk,_⟩ := source_a5_original_product_quotient D e hn ht htn
  let eqR : (R ⧸ pCore 2 R) ≃*
      (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  have hAut : IsPGroup 30 (MulAut (R ⧸ pCore 2 R)) :=
    Theory.AlternatingFive.pair_automorphism_isPGroup_thirty.of_equiv (MulAut.congr eqR).symm
  have hB30 : IsPGroup 30 B := hAut.of_injective
    ((normalizerPCoreQuotientAction R).comp (inclusion hBM))
    (section_action_injective R B hBM hfaith)
  obtain ⟨n,hcard⟩ := hB30.exists_card_dvd_pow
  have hcard15 : Nat.card B ∣ 15 ^ n := by
    have hh : Nat.card B ∣ 2 ^ n * 15 ^ n := by
      simpa only [←mul_pow, show 2 * 15 = 30 by decide] using hcard
    exact (hodd.coprime_two_right.pow_right n).dvd_of_dvd_mul_left hh
  let N := R.subgroupOf M
  let BM := B.subgroupOf M
  let : N.Normal := normal_subgroupOf_of_le_normalizer (show M ≤ normalizer (R : Set G) from le_rfl)
  have hc3 : Nat.Coprime 3 N.index := by
    have he : N = primeToResidual 3 M := by
      apply map_injective M.subtype_injective
      rw [map_subgroupOf_eq_of_le R.le_normalizer,
        source_nonnormal_cubic_residual D hn]
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [he]
    exact primeToResidual_index_coprime 3
  have hc5 : Nat.Coprime 5 N.index := source_nonnormal_a5_orbit_index_coprime_five D e hn
  have hc15 : Nat.Coprime 15 N.index := by
    simpa only [show 3 * 5 = 15 by decide] using hc3.mul_left hc5
  have hcBM : Nat.card BM ∣ 15 ^ n := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hBM).toEquiv]
  have hcop : Nat.Coprime N.index (Nat.card BM) :=
    (hc15.pow_left n).symm.coprime_dvd_right hcBM
  have hle : BM ≤ N := relIndex_eq_one.mp
    (Nat.eq_one_of_dvd_coprimes hcop (N.relIndex_dvd_index_of_normal BM)
      (N.relIndex_dvd_card BM))
  intro b hb
  exact hle (show (⟨b,hBM hb⟩ : M) ∈ BM from hb)

end CFSG.Quasithin.Chapter10
