module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperAction
public import Theory.GroupAction.SevenFixedVectorInSixteen
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperCore
public import CFSG.Quasithin.Chapter13.Section07.Preliminaries
public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.PGroup
public import Theory.Representation.BinaryAlternatingSevenCohomology
public import Theory.Representation.FirstCohomologyAutomorphism
public import Theory.Representation.SL2FourNaturalOrbits.BorelFactors

/-!
# The two centralizer consequences of an A₇ upper quotient

An order-seven actor in the upper component fixes a nonzero vector of
the original V, by fixed-point congruence on its16/32-element core.
Original L-transitivity conjugates this actor into Gz, so7 divides|Gz|.

If the upper core equals V, its faithful quotient acts irreducibly in
four binary dimensions. The proved H¹(A₇,V)=0 makes every original
Q-element act on I by conjugation by a vector of V. Its difference
from that inner actor lies in C_T(L)=1, proving Q=V. All conjugations
and both intrinsic-to-ambient inclusions are retained in the proof.

These conclusions feed the original source centralizer calculation in
13.5.15(6), yielding the A₇ contradiction for the specialized13.3.2
maximality argument. Source: Aschbacher–Smith I.1.6(8),13.3.2,13.5.15,
pp.408,884–885,920–921.
-/


public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperAction
open Section08.SourceCompletion Chapter13.Section05.NormalBranch
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

theorem seven_dvd_point_centralizer {I : Subgroup G}
    (hI : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T I)
    (hLI : D.L ≤ I) (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) :
    7 ∣ Nat.card D.Gz := by
  classical
  let W := I.pCoreIn 2
  let : IsElementaryAbelian 2 (D.LT.pCoreIn 2) :=
    (UpperCore.original_core_elementary_bound d h e hseed hn hU).1
  let : IsElementaryAbelian 2 W :=
    IsElementaryAbelian.of_le (UpperCore.upper_core_le_original d hI.maximal_faithful.1.1 hLI)
  have hW : Nat.card W = 16 ∨ Nat.card W = 32 := by
    have hc : Nat.card W = Nat.card (pCore 2 I) := card_map_of_injective I.subtype_injective
    rw [hc]
    exact UpperCore.upper_core_card d h e hseed hn hU hI hLI
  have hseven : 7 ∣ Nat.card I := by
    have hq : Nat.card (I ⧸ pCore 2 I) = 2520 := by
      rw [Nat.card_congr eI.toEquiv,nat_card_alternatingGroup]
      norm_num
    exact (show 7 ∣ Nat.card (I ⧸ pCore 2 I) by rw [hq]; decide).trans
      (card_dvd_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _))
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := I) 7 hseven
  let A := zpowers (a : G)
  have hA : Nat.card A = 7 := by
    rw [Nat.card_zpowers]
    exact (orderOf_injective I.subtype I.subtype_injective a).trans ha
  have hAI : A ≤ I := zpowers_le.mpr a.property
  have hAW : A ≤ normalizer (W : Set G) :=
    (hAI.trans I.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  obtain ⟨v,hv,hv1,hva⟩ := seven_fixed_vector_in_sixteen D.V W A
    (module_le_upper_core d h e hseed hn hU hI hLI) (ReturningPlane.module_card d) hW hA hAW
  obtain ⟨z,hz,hunique⟩ := (Nat.card_eq_two_iff' (1 : D.V₁)).mp h.point_card
  have hz1 : (z : G) ≠ 1 := fun he => hz (Subtype.ext he)
  obtain ⟨l,hl,hlv⟩ := Section07.natural_nonzero_transitive d hv
    (h.point_lt.le.trans h.plus_le z.property) hv1 hz1
  let b := (MulAut.conj l) (a : G)
  have hbz : b * (z : G) = (z : G) * b := by
    have hc := congrArg (MulAut.conj l) (hva (a : G) (mem_zpowers (a : G)))
    simpa only [b,map_mul, MulAut.conj_apply,hlv] using hc
  have hb : b ∈ D.Gz := by
    intro y hy
    by_cases hy1 : y = 1
    · simp [hy1]
    have hyz : (⟨y,hy⟩ : D.V₁) = z := hunique _ (fun he => hy1 (congrArg Subtype.val he))
    have hyz' : y = (z : G) := congrArg Subtype.val hyz
    rw [hyz']
    exact hbz.symm
  have hbo : orderOf (⟨b,hb⟩ : D.Gz) = 7 := by
    rw [← orderOf_injective D.Gz.subtype D.Gz.subtype_injective]
    exact (MulAut.conj l).orderOf_eq (a : G) |>.trans
      ((orderOf_injective I.subtype I.subtype_injective a).trans ha)
  exact hbo ▸ orderOf_dvd_natCard (⟨b,hb⟩ : D.Gz)

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperAction

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperAction
open Section08.SourceCompletion Chapter13.Section05.NormalBranch
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

theorem original_core_eq_module_of_seven_core {I : Subgroup G}
    (hI : Chapter12.Section02.Hypothesis1221 KnownSimple.IsKnownSimple D.T I)
    (hLI : D.L ≤ I) (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7))
    (hcore : I.pCoreIn 2 = D.V) : D.LT.pCoreIn 2 = D.V := by
  let N := pCore 2 I
  let : IsElementaryAbelian 2 N :=
    (UpperCore.upper_core_elementary_bound d h e hseed hn hU hI.maximal_faithful.1.1 hLI).1
  let ρ := coreSevenRepresentation eI
  have hdim : Module.finrank (ZMod 2) (Additive N) = 4 := by
    have hc : Nat.card N = 16 := by
      rw [← card_map_of_injective I.subtype_injective]
      change Nat.card (I.pCoreIn 2) = 16
      rw [hcore,ReturningPlane.module_card d]
    have hd := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive N)
    change Nat.card N = _ at hd
    rw [hc,Nat.card_zmod] at hd
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) hd.symm
  let : Nontrivial (Additive N) := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [hdim]; decide)
  let : ρ.IsIrreducible :=
    Representation.SL2FourNatural.BorelFactors.irreducible_of_transitive ρ (by
      intro v w hv hw
      have hvV : (v.toMul.val : G) ∈ D.V := hcore ▸ mem_map_of_mem I.subtype v.toMul.property
      have hwV : (w.toMul.val : G) ∈ D.V := hcore ▸ mem_map_of_mem I.subtype w.toMul.property
      have hv1 : (v.toMul.val : G) ≠ 1 := fun he =>
        hv (congrArg Additive.ofMul (Subtype.ext (Subtype.ext he)))
      have hw1 : (w.toMul.val : G) ≠ 1 := fun he =>
        hw (congrArg Additive.ofMul (Subtype.ext (Subtype.ext he)))
      obtain ⟨l,hl,he⟩ := Section07.natural_nonzero_transitive d hvV hwV hv1 hw1
      refine ⟨sevenMap eI (inclusion hLI ⟨l,hl⟩),?_⟩
      apply Additive.toMul.injective
      exact Subtype.ext (Subtype.ext ((coreSevenRepresentation_map eI _ v).trans he)))
  let : Subsingleton (Representation.OneCohomology.H1 ρ) :=
    Module.finrank_zero_iff.mp
      (Representation.binaryAlternatingSeven_finrank_H1_eq_zero_of_irreducible_four ρ hdim)
  have hL := ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff D.T D.L).mp
    d.counterexample.local_component).1
  have hTI := Chapter1.Section02.Adequate.local_chain_normalizes
    hL hI.maximal_faithful.1.1 hLI d.normalizes_L
  have hNcentral : centralizer (N : Set I) = N :=
    le_antisymm ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp
      hI.maximal_faithful.2.1.2.2) N.le_centralizer
  let f := sevenMap eI
  have hf : Function.Surjective f := eI.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = N := by
    ext i
    change eI (QuotientGroup.mk' N i) = 1 ↔ i ∈ N
    rw [eI.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff _
  let coordinates : N ≃* Multiplicative (Additive N) := (MulEquiv.multiplicativeAdditive N).symm
  have he (i : I) (v : Additive N) :
      (coordinates.symm (Multiplicative.ofAdd (ρ (f i) v)) : I) =
        i * (coordinates.symm (Multiplicative.ofAdd v) : I) * i⁻¹ := by
    apply Subtype.ext
    exact coreSevenRepresentation_map eI i v
  apply le_antisymm ?_
    (hcore ▸ UpperCore.upper_core_le_original d hI.maximal_faithful.1.1 hLI)
  intro q hq
  have hqT := (h.sylow_centralizer.symm.le hq).1
  have hqc := (h.sylow_centralizer.symm.le hq).2
  let α : MulAut I := I.normalizerMonoidHom ⟨q,hTI hqT⟩
  have hfix (n : I) (hn : n ∈ N) : α n = n := by
    apply Subtype.ext
    change q * (n : G) * q⁻¹ = (n : G)
    exact mul_inv_eq_iff_eq_mul.mpr
      ((hqc (n : G) (hcore ▸ mem_map_of_mem I.subtype hn)).symm)
  have hα (i : I) : f (α i) = f i := by
    have hd : (α i)⁻¹ * i ∈ centralizer (N : Set I) := by
      intro n hn
      have hh := hfix (i*n*i⁻¹) ((inferInstance : N.Normal).conj_mem n hn i)
      rw [map_mul,map_mul,map_inv,hfix n hn] at hh
      calc
        n * ((α i)⁻¹*i) = (α i)⁻¹*(α i*n*(α i)⁻¹)*i := by group
        _ = (α i)⁻¹*(i*n*i⁻¹)*i := by rw [hh]
        _ = ((α i)⁻¹*i)*n := by group
    have hd' : f ((α i)⁻¹*i) = 1 := by
      change (α i)⁻¹*i ∈ f.ker
      rw [hk,← hNcentral]
      exact hd
    rw [map_mul,map_inv,inv_mul_eq_one] at hd'
    exact hd'
  obtain ⟨n,hinner⟩ := Representation.OneCohomology.automorphism_inner_of_H1_zero
    N f hf hk coordinates ρ he α hα hfix
  have hnV : (n.val : G) ∈ D.V := hcore ▸ mem_map_of_mem I.subtype n.property
  have hnT : (n.val : G) ∈ (D.T : Subgroup G) := h.V_le_T hnV
  have hc : (n.val : G) * q ∈ (D.T : Subgroup G) ⊓ centralizer (D.L : Set G) := by
    refine ⟨(D.T : Subgroup G).mul_mem hnT hqT,?_⟩
    intro l hl
    have hh := congrArg (fun i : I => (i : G)) (hinner ⟨l,hLI hl⟩)
    change q*l*q⁻¹ = (n.val : G)⁻¹*l*(n.val : G) at hh
    calc
      l*((n.val : G)*q) = (n.val : G)*((n.val : G)⁻¹*l*(n.val : G))*q := by group
      _ = (n.val : G)*(q*l*q⁻¹)*q := by rw [← hh]
      _ = ((n.val : G)*q)*l := by group
  have hz := mem_bot.mp ((SourcePairCentralizer.sylow_local_centralizer_eq_bot_of_generated_core
    d h e hseed hn hU).le hc)
  rw [eq_inv_of_mul_eq_one_right hz]
  exact D.V.inv_mem hnV

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.UpperAction