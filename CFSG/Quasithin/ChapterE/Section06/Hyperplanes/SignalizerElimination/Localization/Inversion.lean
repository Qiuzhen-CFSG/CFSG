module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination.Contracts
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Basic
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Inverting the completed local odd closure

A nonidentity element z of C_V(T) exists because V is nontrivial and normal
in T. The characteristic-two conclusions 1.1.3(2) and 1.1.4(6) kill the odd
core of every subspace centralizer containing z. Completeness then makes z
fixed-point-free on X. Its involutory conjugation inverts X and proves that
X is abelian. If z lies in U₀, each generating odd core is already trivial.

`EarlierLocalFacts` retains the exact earlier source inputs; completion is
also explicit. No abelianness or inversion property is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.20,
printed p.253 (PDF p.264); 1.1.3(2), 1.1.4(6), printed p.500.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U₀ : Subgroup G}

omit [Finite G] in
/-- The actual closure is invariant under V, since each of its generators is. -/
theorem le_normalizer_localOddClosure [IsElementaryAbelian 2 V] :
    V ≤ normalizer (localOddClosure V U₀ : Set G) := by
  apply le_trans (le_iInf fun A => ?_) (iInf_normalizer_le_normalizer_iSup _)
  exact (V.le_centralizer.trans (Subgroup.centralizer_le A.property.2)).trans
    (centralizer_le_normalizer_oddCentralizer A.val)

/-- A subspace containing a nonidentity Sylow-fixed point has trivial odd core.
This uses precisely the centralizer clause of 1.1.3(2) and 1.1.4(6). -/
theorem oddCentralizer_eq_bot_of_sylow_fixed
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    {z : G} (hz : z ∈ sylowFixedSpace (T : Subgroup G) V) (hne : z ≠ 1)
    {A : Subgroup G} (hAV : A ≤ V) (hzA : z ∈ A) : oddCentralizer A = ⊥ := by
  let _ := h.elementary
  have hAC : A ≤ centralizer ({z} : Set G) := by
    intro a ha
    exact mem_centralizer_singleton_iff.mpr ((V.le_centralizer hz.1) a (hAV ha))
  have hCC : centralizer (A : Set G) ≤ centralizer ({z} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hx z hzA).symm
  have hc := earlier.centralizers A (centralizer ({z} : Set G))
    (h.centralizer_fixedPoint_characteristicTwo earlier hz hne) hAC
    ((IsElementaryAbelian.isPGroup 2 V).to_le hAV)
  rw [inf_eq_right.mpr hCC] at hc
  exact (oddCentralizer_eq_bot_iff A).mpr
    (pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hc)

/-- Completeness makes every nonidentity Sylow-fixed point fixed-point-free
on the local closure. The case where that point is already in U₀ forces X=1. -/
theorem localOddClosure_inf_sylow_fixed_eq_bot
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hcpl : CompletedLocalOddClosure V) (hUV : U₀ ≤ V)
    (hcor : subgroupCorank V U₀ = 3)
    {z : G} (hz : z ∈ sylowFixedSpace (T : Subgroup G) V) (hne : z ≠ 1) :
    localOddClosure V U₀ ⊓ centralizer ({z} : Set G) = ⊥ := by
  by_cases hzU : z ∈ U₀
  · have hX : localOddClosure V U₀ = ⊥ := by
      apply le_bot_iff.mp
      refine iSup_le fun A => ?_
      rw [oddCentralizer_eq_bot_of_sylow_fixed h earlier hz hne
        A.property.2 (A.property.1.le hzU)]
    rw [hX, bot_inf_eq]
  · let A := U₀ ⊔ zpowers z
    have hzA : z ∈ A := (le_sup_right : zpowers z ≤ A) (mem_zpowers z)
    have hUA : U₀ < A := lt_of_le_of_ne le_sup_left (fun he => hzU (he.symm ▸ hzA))
    have hAV : A ≤ V := sup_le hUV (zpowers_le.mpr hz.1)
    have hzero := (hcpl U₀ hUV hcor).2 A hUA hAV
    rw [oddCentralizer_eq_bot_of_sylow_fixed h earlier hz hne hAV hzA] at hzero
    apply le_bot_iff.mp
    rw [← hzero]
    apply le_inf inf_le_left
    rintro x ⟨hx, hzfix⟩
    have hU : x ∈ centralizer (U₀ : Set G) := localOddClosure_le V U₀ hx
    have hzcomm : x ∈ centralizer (zpowers z : Set G) := by
      rintro a ⟨n, rfl⟩
      exact (show Commute z x from (mem_centralizer_singleton_iff.mp hzfix).symm).zpow_left n |>.eq
    have hA : A ≤ centralizer ({x} : Set G) := by
      apply sup_le
      · intro u hu
        exact mem_centralizer_singleton_iff.mpr (hU u hu)
      · intro a ha
        exact mem_centralizer_singleton_iff.mpr (hzcomm a ha)
    intro a ha
    exact mem_centralizer_singleton_iff.mp (hA ha)

/-- Conjugation by a nonidentity element of C_V(T) inverts the actual X. -/
theorem localOddClosure_inverted
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hcpl : CompletedLocalOddClosure V) (hUV : U₀ ≤ V)
    (hcor : subgroupCorank V U₀ = 3)
    {z : G} (hz : z ∈ sylowFixedSpace (T : Subgroup G) V) (hne : z ≠ 1)
    {x : G} (hx : x ∈ localOddClosure V U₀) : z * x * z⁻¹ = x⁻¹ := by
  let _ := h.elementary
  let X := localOddClosure V U₀
  let zN : normalizer (X : Set G) := ⟨z, le_normalizer_localOddClosure hz.1⟩
  let φ := X.normalizerMonoidHom zN
  have hφ : MonoidHom.FixedPointFree φ := by
    intro a ha
    have he : z * (a : G) * z⁻¹ = (a : G) := congrArg Subtype.val ha
    have hm : (a : G) ∈ X ⊓ centralizer ({z} : Set G) :=
      ⟨a.property, mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he).symm⟩
    rw [localOddClosure_inf_sylow_fixed_eq_bot h earlier hcpl hUV hcor hz hne] at hm
    exact Subtype.ext (mem_bot.mp hm)
  have hzz : zN * zN = 1 := by
    apply Subtype.ext
    change z * z = 1
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) z hz.1
  have hφφ : φ * φ = 1 := by
    change X.normalizerMonoidHom zN * X.normalizerMonoidHom zN = 1
    rw [← map_mul, hzz, map_one]
  have hinv : Function.Involutive φ := fun a => congrArg (fun f : MulAut X => f a) hφφ
  exact congrArg Subtype.val (congrFun (hφ.coe_eq_inv_of_involutive hinv) ⟨x, hx⟩)

/-- A central involution exists by normality in T; its fixed-point-free action
therefore proves abelianness, rather than assuming it as completion data. -/
theorem localOddClosure_isMulCommutative
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hcpl : CompletedLocalOddClosure V) (hUV : U₀ ≤ V)
    (hcor : subgroupCorank V U₀ = 3) : IsMulCommutative (localOddClosure V U₀) := by
  obtain ⟨z, hz, hne⟩ := Components.exists_sylow_fixed h
  have hi : ∀ {x : G}, x ∈ localOddClosure V U₀ → z * x * z⁻¹ = x⁻¹ :=
    fun hx => localOddClosure_inverted h earlier hcpl hUV hcor hz hne hx
  apply IsMulCommutative.of_comm
  intro a b
  apply Subtype.ext
  have he := (MulAut.conj z).map_mul (a : G) (b : G)
  change z * ((a : G) * (b : G)) * z⁻¹ =
    (z * (a : G) * z⁻¹) * (z * (b : G) * z⁻¹) at he
  rw [hi ((localOddClosure V U₀).mul_mem a.property b.property), hi a.property,
    hi b.property, mul_inv_rev] at he
  have hh := congrArg Inv.inv he
  simpa using hh

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SignalizerElimination
