module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Centralizing
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Internal
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Applying B.1.8 to a transvection normal closure

A faithful binary transvection has order two and its cyclic subgroup is a
best offender. Every ambient conjugate is again a transvection. Consequently
the restriction to the normal closure has its whole acting group generated
by best offenders, not just a subgroup of the normal closure. Relative
normality also gives trivial two-core when the ambient two-core is trivial.

`normalClosure_factors_of_universal` establishes every applicability condition
before invoking the universal factor conclusion of B.1.8. That universal
theorem remains an explicit input owned by the Chapter B development. No
factor decomposition specialized to this normal closure is an input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.1.8,
printed p.70, and the solvable case of 13.8.5, printed pp.947–948.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition
variable {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]
  {ρ : Representation (ZMod 2) A E} {t : A}

theorem IsTransvection.square (ht : IsTransvection ρ t) (hρ : Function.Injective ρ) :
    t ^ 2 = 1 := by
  apply hρ
  rw [pow_two, map_mul, map_one]
  ext w
  obtain ⟨f, v, _, _, hfv, he⟩ := ht
  change ρ t (ρ t w) = w
  simp only [he, map_add, map_smul, hfv, smul_zero, add_zero]
  rw [add_assoc, ← add_smul]
  have hz : f w + f w = 0 := by
    rw [← two_mul, show (2 : ZMod 2) = 0 from rfl, zero_mul]
  rw [hz, zero_smul, add_zero]

theorem IsTransvection.fixedCodim_le_one [FiniteDimensional (ZMod 2) E]
    (ht : IsTransvection ρ t) : fixedCodim ρ (zpowers t) ≤ 1 := by
  obtain ⟨f, v, _, hv, _, he⟩ := ht
  have hk : fixedSpace ρ (zpowers t) = f.ker := by
    ext w
    rw [mem_fixedSpace_zpowers_iff, LinearMap.mem_ker, he]
    constructor
    · intro h
      exact (smul_eq_zero.mp (add_left_cancel (h.trans (add_zero w).symm))).resolve_right hv
    · intro h
      rw [h, zero_smul, add_zero]
  unfold fixedCodim
  rw [hk, f.quotKerEquivRange.finrank_eq]
  simpa only [Module.finrank_self] using (Submodule.finrank_le f.range)

theorem IsTransvection.bestOffender [Finite A] [FiniteDimensional (ZMod 2) E]
    (ht : IsTransvection ρ t) (hρ : Function.Injective ρ) :
    IsBestOffender ρ (zpowers t) := by
  have hs := ht.square hρ
  have hc : Nat.card (zpowers t) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hs ht.ne_one
  have hr : rank (zpowers t) = 1 := by norm_num [rank, hc]
  have hff : fixedCodim ρ (zpowers t) ≤ rank (zpowers t) := by
    rw [hr]
    exact ht.fixedCodim_le_one
  refine ⟨⟨?_, IsElementaryAbelian.zpowers_of_pow_eq_one hs⟩, ?_⟩
  · intro hb
    have : t = 1 := by simpa [hb] using (mem_zpowers t)
    exact ht.ne_one this
  · intro B hB
    have hd : Nat.card B ∣ 2 := hc ▸ card_dvd_of_le hB
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hb | hb
    · have he : B = ⊥ := card_eq_one.mp hb
      rw [he, weight_bot]
      exact (fixedCodim_le_rank_iff ρ _).mp hff
    · have he : B = zpowers t := eq_of_le_of_card_ge hB (by omega)
      rw [he]

theorem IsTransvection.conjugate (ht : IsTransvection ρ t) (a : A) :
    IsTransvection ρ (a * t * a⁻¹) := by
  obtain ⟨f, v, hf, hv, hfv, he⟩ := ht
  let g := f.comp (ρ a⁻¹)
  have hi (x : E) : ρ a⁻¹ (ρ a x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hj (x : E) : ρ a (ρ a⁻¹ x) = x := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  refine ⟨g, ρ a v, ?_, ?_, ?_, ?_⟩
  · intro hz
    apply hf
    ext x
    have h := LinearMap.congr_fun hz (ρ a x)
    simpa [g, hi] using h
  · intro hz
    exact hv ((hi v).symm.trans (by rw [hz, map_zero]))
  · simpa [g, hi] using hfv
  · intro w
    simp only [map_mul, Module.End.mul_apply, he, map_add, map_smul, hj]
    rfl

theorem normalClosure_offenderSubgroup_eq_top [Finite A] [FiniteDimensional (ZMod 2) E]
    (ht : IsTransvection ρ t) (hρ : Function.Injective ρ) :
    offenderSubgroup (ρ.comp (normalClosure ({t} : Set A)).subtype) = ⊤ := by
  let K := normalClosure ({t} : Set A)
  let J := offenderSubgroup (ρ.comp K.subtype)
  have hKJ : K ≤ J.map K.subtype := by
    apply (Subgroup.closure_le (J.map K.subtype)).mpr
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    have hyt : y = t := Set.mem_singleton_iff.mp hy
    subst y
    obtain ⟨a, rfl⟩ := isConj_iff.mp hxy
    have hbest := (ht.conjugate a).bestOffender hρ
    have hle : zpowers (a * t * a⁻¹) ≤ K := by
      apply zpowers_le.mpr
      exact conjugatesOfSet_subset_normalClosure hx
    have hb := hbest.subgroupOf ρ hle
    have hm : (zpowers (a * t * a⁻¹)).subgroupOf K ≤ J :=
      le_iSup_of_le _ (le_iSup_of_le ⟨hb, le_top⟩ le_rfl)
    have hxK : a * t * a⁻¹ ∈ K := hle (mem_zpowers _)
    exact ⟨⟨_, hxK⟩, hm (mem_zpowers _), rfl⟩
  apply top_unique
  intro k _
  obtain ⟨j, hj, he⟩ := hKJ k.property
  have he' : j = k := Subtype.ext he
  exact he' ▸ hj

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition
open ChapterB
universe u v
variable {A : Type u} {E : Type v} [Group A] [Finite A]
  [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
  {ρ : Representation (ZMod 2) A E} {t : A}

theorem normalClosure_twoCore_eq_bot (hcore : pCore 2 A = ⊥) (t : A) :
    pCore 2 (normalClosure ({t} : Set A)) = ⊥ := by
  rw [pCore_subnormal_eq_comap 2 (inferInstance : (normalClosure ({t} : Set A)).Normal).isSubnormal,
    hcore]
  apply le_bot_iff.mp
  intro x hx
  exact Subtype.ext hx

/-- The universal B.1.8 factor theorem, applied only after proving all its hypotheses. -/
theorem normalClosure_factors_of_universal
    (hB18 : ∀ (B : Type u) [Group B] [Finite B] [Group.IsSolvable B]
      (σ : Representation (ZMod 2) B E),
      pCore 2 B = ⊥ → Function.Injective σ → IsFFModule σ → Nonempty (SolvableFFFactors σ))
    (hρ : Function.Injective ρ) (hcore : pCore 2 A = ⊥) (ht : IsTransvection ρ t)
    (hsolv : Group.IsSolvable (normalClosure ({t} : Set A))) :
    Nonempty (SolvableFFFactors (ρ.comp (normalClosure ({t} : Set A)).subtype)) := by
  let K := normalClosure ({t} : Set A)
  let := hsolv
  have hfaithful : Function.Injective (ρ.comp K.subtype) := hρ.comp Subtype.val_injective
  have htK : IsTransvection (ρ.comp K.subtype)
      (⟨t, subset_normalClosure (Set.mem_singleton t)⟩ : K) := ht
  exact hB18 K (ρ.comp K.subtype) (normalClosure_twoCore_eq_bot hcore t) hfaithful
    ⟨_, (htK.bestOffender hfaithful).isOffender _⟩

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition

end
