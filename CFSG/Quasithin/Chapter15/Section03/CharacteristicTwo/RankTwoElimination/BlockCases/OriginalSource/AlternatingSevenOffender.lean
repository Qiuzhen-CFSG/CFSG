module
public import CFSG.Quasithin.ChapterC.Section02.SourceExtraction.C27.OriginalRestriction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Support
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Transport
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSevenFixed
public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddParity
public import Theory.Representation.BinaryOffender.Embedding
public import Theory.SpecificGroups.Alternating.SevenComponent.Extension

/-!
# The actual ordinary A₇ radical contains an outer element

The short-block support theorem identifies [W,L] with U(L), so the source
omega-center W contains the actual natural module. C.2.7(2) supplies a best
offender inside R*. If R* were contained in L*, this offender would restrict
faithfully to the six-dimensional natural A₇ module. Odd-degree permutation
offenders contain odd permutations, giving a contradiction.

The proof preserves the original core quotient, star quotient and conjugation
action. It uses C.2.7(1–2), without any of its marked model alternatives.
Source: Aschbacher–Smith B.3.2, C.2.7 and15.3.21, pp.83,145–147,1127.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open ChapterC Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Representation Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {H K R M : Subgroup G}

theorem source_blockU_le_starV (h : Input κ H R M K) (hs : IsShort K) :
    (blockU K).map (inclusion (show K ≤ K ⊔ R from le_sup_left)) ≤ starV K R := by
  let J := K ⊔ R
  let K₀ := K.subgroupOf J
  let e : K₀ ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let : K₀.Normal := normal_subgroupOf_of_le_normalizer (sup_le le_normalizer h.normalizes)
  have hk := (C27Source.kernel_offender_from_source h).1
  have hne := starImage_ne_bot_of_bound h.normalizes h.quasisimple hk.upper
  have hm : ⁅starV K R,K₀⁆ ≠ ⊥ := by
    intro he
    have hfix : K₀ ≤ starKernel K R := by
      rw [commutator_comm] at he
      exact commutator_eq_bot_iff_le_centralizer.mp he
    apply hne
    apply bot_unique
    rintro _ ⟨x,hx,rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr (hfix hx)
  have hb : IsBlock K₀ := ⟨inferInstance,hs.of_mulEquiv e.symm,(inferInstance : K₀.Normal).isSubnormal⟩
  have hu := RankOne.ChiProduct.SelectedRankOne.blockU_eq_nontrivial_normal_module_commutator
    K₀ (starV K R) hb hm
  have hmap : (blockU K₀).map e.toMonoidHom = blockU K := by
    rw [blockU,map_commutator,pCore_map_iso,map_top_of_surjective _ e.surjective]
    rfl
  have he : (blockU K).map (inclusion (show K ≤ J from le_sup_left)) =
      (blockU K₀).map K₀.subtype := by
    rw [←hmap,map_map]
    rfl
  rw [he,hu]
  exact commutator_le_left _ _

private theorem natural_offender_not_le_alternating
    {A : Subgroup (Equiv.Perm (Fin 7))}
    (hA : IsOffender (BinaryPermutation.naturalRepresentation (Fin 7)) A) :
    ¬ A ≤ alternatingGroup (Fin 7) := by
  apply ChapterB.Offenders.core_offender_not_le_alternating (Or.inr rfl)
  refine ⟨hA.1,?_⟩
  rw [BinaryPermutation.fixedCodim_core_eq_full_odd _ (by decide),
    ←BinaryPermutation.fixedCodim_natural_eq_full_odd _ (by decide)]
  exact hA.2

/-- The source radical cannot have its entire star image inside its A7 component:
its actual offender would restrict to an impossible even natural-module offender. -/
theorem alternatingSeven_radical_not_le_component
    (h : Input κ H R M K) (hb : IsAlternatingBlock K 7) :
    ¬ starImage K R R ≤ starImage K R K := by
  intro hRK
  obtain ⟨hk,ho⟩ := C27Source.kernel_offender_from_source h
  obtain ⟨A,hAR,hA⟩ := ho.best
  obtain ⟨r,⟨m⟩,hr⟩ := hb.2.2
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply bot_unique
    intro x hx
    have he : m.quotientIso x ∈ center (alternatingGroup (Fin 7)) :=
      (centerCongr m.quotientIso ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
    exact m.quotientIso.map_eq_one_iff.mp he
  have hne := starImage_ne_bot_of_bound h.normalizes h.quasisimple hk.upper
  let a := coreStarEquivOfCenterEqBot h.normalizes h.quasisimple hne hz
  let eK : starImage K R K ≃* alternatingGroup (Fin 7) := a.symm.trans m.quotientIso
  let f : starImage K R K →* Equiv.Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp eK.toMonoidHom
  let := hb.2.1.elementary
  let := hb.2.1.module_elementary
  let qU := QuotientGroup.mk' (blockFixed K)
  have hqU : Function.Injective qU := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [QuotientGroup.ker_mk',hb.seven_fixed_eq_bot]
  let b : blockU K ≃* BlockModule K := MulEquiv.ofBijective qU ⟨hqU,QuotientGroup.mk'_surjective _⟩
  let eU : Additive (blockU K) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 7) :=
    { (b.trans m.moduleIso).toAdditiveLeft with
      map_smul' := fun c v => ZMod.map_smul (b.trans m.moduleIso).toAdditiveLeft c v }
  let j : blockU K →* starV K R :=
    ((inclusion (show K ≤ K ⊔ R from le_sup_left)).comp (blockU K).subtype).codRestrict _
      (fun u => source_blockU_le_starV h hb.2.1 (mem_map_of_mem _ u.property))
  have hj : Function.Injective j := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : starV K R => (w : (K ⊔ R : Subgroup G)).val) huv
  let jlin : Additive (blockU K) →ₗ[ZMod 2] Additive (starV K R) := j.toAdditive.toZModLinearMap 2
  let e : BinaryPermutation.natural (Fin 7) →ₗ[ZMod 2] Additive (starV K R) := jlin.comp eU.symm.toLinearMap
  have hei : Function.Injective e := hj.comp eU.symm.injective
  let ρ := (starRepresentation K R).comp (starImage K R K).subtype
  have he (g : starImage K R K) (v : BinaryPermutation.natural (Fin 7)) :
      ρ g (e v) = e (BinaryPermutation.naturalRepresentation (Fin 7) (f g) v) := by
    obtain ⟨k,rfl⟩ := toStarImage_surjective K R g
    obtain ⟨u,rfl⟩ := eU.surjective v
    have hcoord : eU (Additive.ofMul (blockConjugate K k u.toMul)) =
        BinaryPermutation.naturalRepresentation (Fin 7) (f (toStarImage K R k)) (eU u) := by
      change Multiplicative.toAdd (m.moduleIso (qU (blockConjugate K k u.toMul))) = _
      rw [m.intertwining,hr]
      have heK : eK (toStarImage K R k) = m.quotientIso (QuotientGroup.mk' (pCore 2 K) k) := by
        change m.quotientIso (a.symm (a (QuotientGroup.mk' (pCore 2 K) k))) = _
        rw [a.symm_apply_apply]
      change _ = BinaryPermutation.naturalRepresentation (Fin 7) (eK (toStarImage K R k)).val (eU u)
      rw [heK]
      rfl
    rw [←hcoord]
    change ρ (toStarImage K R k) (jlin (eU.symm (eU u))) =
      jlin (eU.symm (eU (Additive.ofMul (blockConjugate K k u.toMul))))
    rw [eU.symm_apply_apply,eU.symm_apply_apply]
    apply congrArg Additive.ofMul
    apply Subtype.ext
    change ((starRepresentation K R (QuotientGroup.mk' (starKernel K R)
      (inclusion (show K ≤ K ⊔ R from le_sup_left) k)) (jlin u)).toMul :
        (K ⊔ R : Subgroup G)) = _
    rw [starRepresentation_apply]
    rfl
  have hAK : A ≤ starImage K R K := hAR.trans hRK
  have hoff := (hA.subgroupOf (starRepresentation K R) hAK).isOffender ρ
  have hmapped := hoff.map_of_embedding ρ (BinaryPermutation.naturalRepresentation (Fin 7))
    f e hei he (Subtype.val_injective.comp eK.injective)
  exact natural_offender_not_le_alternating hmapped (by
    rintro _ ⟨x,hx,rfl⟩
    exact (eK x).property)
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
