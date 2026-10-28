module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientTitsOriginalImage
public import CFSG.Quasithin.Chapter6.Section01.SourceBasic
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.Representation.BinaryConjugationCoordinates

/-!
# Literal coordinates of the original Tits quotient kernel

The original Hermitian marking identifies the kernel of the map into
KT/O₂(KT) with a binary submodule. Its quotient has exactly the order
of the literal module image, and conjugation by original normalizing
actors preserves this kernel.

Source: Aschbacher--Smith6.1.4, printed pp.665--666.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
attribute [local instance] SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
open OrthogonalFourMinus.FiniteModel Matrix.SpecialLinearGroup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

local instance kernelFixedAlgebra : Algebra (ZMod 2) (fixedField 2) := ZMod.algebra _ 2
local instance kernelBinaryModule : Module (ZMod 2) (Space 2) :=
  Module.compHom (Space 2) (algebraMap (ZMod 2) (fixedField 2))

private def kernelImageSpace {B : Subgroup G}
    (f : B ≃* Multiplicative (Space 2)) (U : Subgroup G) :
    Submodule (ZMod 2) (Space 2) :=
  AddSubgroup.toZModSubmodule 2 ((U.subgroupOf B).map f.toMonoidHom).toAddSubgroup

omit [Finite G] in
private theorem kernelMemImageSpace {B : Subgroup G}
    (f : B ≃* Multiplicative (Space 2)) (U : Subgroup G) (v : B) :
    (f v).toAdd ∈ kernelImageSpace f U ↔ (v : G) ∈ U := by
  change f v ∈ (U.subgroupOf B).map f.toMonoidHom ↔ v ∈ U.subgroupOf B
  exact mem_map_iff_mem f.injective

omit [Finite G] in
private theorem kernelNormalizedImageStabilizer {B : Subgroup G}
    (hLB : L ≤ normalizer (B : Set G))
    (q : L →* Matrix.SpecialLinearGroup (Fin 2) (Field 2))
    (f : B ≃* Multiplicative (Space 2))
    (hf : ∀ (l : L) (v : B),
      (f (B.normalizerMonoidHom ⟨l,hLB l.property⟩ v)).toAdd =
        SL2.BinarySmall.hermitian 2 (q l) (f v).toAdd)
    (W : Subgroup G) (l : L)
    (hl : (l : G) ∈ normalizer (W : Set G)) :
    q l ∈ subspaceStabilizer (SL2.BinarySmall.hermitian 2) (kernelImageSpace f W) := by
  intro x
  obtain ⟨v,rfl⟩ := f.surjective (Multiplicative.ofAdd x)
  change SL2.BinarySmall.hermitian 2 (q l) (f v).toAdd ∈ kernelImageSpace f W ↔
    (f v).toAdd ∈ kernelImageSpace f W
  rw [←hf, kernelMemImageSpace, kernelMemImageSpace]
  exact (mem_normalizer_iff.mp hl v).symm

private theorem kernel_exists_hermitian_sylow_coordinates
    {B : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hm : IsConjugationModel L B (SL2.BinarySmall.hermitian 2)) :
    ∃ (q : L →* Matrix.SpecialLinearGroup (Fin 2) (Field 2))
      (f : B ≃* Multiplicative (Space 2)),
      Function.Surjective q ∧
      (∀ (l : L) (v : B),
        (f (B.normalizerMonoidHom ⟨l,hm.normalizes l.property⟩ v)).toAdd =
          SL2.BinarySmall.hermitian 2 (q l) (f v).toAdd) ∧
      ((T : Subgroup G).subgroupOf L).map q =
        Matrix.SpecialLinearGroup.upperUnipotent (Field 2) := by
  have hN := hm.normalizes
  obtain ⟨e,f,hf⟩ := hm
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  let S := P.mapSurjective hq
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq
    (Matrix.SpecialLinearGroup (Fin 2) (Field 2)) S
      (Matrix.SpecialLinearGroup.upperUnipotentSylow (Field 2) 2)
  have hS : (S : Subgroup _).map (MulAut.conj a).toMonoidHom =
      Matrix.SpecialLinearGroup.upperUnipotent (Field 2) := by
    change ((a • S : Sylow 2 (Matrix.SpecialLinearGroup (Fin 2) (Field 2))) :
      Subgroup (Matrix.SpecialLinearGroup (Fin 2) (Field 2))) = _
    rw [ha]
    rfl
  let ρ := SL2.BinarySmall.hermitian 2
  let A := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom a)
  let f' := f.trans A.toAddEquiv.toMultiplicative
  let q' := (MulAut.conj a).toMonoidHom.comp q
  have hact (l : L) (v : B) :
      (f (B.normalizerMonoidHom ⟨l,hN l.property⟩ v)).toAdd =
        ρ (q l) (f v).toAdd := by
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.ext
    change (f.symm (f (B.normalizerMonoidHom ⟨l,hN l.property⟩ v)) : G) = _
    rw [f.symm_apply_apply]
    exact (hf l v).symm
  refine ⟨q',f',(MulAut.conj a).surjective.comp hq,?_,?_⟩
  · intro l v
    change ρ a (f (B.normalizerMonoidHom ⟨l,hN l.property⟩ v)).toAdd =
      ρ (a * q l * a⁻¹) (ρ a (f v).toAdd)
    rw [hact,map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,
      ρ.inv_self_apply]
  · change ((T : Subgroup G).subgroupOf L).map
      ((MulAut.conj a).toMonoidHom.comp q) = _
    rw [←Subgroup.map_map,←hP]
    exact hS

omit [Finite G] in
private theorem coordinate_quotient_card
    {B J : Subgroup G} (hBJ : B ≤ J)
    (f : B ≃* Multiplicative (Space 2)) :
    Nat.card ((Space 2) ⧸ kernelImageSpace f (J.pCoreIn 2)) =
      Nat.card ((B.subgroupOf J).map (QuotientGroup.mk' (pCore 2 J))) := by
  let q := QuotientGroup.mk' (pCore 2 J)
  change (((J.pCoreIn 2).subgroupOf B).map f.toMonoidHom).toAddSubgroup.index = _
  rw [index_toAddSubgroup]
  rw [index_map_of_bijective f.bijective]
  change (J.pCoreIn 2).relIndex B = Nat.card ((B.subgroupOf J).map q)
  rw [←relIndex_ker (K := B.subgroupOf J) q]
  rw [show q.ker = pCore 2 J from QuotientGroup.ker_mk' _]
  have he := relIndex_map_map_of_injective (pCore 2 J) (B.subgroupOf J) J.subtype_injective
  rw [map_subgroupOf_eq_of_le hBJ] at he
  exact he

/-- The actual full quotient kernel has small Hermitian coordinate quotient
and is invariant under all original actors in L∩KT. -/
theorem original_hermitian_tits_kernel_coordinates
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup) :
    let B := reducedSubgroup (L ⊔ (T : Subgroup G))
    let J := K ⊔ (T : Subgroup G)
    ∃ (q : L →* Matrix.SpecialLinearGroup (Fin 2) (Field 2))
      (f : B ≃* Multiplicative (Space 2))
      (W : Submodule (ZMod 2) (Space 2)),
      Function.Surjective q ∧ q.ker = pCore 2 L ∧
      (∀ (l : L) (v : B),
        (f (B.normalizerMonoidHom ⟨l,hm.normalizes l.property⟩ v)).toAdd =
          SL2.BinarySmall.hermitian 2 (q l) (f v).toAdd) ∧
      ((T : Subgroup G).subgroupOf L).map q =
        Matrix.SpecialLinearGroup.upperUnipotent (Field 2) ∧
      (∀ v : B, (f v).toAdd ∈ W ↔ (v : G) ∈ J.pCoreIn 2) ∧
      Nat.card ((Space 2) ⧸ W) ≤ 32 ∧
      (∀ (l : L), (l : G) ∈ J → ∀ x ∈ W,
        SL2.BinarySmall.hermitian 2 (q l) x ∈ W) := by
  let B := reducedSubgroup (L ⊔ (T : Subgroup G))
  let J := K ⊔ (T : Subgroup G)
  obtain ⟨q,f,hq,hf,hS⟩ := kernel_exists_hermitian_sylow_coordinates
    h.sylow_normalizes_L hm
  let W := kernelImageSpace f (J.pCoreIn 2)
  have hBJ : B ≤ J := (h.reduced_enlargement.rankOneInput hout).reduced_le_sylow.trans le_sup_right
  have hk : q.ker = pCore 2 L := by
    rw [BinaryConjugationCoordinates.model_kernel L B hm.normalizes
      (SL2.BinarySmall.hermitian 2) (OrthogonalFourMinus.RankOne.hermitian_injective 2) q f hf]
    have he := hm.centralizer_eq_core (OrthogonalFourMinus.RankOne.hermitian_injective 2)
    ext l
    change (l : G) ∈ centralizer (B : Set G) ↔ l ∈ pCore 2 L
    constructor
    · intro hl
      have hh : (l : G) ∈ L.pCoreIn 2 := he ▸ ⟨l.property,hl⟩
      exact (mem_map_iff_mem L.subtype_injective).mp hh
    · intro hl
      have hh : (l : G) ∈ L.pCoreIn 2 := mem_map_of_mem L.subtype hl
      exact (he.symm ▸ hh).2
  refine ⟨q,f,W,hq,hk,hf,hS,fun v => kernelMemImageSpace f _ v,?_,?_⟩
  · rw [show W = kernelImageSpace f (J.pCoreIn 2) from rfl,coordinate_quotient_card hBJ f]
    exact original_hermitian_tits_module_image_card_le h hout hm hM₁ hCM₁ hK hnot hqK e
  · intro l hl x hx
    have hn : (l : G) ∈ normalizer (J.pCoreIn 2 : Set G) :=
      (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))) hl
    exact (kernelNormalizedImageStabilizer hm.normalizes q f hf (J.pCoreIn 2) l hn x).mpr hx

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
