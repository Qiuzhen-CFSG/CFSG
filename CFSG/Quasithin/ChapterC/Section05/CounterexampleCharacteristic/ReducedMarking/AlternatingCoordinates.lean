module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.Native
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.AlternatingAction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SymmetricFive.A5Source
/-!
# Actual binary coordinates for the reduced alternating action

The original module coordinates remain bijective on the intrinsic subgroup
of KT. The restricted normalizer action agrees on the original K marking.
The proved outer-compatibility theorem upgrades this A₅ equivariance to the
whole S₅ action, retaining the original coordinate map and literal module.

Source: Aschbacher–Smith C.5.4 and C.5.9, printed pp.155 and161.
-/
@[expose] public section
open Subgroup Stellmacher BinaryPermutation Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G}

noncomputable def alternatingNativeCoordinates (h : AlternatingPairSetup R K L) (T : Subgroup G) :
    ((sourceModule K).subgroupOf (K ⊔ T)) ≃* Multiplicative (core (Fin 5)) :=
  (subgroupOfEquivOfLe (show sourceModule K ≤ K ⊔ T from
    (map_subtype_le _).trans le_sup_left)).trans h.coordinates

omit [Finite G] in
theorem alternating_native_marking (h : AlternatingPairSetup R K L)
    (T : Subgroup G) (hn : T ≤ normalizer (K : Set G))
    (hST : ChapterB.baumann R ≤ T) :
    let : ((sourceModule K).subgroupOf (K ⊔ T)).Normal := reduced_module_normal K T hn
    let : IsElementaryAbelian 2 ((sourceModule K).subgroupOf (K ⊔ T)) := reduced_module_elementary K T h.block.2.1
    ∃ (q : (K ⊔ T : Subgroup G) →* FivePerm) (hq : Function.Surjective q)
      (hker : q.ker = centralizer ((sourceModule K).subgroupOf (K ⊔ T) : Set (K ⊔ T : Subgroup G))),
      let p := (alternatingNativeCoordinates h T).toMonoidHom.toAdditiveLeft.toZModLinearMap 2
      Function.Bijective p ∧
      (∀ g v, p (NormalElementaryQuotient.representation _ q hq hker g v) =
        coreRepresentation (Fin 5) g (p v)) ∧
      ∀ s : (K ⊔ ChapterB.baumann R : Subgroup G),
        q (inclusion (sup_le_sup_left hST K) s) = h.action s := by
  let : ((sourceModule K).subgroupOf (K ⊔ T)).Normal := reduced_module_normal K T hn
  let : IsElementaryAbelian 2 ((sourceModule K).subgroupOf (K ⊔ T)) := reduced_module_elementary K T h.block.2.1
  obtain ⟨q,hq,hker,hcompat⟩ := alternating_reduced_action h T hn hST
  have hker' : q.ker = centralizer ((sourceModule K).subgroupOf (K ⊔ T) : Set (K ⊔ T : Subgroup G)) := by
    rw [native_centralizer (K ⊔ T) (sourceModule K) ((map_subtype_le _).trans le_sup_left)]
    exact hker
  let p := (alternatingNativeCoordinates h T).toMonoidHom.toAdditiveLeft.toZModLinearMap 2
  have hp : Function.Bijective p := (alternatingNativeCoordinates h T).bijective
  let ρ := NormalElementaryQuotient.representation _ q hq hker'
  have he : ∀ g ∈ alternatingGroup (Fin 5), ∀ v, p (ρ g v) = coreRepresentation (Fin 5) g (p v) := by
    intro g hg v
    obtain ⟨k,hk,hkg⟩ : ∃ k ∈ K.subgroupOf (K ⊔ ChapterB.baumann R), h.action k = g :=
      (h.block_image.symm ▸ hg : g ∈ (K.subgroupOf (K ⊔ ChapterB.baumann R)).map h.action)
    let a : (K ⊔ T : Subgroup G) := inclusion (sup_le_sup_left hST K) k
    have haq : q a = g := (hcompat k).trans hkg
    have heq := h.equivariant k ⟨(v.toMul : (K ⊔ T : Subgroup G)),v.toMul.property⟩
    have hv : ((ρ (q a) v).toMul : (K ⊔ T : Subgroup G)) =
        a * (v.toMul : (K ⊔ T : Subgroup G)) * a⁻¹ :=
      NormalElementaryQuotient.representation_apply _ q hq hker' a v
    apply Multiplicative.ofAdd.injective
    apply h.coordinates.symm.injective
    apply Subtype.ext
    change (h.coordinates.symm (h.coordinates
      ⟨((ρ g v).toMul : (K ⊔ T : Subgroup G)), (ρ g v).toMul.property⟩) : G) = _
    rw [h.coordinates.symm_apply_apply]
    have hvG := congrArg Subtype.val hv
    change (((ρ g v).toMul : (K ⊔ T : Subgroup G)) : G) = _
    rw [← haq]
    exact hvG.trans (heq.symm.trans (by rw [hkg,haq]; rfl))
  have hall : ∀ g v, p (ρ g v) = coreRepresentation (Fin 5) g (p v) :=
    FiveCentralExtension.equivariant_of_alternating ρ p hp.2 he (by
      intro v hv g hg
      have hz : v = 0 := hp.1 (hv.trans (map_zero p).symm)
      rw [hz,map_zero])
  exact ⟨q,hq,hker',hp,hall,hcompat⟩
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
