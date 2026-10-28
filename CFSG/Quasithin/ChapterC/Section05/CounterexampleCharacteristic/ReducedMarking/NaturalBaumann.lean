module
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.Native
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.SemilinearModel
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.SemilinearSource
/-!
# The reduced Baumann Sylow theorem for the actual natural cover

Restrict the intrinsic cover action to KT and pass to its actual image.
Its normal SL₂ layer is the literal K-image. The projection keeps precisely
C_U(K), identified with the fixed space of the actual residual. The checked
semilinear Baumann theorem therefore proves that Baum(T) is Sylow in
K Baum(T), with no deletion of the central cover or outer field action.

Source: Aschbacher–Smith C.5.4 and C.5.9, pp.155 and161, using B.6.10.
-/
public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
open ConjugateSource.RankOne
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [Algebra (ZMod 2) F]

theorem natural_reduced_action_and_sylow (K T : Subgroup G) (hK : IsShort K)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hmin : ChapterB.IsMinimalParabolicOver P ⊤)
    (hno : ∀ N : Subgroup G, N ≤ T → normalizer (T : Set G) ≤ normalizer (N : Set G) →
      K ⊔ T ≤ normalizer (N : Set G) → N = ⊥)
    (τ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (Multiplicative (Fin 2 → F)))
    (m : BlockModuleModel K τ)
    (hτ : ∀ g v, (τ g v).toAdd = Matrix.mulVec g.val v.toAdd)
    (hF : 2 < Nat.card F) :
    ∃ β : normalizer (K : Set G) →* MulAut (Multiplicative (Fin 2 → F)),
      (∀ a u, β a (modelProjection m u) = modelProjection m (normalizerConjugate a u)) ∧
      β.ker = (centralizer (U K : Set G)).subgroupOf (normalizer (K : Set G)) ∧
      (K.subgroupOf (normalizer (K : Set G))).map β = τ.range ∧
      ((S T).subgroupOf (normalizer (K : Set G))).map β ≤ τ.range ∧
      Chapter1.IsSylowIn 2 (S T) (K ⊔ S T) := by
  let A := K ⊔ T
  let N := normalizer (K : Set G)
  have hAN : A ≤ N := sup_le K.le_normalizer hn
  have hUA : U K ≤ A := (map_subtype_le _).trans le_sup_left
  let V := (U K).subgroupOf A
  let : V.Normal := reduced_module_normal K T hn
  let : IsElementaryAbelian 2 V := reduced_module_elementary K T hK
  obtain ⟨β,hβ,hβker,hβK⟩ := exists_full_model_action hK m (natural_action_injective τ hτ)
  let a := β.comp (inclusion hAN)
  let H := a.range
  let q : A →* H := a.rangeRestrict
  have hq : Function.Surjective q := a.rangeRestrict_surjective
  have hker : q.ker = centralizer (V : Set A) := by
    rw [native_centralizer A (U K) hUA]
    ext z
    change q z = 1 ↔ (z : G) ∈ centralizer (U K : Set G)
    rw [Subtype.ext_iff]
    change a z = 1 ↔ (z : G) ∈ centralizer (U K : Set G)
    change inclusion hAN z ∈ β.ker ↔ _
    rw [hβker]
    rfl
  have haK : (K.subgroupOf A).map a = τ.range := by
    calc
      _ = (K.subgroupOf N).map β := by
        ext z
        constructor
        · rintro ⟨k,hk,rfl⟩
          exact ⟨inclusion hAN k,hk,rfl⟩
        · rintro ⟨k,hk,rfl⟩
          exact ⟨⟨k,(show K ≤ A from le_sup_left) hk⟩,hk,rfl⟩
      _ = τ.range := hβK
  have hτH : τ.range ≤ H := haK.symm ▸ map_le_range _ _
  let L := τ.range.subgroupOf H
  have hL : (K.subgroupOf A).map q = L := by
    apply map_injective H.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le hτH]
    exact haK
  let : (K.subgroupOf A).Normal :=
    (normal_subgroupOf_iff_le_normalizer (show K ≤ A from le_sup_left)).mpr hAN
  let : L.Normal := hL ▸ Subgroup.Normal.map inferInstance q hq
  let e : L ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (subgroupOfEquivOfLe hτH).trans (MonoidHom.ofInjective (natural_action_injective τ hτ)).symm
  let ρ := automorphismRepresentation H
  have hfaith : Function.Injective ρ := by
    intro b c he
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    exact Multiplicative.toAdd.injective (congrArg (fun f => f v.toAdd) he)
  have hnat (g : L) (v : Fin 2 → F) : ρ (g : H) v = Matrix.mulVec (e g).val v := by
    have he : τ (e g) = ((g : H) : MulAut (Multiplicative (Fin 2 → F))) :=
      MonoidHom.apply_ofInjective_symm (natural_action_injective τ hτ) _
    change (((g : H) : MulAut (Multiplicative (Fin 2 → F))) (Multiplicative.ofAdd v)).toAdd = _
    rw [← he,hτ]
    rfl
  let eV : V ≃* U K := subgroupOfEquivOfLe hUA
  let f := ((modelProjection m).comp eV.toMonoidHom).toAdditiveLeft.toZModLinearMap 2
  have hf : Function.Surjective f := (modelProjection_surjective m).comp eV.surjective
  have he : ∀ g v, f (NormalElementaryQuotient.representation V q hq hker g v) = ρ g (f v) := by
    intro g v
    obtain ⟨z,rfl⟩ := hq g
    have hv := NormalElementaryQuotient.representation_apply V q hq hker z v
    have heV : eV (NormalElementaryQuotient.representation V q hq hker (q z) v).toMul =
        normalizerConjugate (inclusion hAN z) (eV v.toMul) := by
      apply Subtype.ext
      exact congrArg (fun z : A => (z : G)) hv
    change (modelProjection m (eV (NormalElementaryQuotient.representation V q hq hker (q z) v).toMul)).toAdd = _
    rw [heV,← hβ]
    rfl
  have hres := normal_extension_residual K T hK.twoPerfect hT hn
  have hk : f.ker = fixedSpace (NormalElementaryQuotient.representation V q hq hker) ((pResidual 2 A).map q) := by
    ext v
    rw [NormalElementaryQuotient.mem_fixedSpace_image]
    change f v = 0 ↔ _
    have hp : f v = 0 ↔ ((v.toMul : A) : G) ∈ centralizer (K : Set G) :=
      modelProjection_kernel m (eV v.toMul)
    rw [hp]
    constructor
    · intro hc k hk
      apply Subtype.ext
      exact hc k (hres ▸ mem_map_of_mem A.subtype hk)
    · intro hc k hk
      obtain ⟨z,hz,rfl⟩ := (hres.symm ▸ hk : k ∈ (pResidual 2 A).map A.subtype)
      exact congrArg Subtype.val (hc z hz)
  have hred := reduced_module_reduced K T hK hT hn
  have hJ := native_thompson_moves K T hK hT hn P hP hno
  have hs := (ChapterB.RankOneBaumann.semilinear_baumann_sylow_and_alpha
    P hmin V hred hJ q hq hker L e ρ hfaith hnat hF f hf he hk).1
  have hm := (Chapter1.IsSylowIn.map_iff A.subtype A.subtype_injective).mpr hs
  have hB : (ChapterB.baumann (P : Subgroup A)).map A.subtype = S T :=
    (show (ChapterB.baumann (P : Subgroup A)).map A.subtype =
      ChapterB.baumann ((P : Subgroup A).map A.subtype) from
      baumann_map_injective A.subtype A.subtype_injective (P : Subgroup A)).trans
        (congrArg ChapterB.baumann hP)
  rw [Subgroup.map_sup,hres,hB] at hm
  have hi := (ChapterB.RankOneBaumann.thompson_baumann_images_of_semilinear_quotient
    P V q hq hker (hred.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal P))
      hJ L e ρ hfaith hnat hF f hf he).2
  have hbA : ChapterB.baumann (P : Subgroup A) = (S T).subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [hB,map_subgroupOf_eq_of_le (show S T ≤ A from inf_le_left.trans le_sup_right)]
  have hsmall : ((S T).subgroupOf N).map β ≤ τ.range := by
    rintro b ⟨s,hs,rfl⟩
    let z : A := ⟨s,(show T ≤ A from le_sup_right) (show (s : G) ∈ T from hs.1)⟩
    have hz : q z ∈ (ChapterB.baumann (P : Subgroup A)).map q :=
      mem_map_of_mem q (hbA.symm ▸ hs)
    have hzL := (hi ▸ hz).2
    exact hzL
  exact ⟨β,hβ,hβker,hβK,hsmall,hm⟩
end CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
