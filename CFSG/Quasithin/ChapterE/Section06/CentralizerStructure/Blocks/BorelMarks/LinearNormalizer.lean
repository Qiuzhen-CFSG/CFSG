module
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.RankOneSetup.NaturalAction
public import Theory.GroupTheory.ElementaryThompsonQuotientNormalizer
public import Theory.GroupTheory.QuotientIntersection

/-!
# A natural block's Sylow normalizer preserves the original Thompson subgroup

The actual block module extends to the whole block normalizer, retaining its
central cover. In a normalized two-group extension, the semilinear natural
module theorem identifies the Thompson image with the inner Sylow image.
The action kernel is the original two-core and lies in the chosen Sylow
subgroup, so Thompson normalizers lift exactly. This puts the normalizer of
the block Sylow intersection in the normalizer of the original Thompson
subgroup; no Borel marking or extra normalizer hypothesis is assumed.

Source: Aschbacher–Smith C.1.29, printed p.134, using B.6.10, p.117.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06
open ChapterC ChapterC.Section05 ChapterC.Section05.ConjugateSource.RankOne
open ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [Algebra (ZMod 2) F]

theorem natural_sylow_normalizer_preserves_thompson
    (K T : Subgroup G) (hK : IsShort K)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hmove : K = ⁅K,elementaryAbelianMaxJ T⁆)
    (τ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (Multiplicative (Fin 2 → F)))
    (m : BlockModuleModel K τ)
    (hτ : ∀ g v, (τ g v).toAdd = Matrix.mulVec g.val v.toAdd)
    (hF : 2 < Nat.card F) :
    K ⊓ normalizer (↑(K ⊓ T) : Set G) ≤ normalizer (elementaryAbelianMaxJ T : Set G) := by
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
  have hJ := BlockAnalysis.AlternatingSetup.native_thompson_moves_of_commutator K T hK P hP hmove
  have hred := reduced_module_reduced K T hK hT hn
  have hi := (ChapterB.RankOneBaumann.thompson_baumann_images_of_semilinear_quotient
    P V q hq hker (hred.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal P))
      hJ L e ρ hfaith hnat hF f hf he).1
  have hkP : q.ker ≤ P := by
    rw [hker,reduced_module_core K T hK hT hn]
    exact pCore_isPGroup.le_sylow_of_normal P
  have hPi : (P : Subgroup A) = T.subgroupOf A := by
    apply map_injective A.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (show T ≤ A from le_sup_right)]
  have heJ : (elementaryAbelianMaxJ (P : Subgroup A)).map q =
      ((K ⊓ T).subgroupOf A).map q := by
    rw [hi,←hL,inf_comm,←map_inf_of_ker_le q _ _ hkP,hPi]
    rfl
  have hJA : (elementaryAbelianMaxJ (P : Subgroup A)).map A.subtype = elementaryAbelianMaxJ T := by
    rw [←elementaryAbelianMaxJ_map_injective A.subtype A.subtype_injective,hP]
  intro x hx
  let xA : A := ⟨x,(show K ≤ A from le_sup_left) hx.1⟩
  have hxA : xA ∈ normalizer (((K ⊓ T).subgroupOf A) : Set A) := by
    intro y
    exact hx.2 (y : G)
  have hxq : q xA ∈ normalizer ((elementaryAbelianMaxJ (P : Subgroup A)).map q : Set H) := by
    rw [heJ]
    exact (((K ⊓ T).subgroupOf A).le_normalizer_map q) (mem_map_of_mem q hxA)
  have hxJ : xA ∈ normalizer (elementaryAbelianMaxJ (P : Subgroup A) : Set A) := by
    rw [←normalizer_comap_map_maxJ (P : Subgroup A) q hq hkP]
    exact hxq
  rw [←hJA]
  exact (elementaryAbelianMaxJ (P : Subgroup A)).le_normalizer_map A.subtype
    (mem_map_of_mem A.subtype hxJ)

end CFSG.Quasithin.ChapterE.Section06
