module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.BaumannNormalization.FixedWitness
public import CFSG.Quasithin.ChapterC.Section05.CounterexampleCharacteristic.ReducedMarking.NaturalBaumann

/-!
# A noncentral Thompson-fixed vector in an actual natural block

Restrict the intrinsic full-normalizer action to the normal extension KT.
The actual natural projection retains its possible central kernel. The
semilinear offender theorem gives Thompson fixed codimension n; the
residual fixed kernel has codimension 2n. Their strict inequality produces
a noncentral fixed vector without a splitting or minimality hypothesis.

Source: Aschbacher--Smith C.1.16(2), pp.125--126, applied in C.5.4(1), p.155.
The existing full-normalizer model is retained with its original maps.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BaumannNormalization
open Section05.ConjugateSource.RankOne Section05.CounterexampleCharacteristic Section05.CounterexampleCharacteristic.ReducedMarking
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [Algebra (ZMod 2) F]

omit [Finite G] [Field F] [Finite F] [Algebra (ZMod 2) F] in
theorem thompson_moves_of_moved (K T : Subgroup G) (hK : IsShort K)
    (hm : K = ⁅K,elementaryAbelianMaxJ T⁆) :
    ¬ elementaryAbelianMaxJ T ≤ centralizer (U K : Set G) := by
  intro hc
  have hnU : K ≤ normalizer (U K : Set G) := K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hnC : K ≤ normalizer (centralizer (U K : Set G) : Set G) :=
    hnU.trans (normalizer_le_normalizer_centralizer (U K))
  have hKC : K ≤ centralizer (U K : Set G) := hm.le.trans
    ((commutator_mono le_rfl hc).trans
      (le_normalizer_iff_commutator_le_right.mp hnC))
  have hUC : blockU K ≤ center K := by
    intro u hu
    rw [mem_center_iff]
    intro k
    exact Subtype.ext ((hKC k.property) u (mem_map_of_mem K.subtype hu)).symm
  exact hK.irreducible.1.not_ge (le_inf le_rfl hUC)

theorem natural_fixed_noncentral (K T : Subgroup G) (hK : IsShort K)
    (hT : IsPGroup 2 T) (hn : T ≤ normalizer (K : Set G))
    (P : Sylow 2 (K ⊔ T : Subgroup G))
    (hP : (P : Subgroup (K ⊔ T : Subgroup G)).map (K ⊔ T).subtype = T)
    (hUT : U K ≤ T) (hmoved : K = ⁅K,elementaryAbelianMaxJ T⁆)
    (τ : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (Multiplicative (Fin 2 → F)))
    (m : BlockModuleModel K τ)
    (hτ : ∀ g v, (τ g v).toAdd = Matrix.mulVec g.val v.toAdd)
    (hF : 2 < Nat.card F) :
    ¬ U K ⊓ centralizer (elementaryAbelianMaxJ T : Set G) ≤ centralizer (K : Set G) := by
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
  have hJ : ¬ elementaryAbelianMaxJ (P : Subgroup A) ≤ centralizer (V : Set A) := by
    intro hc
    have hm := map_mono (f := A.subtype) hc
    rw [native_centralizer A (U K) hUA, subgroupOf_map_subtype,
      ←elementaryAbelianMaxJ_map_injective A.subtype A.subtype_injective,hP] at hm
    exact thompson_moves_of_moved K T hK hmoved (hm.trans inf_le_left)
  have hVP : V ≤ (P : Subgroup A) := by
    intro v hv
    obtain ⟨t,ht,he⟩ := hP.symm ▸ hUT hv
    exact (Subtype.ext he : t = v) ▸ ht
  have hdimJ := ChapterB.RankOneBaumann.thompson_fixedCodim_of_semilinear_quotient
    P V q hq hker hVP hJ L e ρ hfaith hnat hF f hf he
  have hdimK := ChapterB.RankOneBaumann.residual_fixedCodim_of_marked_kernel
    V q hq hker f hf hk
  intro hc
  have hbound : V ⊓ centralizer (elementaryAbelianMaxJ (P : Subgroup A) : Set A) ≤
      V ⊓ centralizer (pResidual 2 A : Set A) := by
    rintro v ⟨hv,hvJ⟩
    refine ⟨hv,?_⟩
    have hvC : (v : G) ∈ centralizer (elementaryAbelianMaxJ T : Set G) := by
      intro j hj
      have hj' : j ∈ (elementaryAbelianMaxJ (P : Subgroup A)).map A.subtype := by
        rwa [←elementaryAbelianMaxJ_map_injective A.subtype A.subtype_injective,hP]
      obtain ⟨z,hz,rfl⟩ := hj'
      exact congrArg Subtype.val (hvJ z hz)
    intro k hk
    exact Subtype.ext ((hc ⟨hv,hvC⟩) k (hres ▸ mem_map_of_mem A.subtype hk))
  have hcard := Nat.card_le_card_of_injective _ (inclusion_injective hbound)
  have hlog := Nat.log_mono_right (b := 2) hcard
  have hd : ChapterB.BaumannArgument.fixedCodim V (pResidual 2 A) ≤
      ChapterB.BaumannArgument.fixedCodim V (elementaryAbelianMaxJ (P : Subgroup A)) :=
    Nat.sub_le_sub_left hlog _
  rw [hdimJ,hdimK] at hd
  have hnpos : 0 < Module.finrank (ZMod 2) F := Module.finrank_pos
  omega
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BaumannNormalization
