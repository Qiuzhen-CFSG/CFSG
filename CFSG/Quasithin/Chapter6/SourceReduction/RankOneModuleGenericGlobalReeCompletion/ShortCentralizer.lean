module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.LongCentralizer
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.ShortCentralizer

/-!
# The original short-root marker and its full-extension centralizer

The same full-normalizer extension supplies a native short-root involution
in the linear radical with full extension centralizer in the left endpoint.
The original compatible pure map carries the actual radical to O₂(L), and
the full endpoint marking identifies the original normalizer-centralizer
with that entire extension centralizer. An injective map from the native
centralizer preserves divisibility by three in the ambient solvable
residual, excluding fusion with all original long-root center involutions.

The final theorem retains the same carrier's odd cyclic outer degree,
original Sylow marking, both endpoints, whole Borel and entire long-root
centralizer comparisons. Full ambient short-root containment and exhaustion
of the involution classes remain for F.4.42–43; no ambient order or
recognition hypothesis is added here.
Source: Aschbacher–Smith 5.3.1–3 and F.4.27,35,42–43,
printed pp.658–659,288,292,295–296 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds ReeF4.EvenInvolutionGeometry
variable {G : Type*} [Group G]
/-- The literal full left-normalizer map into the same extension carrier. -/
@[expose] def FullNormalizerMarking.leftToCarrier {N : Type*} [Group N]
    {L K S : Subgroup G} {R₀ C R₁ : Subgroup N}
    {β : RankTwoAmalgam R₀ C R₁} (D : FullNormalizerMarking L K S R₀ C R₁ β) :
    normalizer (L : Set G) →* D.extension.carrier :=
  (inclusion D.extension.left_le).comp D.full.left.toMonoidHom

/-- Faithfulness of the marked full left-normalizer map. -/
theorem FullNormalizerMarking.leftToCarrier_injective {N : Type*} [Group N]
    {L K S : Subgroup G} {R₀ C R₁ : Subgroup N}
    {β : RankTwoAmalgam R₀ C R₁} (D : FullNormalizerMarking L K S R₀ C R₁ β) :
    Function.Injective D.leftToCarrier :=
  (inclusion_injective D.extension.left_le).comp D.full.left.injective

/-- Its range is the whole left endpoint inside this extension. -/
theorem FullNormalizerMarking.leftToCarrier_range {N : Type*} [Group N]
    {L K S : Subgroup G} {R₀ C R₁ : Subgroup N}
    {β : RankTwoAmalgam R₀ C R₁} (D : FullNormalizerMarking L K S R₀ C R₁ β) :
    D.leftToCarrier.range = D.extension.left.subgroupOf D.extension.carrier := by
  rw [FullNormalizerMarking.leftToCarrier,MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr D.full.left.surjective,
    ←MonoidHom.range_eq_map,inclusion_range]

private theorem centralizer_map_of_range {X : Type*} [Group X]
    (P : Subgroup G) (f : P →* X) (hf : Function.Injective f)
    (z : P) (hC : centralizer ({f z} : Set X) ≤ f.range) :
    ((centralizer ({z.val} : Set G)).subgroupOf P).map f =
      centralizer ({f z} : Set X) := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have he : x*z = z*x := Subtype.ext (mem_centralizer_singleton_iff.mp hx)
    simpa only [map_mul] using congrArg f he
  · intro y hy
    obtain ⟨x,rfl⟩ := hC hy
    refine ⟨x,mem_centralizer_singleton_iff.mpr ?_,rfl⟩
    have hcomm : x*z = z*x := hf (by
      simpa only [map_mul] using mem_centralizer_singleton_iff.mp hy)
    exact congrArg Subtype.val hcomm

variable [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B (residual H))
  (h : Input KnownSimple.IsKnownSimple T L W n)
  (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
  (hp : Group.IsPerfect (residual H)) (m : ℕ)
  (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) (ReeFour.amalgam m).reverse))
include d h hH hp he

/-- The same full marking compares the entire extension short-root centralizer with the original left-normalizer centralizer. Ambient nonfusion holds for this actual marker. -/
theorem Preparation.ree_short_centralizer_comparison
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m) :
    ∃ (t : Model m) (v : normalizer (L : Set G)),
      IsShortRootInvolution t ∧ t ∈ radical m .linear ∧
      v.val ∈ L.pCoreIn 2 ∧ orderOf v.val = 2 ∧
      D.leftToCarrier v = D.extension.baseHom t ∧
      ((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))).map
        D.leftToCarrier = centralizer ({D.extension.baseHom t} : Set D.extension.carrier) ∧
      Nonempty (((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))) ≃*
        centralizer ({D.extension.baseHom t} : Set D.extension.carrier)) ∧
      3 ∣ Nat.card (solvableResidual (centralizer ({v.val} : Set G))) ∧
      ∀ z ∈ (center (residual H)).map (residual H).subtype,
        orderOf z = 2 → ¬ IsConj z v.val := by
  have hm := d.ree_parameter_positive h hp m 0 .linear D.pure.left
  obtain ⟨t,ht,ht2,htQ,hCt,hCtE⟩ :=
    GeneralReeFour.extension_short_centralizer_placement D.extension hm 1 one_ne_zero
  have hshort : IsShortRootInvolution t := ⟨1,one_ne_zero,ht⟩
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0
  let a : parabolic m .linear := ⟨t,((radical_le_localFactor m .linear).trans (localFactor_le_parabolic m .linear)) htQ⟩
  let f : parabolic m .linear →* G := P.subtype.comp D.pure.left.symm.toMonoidHom
  have hf : Function.Injective f := P.subtype_injective.comp D.pure.left.symm.injective
  let J := (localFactor m .linear).subgroupOf (parabolic m .linear)
  have hJ : J = solvableResidual (parabolic m .linear) := by
    apply map_injective (parabolic m .linear).subtype_injective
    rw [map_subgroupOf_eq_of_le (localFactor_le_parabolic m .linear),
      parabolic_solvableResidual_map hm .linear]
  have hJf : J.map f = L := by
    rw [hJ,show f = P.subtype.comp D.pure.left.symm.toMonoidHom from rfl,
      ←map_map,map_solvableResidual_eq _ D.pure.left.symm.surjective]
    exact d.parabolic_residuals h hH.1.1.2 hp 0
  have hcore : (localFactor m .linear).pCoreIn 2 = radical m .linear := by
    rw [pCoreIn,←localRadical_eq_pCore,localRadical_map]
  have hQ : ((radical m .linear).subgroupOf (parabolic m .linear)).map f = L.pCoreIn 2 := by
    have hh := map_pCoreIn_of_injective 2 J f hf
    rw [hJf,pCoreIn_subgroupOf 2 _ _ (localFactor_le_parabolic m .linear),hcore] at hh
    exact hh
  have hva : f a ∈ L.pCoreIn 2 := hQ ▸ mem_map_of_mem f htQ
  let v : normalizer (L : Set G) := ⟨f a,L.le_normalizer (pCoreIn_le 2 L hva)⟩
  have hmark : D.leftToCarrier v = D.extension.baseHom t := by
    apply Subtype.ext
    have hh := D.left_marking (D.pure.left.symm a)
    rw [D.pure.left.apply_symm_apply] at hh
    exact hh
  have hmap : ((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))).map
      D.leftToCarrier = centralizer ({D.extension.baseHom t} : Set D.extension.carrier) := by
    rw [←hmark]
    apply centralizer_map_of_range _ D.leftToCarrier D.leftToCarrier_injective v
    rw [D.leftToCarrier_range,hmark]
    exact hCtE
  let k : centralizer ({t} : Set (Model m)) →* G := f.comp (inclusion hCt)
  have hk : Function.Injective k := hf.comp (inclusion_injective hCt)
  have hkC (x : centralizer ({t} : Set (Model m))) : k x ∈ centralizer ({v.val} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh : inclusion hCt x * a = a * inclusion hCt x :=
      Subtype.ext (mem_centralizer_singleton_iff.mp x.property)
    exact (map_mul f _ _).symm.trans ((congrArg f hh).trans (map_mul f _ _))
  let kC := k.codRestrict (centralizer ({v.val} : Set G)) hkC
  have hkCi : Function.Injective kC := (MonoidHom.injective_codRestrict _ _ _).mpr hk
  let kR := (kC.comp (solvableResidual (centralizer ({t} : Set (Model m)))).subtype).codRestrict
    (solvableResidual (centralizer ({v.val} : Set G))) (fun x =>
      map_solvableResidual_le kC (mem_map_of_mem kC x.property))
  have hkR : Function.Injective kR := (MonoidHom.injective_codRestrict _ _ _).mpr
    (hkCi.comp (solvableResidual (centralizer ({t} : Set (Model m)))).subtype_injective)
  have h3 : 3 ∣ Nat.card (solvableResidual (centralizer ({v.val} : Set G))) :=
    (ReeF4.SourceCompletion.short_centralizer_residual_three_dvd hm hshort).trans
      (card_dvd_of_injective kR hkR)
  refine ⟨t,v,hshort,htQ,hva,?_,hmark,hmap,?_,h3,?_⟩
  · exact (orderOf_injective f hf a).trans ((Subgroup.orderOf_coe a).symm.trans ht2)
  · exact ⟨(((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))).equivMapOfInjective
      D.leftToCarrier D.leftToCarrier_injective).trans (MulEquiv.subgroupCongr hmap)⟩
  · intro z hz hz2 hconj
    have hfree := d.ree_long_centralizer_residual_three_free h hH hp m he z hz hz2
    obtain ⟨g,hg⟩ := isConj_iff.mp hconj
    change (MulAut.conj g) z = v.val at hg
    have hc := Nat.card_congr
      (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g) z).solvableResidualEquiv.toEquiv
    rw [hg] at hc
    exact hfree (hc.symm ▸ h3)

/-- Original inputs retain the odd outer degree, Sylow and entire long-root comparison while adding the full extension short-root comparison in the very same carrier. -/
theorem Preparation.ree_full_extension_short_centralizers :
    2*m+1 = n ∧ 0 < m ∧
    ∃ D : ReeNormalizerMarking L (residual H) (sourceS L H) m,
      let J := (MulAut.innerSubgroup (ReeF4.Model m)).subgroupOf D.extension.carrier
      J.index ∣ 2*m+1 ∧ Odd J.index ∧ IsCyclic (D.extension.carrier ⧸ J) ∧
      primeToResidual 2 D.extension.carrier = J ∧
      Nat.card D.extension.carrier = J.index * Nat.card (ReeF4.Model m) ∧
      (T : Subgroup G) ≤ normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
      (∃ S : Sylow 2 D.extension.carrier,
        (S : Subgroup D.extension.carrier) =
          ((T : Subgroup G).subgroupOf (normalizer (L : Set G) ⊓
            normalizer (residual H : Set G))).map D.middleToCarrier) ∧
      (∀ z : center (residual H), orderOf z = 2 →
        let zN : normalizer (residual H : Set G) :=
          ⟨z.val.val,(residual H).le_normalizer z.val.property⟩
        ((centralizer ({z.val.val} : Set G)).subgroupOf
          (normalizer (residual H : Set G))).map D.rightToCarrier =
            centralizer ({D.rightToCarrier zN} : Set D.extension.carrier) ∧
        Nonempty (centralizer ({z.val.val} : Set G) ≃*
          centralizer ({D.rightToCarrier zN} : Set D.extension.carrier))) ∧
      ∃ (t : Model m) (v : normalizer (L : Set G)),
      IsShortRootInvolution t ∧ t ∈ radical m .linear ∧
      v.val ∈ L.pCoreIn 2 ∧ orderOf v.val = 2 ∧
      D.leftToCarrier v = D.extension.baseHom t ∧
      ((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))).map
        D.leftToCarrier = centralizer ({D.extension.baseHom t} : Set D.extension.carrier) ∧
      Nonempty (((centralizer ({v.val} : Set G)).subgroupOf (normalizer (L : Set G))) ≃*
        centralizer ({D.extension.baseHom t} : Set D.extension.carrier)) ∧
      3 ∣ Nat.card (solvableResidual (centralizer ({v.val} : Set G))) ∧
      ∀ z ∈ (center (residual H)).map (residual H).subtype,
        orderOf z = 2 → ¬ IsConj z v.val := by
  obtain ⟨hn,hm,D,hdeg,hodd,hcyc,hres,hcard,hT,hS,hlong⟩ :=
    d.ree_full_extension_long_centralizers h hH hp m he
  exact ⟨hn,hm,D,hdeg,hodd,hcyc,hres,hcard,hT,hS,hlong,
    d.ree_short_centralizer_comparison h hH hp m he D⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
