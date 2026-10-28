module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalReeCompletion.OuterSylow
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.GeneralReeFour.LongCentralizer

/-!
# Full long-root centralizers across the original Ree normalizer marking

The original full centralizer bound and perfect whole residual identify
that centralizer's embedded solvable residual with O²(H). The actual pure
right-parabolic map sends its central involution to a native long-root
involution. The full endpoint marking sends the same element to its inner
automorphism in the constructed extension. Native residual preservation
then puts the full extension centralizer in its right endpoint.

Restricting the literal full-normalizer equivalence consequently identifies
the entire ambient centralizer with the entire extension centralizer. The
existence theorem keeps these maps together with both endpoint markings,
the whole Borel comparison, odd outer degree and the original ambient Sylow.
No new action, extension, fusion, order or recognition premise is added.
Involution exhaustion and full short-root centralizer containment remain
necessary for F.4.43 and the final ambient recognition.
Source: Aschbacher–Smith 5.3.1–3 and F.4.27,35,43,
printed pp.658–659,288,291–292,296 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels ChapterF.SourceCompletion
variable {G : Type*} [Group G]

/-- The literal full right-normalizer map into the same extension carrier. -/
@[expose] def FullNormalizerMarking.rightToCarrier {N : Type*} [Group N]
    {L K S : Subgroup G} {R₀ C R₁ : Subgroup N}
    {β : RankTwoAmalgam R₀ C R₁} (D : FullNormalizerMarking L K S R₀ C R₁ β) :
    normalizer (K : Set G) →* D.extension.carrier :=
  (inclusion D.extension.right_le).comp D.full.right.toMonoidHom

/-- Faithfulness of the marked full right-normalizer map. -/
theorem FullNormalizerMarking.rightToCarrier_injective {N : Type*} [Group N]
    {L K S : Subgroup G} {R₀ C R₁ : Subgroup N}
    {β : RankTwoAmalgam R₀ C R₁} (D : FullNormalizerMarking L K S R₀ C R₁ β) :
    Function.Injective D.rightToCarrier :=
  (inclusion_injective D.extension.right_le).comp D.full.right.injective

/-- Its range is the whole right endpoint inside this extension. -/
theorem FullNormalizerMarking.rightToCarrier_range {N : Type*} [Group N]
    {L K S : Subgroup G} {R₀ C R₁ : Subgroup N}
    {β : RankTwoAmalgam R₀ C R₁} (D : FullNormalizerMarking L K S R₀ C R₁ β) :
    D.rightToCarrier.range = D.extension.right.subgroupOf D.extension.carrier := by
  rw [FullNormalizerMarking.rightToCarrier,MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr D.full.right.surjective,
    ←MonoidHom.range_eq_map,inclusion_range]

private theorem center_image {X : Type*} [Group X]
    {K P : Subgroup G} {R : Subgroup X} (hKP : K ≤ P)
    (f : P →* X) (hR : (K.subgroupOf P).map f = R) (z : center K) :
    f ⟨z.val.val,hKP z.val.property⟩ ∈ (center R).map R.subtype := by
  let a : P := ⟨z.val.val,hKP z.val.property⟩
  have haR : f a ∈ R := hR ▸ mem_map_of_mem f z.val.property
  refine ⟨⟨f a,haR⟩,mem_center_iff.mpr ?_,rfl⟩
  intro r
  have hr : r.val ∈ (K.subgroupOf P).map f := hR.symm ▸ r.property
  obtain ⟨b,hb,he⟩ := hr
  apply Subtype.ext
  change r.val * f a = f a * r.val
  rw [←he,←map_mul,←map_mul]
  apply congrArg f
  apply Subtype.ext
  exact congrArg (fun k : K => k.val) (mem_center_iff.mp z.property ⟨b,hb⟩)

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

/-- The whole original residual is exactly the embedded solvable residual of every original long-root centralizer. -/
theorem Preparation.ree_long_centralizer_residual_eq
    (z : center (residual H)) (hz2 : orderOf z = 2) :
    (solvableResidual (centralizer ({z.val.val} : Set G))).map
      (centralizer ({z.val.val} : Set G)).subtype = residual H := by
  let := hp
  have hzG : orderOf z.val.val = 2 := by
    rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe,hz2]
  have hC := d.ree_central_involution_centralizers h hH hp m he 1 z.val.val
    (mem_map_of_mem _ z.property) hzG
  have hN := d.ree_normalizer_residuals h hH hp m he 1
  apply le_antisymm
  · exact (map_solvableResidual_mono hC).trans_eq hN
  · apply le_map_solvableResidual_of_isPerfect
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp z.property ⟨x,hx⟩))

/-- The given full marking identifies both entire long-root centralizers by its literal right-endpoint map. -/
theorem Preparation.ree_long_centralizer_comparison
    (D : ReeNormalizerMarking L (residual H) (sourceS L H) m)
    (z : center (residual H)) (hz2 : orderOf z = 2) :
    let zN : normalizer (residual H : Set G) :=
      ⟨z.val.val,(residual H).le_normalizer z.val.property⟩
    ((centralizer ({z.val.val} : Set G)).subgroupOf
      (normalizer (residual H : Set G))).map D.rightToCarrier =
        centralizer ({D.rightToCarrier zN} : Set D.extension.carrier) ∧
    Nonempty (centralizer ({z.val.val} : Set G) ≃*
      centralizer ({D.rightToCarrier zN} : Set D.extension.carrier)) := by
  let P := ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1
  have hKP : residual H ≤ P := le_sup_left.trans le_sup_left
  let a : P := ⟨z.val.val,hKP z.val.property⟩
  let zN : normalizer (residual H : Set G) :=
    ⟨z.val.val,(residual H).le_normalizer z.val.property⟩
  have hm := d.ree_parameter_positive h hp m 1 .suzuki D.pure.right
  let f := (ReeF4.Parabolics.parabolic m .suzuki).subtype.comp D.pure.right.toMonoidHom
  have hres : (residual H).subgroupOf P = solvableResidual P := by
    have hr : (solvableResidual P).map P.subtype = residual H :=
      d.parabolic_residuals h hH.1.1.2 hp 1
    rw [←hr]
    exact comap_map_eq_self_of_injective P.subtype_injective _
  have hR : ((residual H).subgroupOf P).map f =
      ReeF4.Parabolics.localFactor m .suzuki := by
    rw [hres,show f = (ReeF4.Parabolics.parabolic m .suzuki).subtype.comp
      D.pure.right.toMonoidHom from rfl,←map_map,
      map_solvableResidual_eq _ D.pure.right.surjective]
    exact ReeF4.Parabolics.parabolic_solvableResidual_map hm .suzuki
  have haZ := center_image hKP f hR z
  rw [ReeF4.SourceCompletion.suzuki_center_eq_longRoot hm] at haZ
  have hf : Function.Injective f :=
    (ReeF4.Parabolics.parabolic m .suzuki).subtype_injective.comp D.pure.right.injective
  have hzG : orderOf z.val.val = 2 := by
    rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe,hz2]
  have ha1 : f a ≠ 1 := by
    intro hh
    have hz1 : z.val.val = 1 := congrArg Subtype.val (hf (hh.trans (map_one f).symm))
    simp [hz1] at hzG
  have hmark : D.rightToCarrier zN = D.extension.baseHom (f a) := by
    apply Subtype.ext
    exact D.right_marking a
  have hC : centralizer ({D.rightToCarrier zN} : Set D.extension.carrier) ≤
      D.rightToCarrier.range := by
    rw [D.rightToCarrier_range,hmark]
    exact GeneralReeFour.extension_long_centralizer_le_right D.extension hm haZ ha1
  have hmap := centralizer_map_of_range _ D.rightToCarrier D.rightToCarrier_injective zN hC
  have hCG := d.ree_central_involution_centralizers h hH hp m he 1 z.val.val
    (mem_map_of_mem _ z.property) hzG
  change centralizer ({z.val.val} : Set G) ≤ normalizer (residual H : Set G) at hCG
  refine ⟨hmap,⟨?_⟩⟩
  exact (subgroupOfEquivOfLe hCG).symm.trans
    ((((centralizer ({z.val.val} : Set G)).subgroupOf (normalizer (residual H : Set G))).equivMapOfInjective
      D.rightToCarrier D.rightToCarrier_injective).trans (MulEquiv.subgroupCongr hmap))

/-- The original prepared row supplies all full long-root centralizer comparisons in the same extension carrying its Sylow. -/
theorem Preparation.ree_full_extension_long_centralizers :
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
      ∀ z : center (residual H), orderOf z = 2 →
        let zN : normalizer (residual H : Set G) :=
          ⟨z.val.val,(residual H).le_normalizer z.val.property⟩
        ((centralizer ({z.val.val} : Set G)).subgroupOf
          (normalizer (residual H : Set G))).map D.rightToCarrier =
            centralizer ({D.rightToCarrier zN} : Set D.extension.carrier) ∧
        Nonempty (centralizer ({z.val.val} : Set G) ≃*
          centralizer ({D.rightToCarrier zN} : Set D.extension.carrier)) := by
  obtain ⟨hn,hm,D,hdeg,hodd,hcyc,hres,hcard,hT,hS⟩ :=
    d.ree_full_extension_outer_sylow h hH hp m he
  exact ⟨hn,hm,D,hdeg,hodd,hcyc,hres,hcard,hT,hS,
    fun z hz => d.ree_long_centralizer_comparison h hH hp m he D z hz⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
