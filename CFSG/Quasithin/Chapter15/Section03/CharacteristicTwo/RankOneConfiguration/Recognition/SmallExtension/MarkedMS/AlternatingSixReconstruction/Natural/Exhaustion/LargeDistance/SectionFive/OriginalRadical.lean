module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeThompson
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.PerfectSmallNormalizer

/-!
# Recovering the original radical on a nonsylow replacement

The original group M = L join R acts faithfully modulo O₂(M) on the same
natural four-dimensional quotient. Its marked A₆ component is normal, so
its whole linear action lies in the natural S₆ normalizer. Extend the
canonical six-letter projection to M and prove agreement with the literal
replacement inclusion. A full replacement action then gives
M = d.overgroup O₂(M), retaining the possible core factors outside the
replacement.

At distance greater than two, a nonsylow original radical has replacement
image of order eight. Its own image is a two-subgroup of S₆ containing
that image; order sixteen would make the original radical Sylow. The two
images therefore coincide. Pullback gives R = d.ambient O₂(M), and the
original characteristic-reduction core cut gives
R intersect d.overgroup = d.ambient.

Now restrict the actual MS2(a) witness H to the replacement overgroup.
Normality makes its two-core the restriction of O₂(H), hence exactly
d.radical. The core supplement also preserves H's proper odd index.
Thus this branch supplies a genuine MSOddIndexRadical on the replacement;
no general inheritance of that hypothesis is asserted. The beyond-four
consumer combines this witness with the forced three-pair image and the
proved Thompson and Baumann normalizers. Both central covers remain intact.
The three-pair exclusion, original Sylow cases and distance-four residual
bounds remain required for the final large-distance theorem.

Source: Aschbacher--Smith C.1.31 (MS2)(a), printed p.135;
Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.8), Section 5 and characteristic reduction in Section 7,
printed pp.877--879, 912--927 and 932--933.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative
open Representation.BinaryAlternatingSixNaturalNormalizer
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace OriginalRadical
private theorem natural_injective : Function.Injective naturalLinearAction := by
  intro g k he
  apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
  apply LinearMap.ext
  intro v
  exact LinearEquiv.congr_fun he v

private theorem exists_projection_of_natural
    {M : Type*} [Group M] (N : Subgroup M) [N.Normal]
    (σ : Representation (ZMod 2) M Vector)
    (a : N →* alternatingGroup (Fin 6)) (ha : Function.Surjective a)
    (hcompat : ∀ (k : N) v, σ k v = BinaryPermutation.naturalRepresentation (Fin 6) (a k) v) :
    ∃ p : M →* Equiv.Perm (Fin 6), ∀ g v,
      σ g v =
        BinaryPermutation.naturalRepresentation (Fin 6) (p g) v := by
  let f : M →* (Vector ≃ₗ[ZMod 2] Vector) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) Vector).toMonoidHom.comp
      (σ).asGroupHom
  have he (k : N) :
      f k = naturalLinearAction (a k).val := by
    apply LinearEquiv.ext
    intro v
    exact hcompat k v
  have himage : (N).map f = alternatingLinearImage := by
    ext t
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨a ⟨k, hk⟩, (he ⟨k, hk⟩).symm⟩
    · rintro ⟨k, rfl⟩
      obtain ⟨l, hl⟩ := ha k
      refine ⟨l, l.property, ?_⟩
      rw [he, hl]
      rfl
  have hmem (g : M) : f g ∈ naturalLinearAction.range := by
    rw [← Representation.BinaryAlternatingSixNaturalNormalizer.normalizer, ← himage]
    apply Subgroup.le_normalizer_map f
    exact ⟨g, by rw [Subgroup.normalizer_eq_top]; trivial, rfl⟩
  let j := f.codRestrict naturalLinearAction.range hmem
  let p : M →* Equiv.Perm (Fin 6) :=
    (MonoidHom.ofInjective natural_injective).symm.toMonoidHom.comp j
  refine ⟨p, ?_⟩
  intro g v
  have hp : naturalLinearAction (p g) = f g :=
    MonoidHom.apply_ofInjective_symm natural_injective (j g)
  exact (LinearEquiv.congr_fun hp v).symm

universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "Q" => pCore 2 M
local notation "T" => R.subgroupOf (L ⊔ R)
local notation "S" => Equiv.Perm (Fin 6)

private theorem exists_ambient_projection :
    ∃ q : M →* S, ∀ g v,
      quotientAction h e hz hn (QuotientGroup.mk' Q g) v =
        BinaryPermutation.naturalRepresentation (Fin 6) (q g) v := by
  let := h.relative_normal
  let : (componentImage L R).Normal := Subgroup.Normal.map inferInstance
    (QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q)
  obtain ⟨q,hq⟩ := exists_projection_of_natural (componentImage L R)
    (quotientAction h e hz hn) (naturalCoordinates h e hz hn).groupEquiv.toMonoidHom
    (naturalCoordinates h e hz hn).groupEquiv.surjective
    ((initialSection h e hz).ambientAction_component (naturalCoordinates h e hz hn))
  exact ⟨q.comp (QuotientGroup.mk' Q),fun g v => hq _ v⟩

/-- Extend the chosen natural six-letter marking to the original ambient group. -/
def ambientProjection : M →* S := Classical.choose (exists_ambient_projection h e hz hn)

theorem ambientProjection_action (g : M) (v : Vector) :
    quotientAction h e hz hn (QuotientGroup.mk' Q g) v =
      BinaryPermutation.naturalRepresentation (Fin 6) (ambientProjection h e hz hn g) v :=
  Classical.choose_spec (exists_ambient_projection h e hz hn) g v

theorem ambientProjection_kernel : (ambientProjection h e hz hn).ker = Q := by
  have he : (BinaryPermutation.naturalRepresentation (Fin 6)).comp
      (ambientProjection h e hz hn) = (quotientAction h e hz hn).comp
        (QuotientGroup.mk' Q) := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    exact (ambientProjection_action h e hz hn g v).symm
  have hk : ((quotientAction h e hz hn).comp (QuotientGroup.mk' Q)).ker = Q := by
    rw [MonoidHom.ker_comp_of_injective _ _ (quotientAction_faithful h e hz hn),
      QuotientGroup.ker_mk']
  rwa [←he,MonoidHom.ker_comp_of_injective _ _
    (BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide))] at hk

theorem ambientProjection_restriction (d : Replacement L R) :
    (ambientProjection h e hz hn).comp d.overgroup.subtype =
      SourceReduction.projection h e hz hn d := by
  apply MonoidHom.ext
  intro g
  apply BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
  apply LinearMap.ext
  intro v
  exact (ambientProjection_action h e hz hn g v).symm.trans
    (SourceReduction.projection_action h e hz hn d g v)

/-- Surjectivity uses the already constructed full action on this same replacement. -/
theorem ambientProjection_surjective {d : Replacement L R}
    (s : FullSymmetricAction h e hz hn d) :
    Function.Surjective (ambientProjection h e hz hn) := by
  have hs : Function.Surjective (SourceReduction.projection h e hz hn d) := by
    simpa only [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] using
      s.surjective
  have hh := ambientProjection_restriction h e hz hn d
  rw [←hh] at hs
  exact Function.Surjective.of_comp hs

/-- The original ambient group is the replacement supplemented by its original two-core.
The original core is not asserted to lie in the replacement. -/
theorem overgroup_sup_core {d : Replacement L R}
    (s : FullSymmetricAction h e hz hn d) : d.overgroup ⊔ Q = ⊤ := by
  let q := ambientProjection h e hz hn
  have hm : d.overgroup.map q = ⊤ := by
    change d.overgroup.map (ambientProjection h e hz hn) = ⊤
    rw [←range_subtype d.overgroup,←MonoidHom.range_comp,ambientProjection_restriction]
    have hs := s.surjective
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hs
    exact MonoidHom.range_eq_top.mpr hs
  have hh := congrArg (Subgroup.comap q) hm
  rwa [comap_map_eq,ambientProjection_kernel,comap_top] at hh

private theorem image_card_eight {A : Type*} [Group A] [Finite A]
    (q : A →* S) (hq : Function.Surjective q) (T₀ : Subgroup A)
    (hp : IsPGroup 2 T₀) (hk : q.ker ≤ T₀)
    (hns : ¬ ∃ P : Sylow 2 A, (P : Subgroup A) = T₀)
    (hc : 8 ≤ Nat.card (T₀.map q)) : Nat.card (T₀.map q) = 8 := by
  open CFSG.Quasithin.ChapterB.Offenders.Six in
    obtain ⟨P,hP⟩ := (hp.map q).exists_le_sylow
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S P sylow
    have hPc : Nat.card (P : Subgroup S) = 16 := by
      have hh := congrArg (fun P : Sylow 2 S => Nat.card (P : Subgroup S)) hg
      change Nat.card ((P : Subgroup S).map (MulAut.conj g).toMonoidHom) =
        Nat.card sylowCarrier at hh
      rwa [card_map_of_injective (MulAut.conj g).injective,card_sylowCarrier] at hh
    have hup : Nat.card (T₀.map q) ≤ 16 := (card_le_of_le hP).trans_eq hPc
    have h16 : Nat.card (T₀.map q) ≠ 16 := by
      intro hh
      have hi := (T₀.map q).card_mul_index
      rw [hh,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin] at hi
      norm_num [Nat.factorial] at hi
      have hiT := T₀.index_map_eq hq hk
      have hodd : ¬ 2 ∣ T₀.index := by omega
      exact hns ⟨hp.toSylow hodd,rfl⟩
    obtain ⟨n,hn⟩ := (hp.map q).exists_card_eq
    have hn4 : n < 4 := by
      by_contra! hle
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hle
      have he : Nat.card (T₀.map q) = 16 := by omega
      exact h16 he
    have hn3 : 3 ≤ n := by
      by_contra! hlt
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show n ≤ 2 by omega)
      omega
    calc
      Nat.card (T₀.map q) = 2 ^ n := hn
      _ = 8 := by rw [show n = 3 by omega]; rfl

variable {h e hz hn}
/-- In the nonsylow branch the two radicals have the same literal original image. -/
theorem nonsylow_radical_image
    {h : SmallMSPair KnownSimple.IsKnownSimple L R}
    {e : CentralMarking L} {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (hns : ¬ ∃ P : Sylow 2 M, (P : Subgroup M) = T) :
    (T).map (ambientProjection h e hz hn) =
      d.radical.map (SourceReduction.projection h e hz hn d) := by
  let q := ambientProjection h e hz hn
  have hd : d.ambient.map q = d.radical.map (SourceReduction.projection h e hz hn d) := by
    rw [←ambientProjection_restriction,←map_map,
      map_subgroupOf_eq_of_le (show d.ambient ≤ d.overgroup from le_sup_right)]
  have hle : d.radical.map (SourceReduction.projection h e hz hn d) ≤ (T).map q := by
    rw [←hd]
    exact map_mono (map_subtype_le d.subgroup)
  have hc : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8 := by
    rcases nonsylow_radical_image_maximal_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hns with ⟨g,hg⟩ | ⟨g,hg⟩
    · rw [hg,card_map_of_injective (MulAut.conj g).injective]
      exact Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore_card
    · rw [hg,card_map_of_injective (MulAut.conj g).injective]
      exact CFSG.Quasithin.ChapterB.Offenders.Six.card_disjointTranspositions 3
  have hT := image_card_eight q
    (ambientProjection_surjective h e hz hn (fullSymmetricAction_knownSimple h e hz hn d hb))
    T h.relative_radical.isPGroup
    (by rw [ambientProjection_kernel]; exact h.relative_radical.twoCore_le) hns
    (hc ▸ card_le_of_le hle)
  exact (eq_of_le_of_card_ge hle (by rw [hT,hc])).symm

/-- The original nonsylow radical is the replacement radical supplemented
by the original two-core, with no splitting assertion. -/
theorem nonsylow_radical_sup_core
    {h : SmallMSPair KnownSimple.IsKnownSimple L R}
    {e : CentralMarking L} {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (hns : ¬ ∃ P : Sylow 2 M, (P : Subgroup M) = T) : d.ambient ⊔ Q = T := by
  have hh := nonsylow_radical_image (e := e) (hz := hz) (hn := hn) hb hns
  rw [←ambientProjection_restriction,←map_map,
    map_subgroupOf_eq_of_le (show d.ambient ≤ d.overgroup from le_sup_right)] at hh
  have hback := congrArg (Subgroup.comap (ambientProjection h e hz hn)) hh
  rw [comap_map_eq,comap_map_eq,ambientProjection_kernel,
    sup_eq_left.mpr h.relative_radical.twoCore_le] at hback
  exact hback.symm

/-- Intersecting the original radical with the actual replacement overgroup
recovers precisely the replacement radical. -/
theorem nonsylow_radical_restriction
    {h : SmallMSPair KnownSimple.IsKnownSimple L R}
    {e : CentralMarking L} {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (hns : ¬ ∃ P : Sylow 2 M, (P : Subgroup M) = T) :
    (T).subgroupOf d.overgroup = d.radical := by
  apply map_injective d.overgroup.subtype_injective
  rw [subgroupOf_map_subtype,
    map_subgroupOf_eq_of_le (show d.ambient ≤ d.overgroup from le_sup_right)]
  have he := nonsylow_radical_sup_core (e := e) (hz := hz) (hn := hn) hb hns
  apply le_antisymm
  · rintro x ⟨hx,hxN⟩
    have hx' : x ∈ d.ambient ⊔ Q := he.symm ▸ hx
    obtain ⟨a,ha,q,hq,rfl⟩ := mem_sup_of_normal_right.mp hx'
    have hqN : q ∈ d.overgroup :=
      (d.overgroup.mul_mem_cancel_left (show a ∈ d.overgroup from mem_sup_right ha)).mp hxN
    exact mul_mem ha (d.core_containment ⟨hqN,hq⟩)
  · exact le_inf (map_subtype_le d.subgroup) le_sup_right

private theorem core_restriction {A : Type*} [Group A] (H N : Subgroup A) [N.Normal] :
    (H.subgroupOf N).pCoreIn 2 = (H.pCoreIn 2).subgroupOf N := by
  have hn : H ≤ normalizer (H.pCoreIn 2 : Set A) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have he : (H ⊓ N).pCoreIn 2 = H.pCoreIn 2 ⊓ N := by
    apply le_antisymm
    · exact le_inf (pCoreIn_mono_of_normalizes inf_le_left
        ((le_inf H.le_normalizer le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf))
        ((pCoreIn_le 2 _).trans inf_le_right)
    · exact le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 H).to_le inf_le_left)
        (inf_le_inf (pCoreIn_le 2 H) le_rfl)
        (inf_le_left.trans ((le_inf hn le_normalizer_of_normal).trans
          inf_normalizer_le_normalizer_inf))
  rw [←inf_subgroupOf_right H N,pCoreIn_subgroupOf 2 (H ⊓ N) N inf_le_right,he,
    inf_subgroupOf_right]

/-- The original MS2(a) witness restricts to a genuine odd-index radical
witness in the nonsylow replacement. Its properness is proved, not assumed. -/
theorem nonsylow_odd_index_radical
    {h : SmallMSPair KnownSimple.IsKnownSimple L R}
    {e : CentralMarking L} {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (hns : ¬ ∃ P : Sylow 2 M, (P : Subgroup M) = T) :
    ChapterC.MSOddIndexRadical d.radical := by
  let := replacement_normal h d
  obtain ⟨H,hH,hodd,hcore⟩ := h.relative_radical
  have hTH : T ≤ H := by rw [←hcore]; exact map_subtype_le _
  have hcore' : (H.subgroupOf d.overgroup).pCoreIn 2 = d.radical := by
    rw [core_restriction,show H.pCoreIn 2 = T from hcore]
    exact nonsylow_radical_restriction (e := e) (hz := hz) (hn := hn) hb hns
  have hNH : d.overgroup ⊔ H = ⊤ := by
    apply top_unique
    rw [←overgroup_sup_core h e hz hn (fullSymmetricAction_knownSimple h e hz hn d hb)]
    exact sup_le_sup_left (h.relative_radical.twoCore_le.trans hTH) _
  have hi : (H.subgroupOf d.overgroup).index = H.index := by
    change H.relIndex d.overgroup = H.index
    rw [←relIndex_sup_of_normalizes_left d.overgroup H le_normalizer_of_normal,
      hNH,relIndex_top_right]
  refine ⟨H.subgroupOf d.overgroup,?_,hi.symm ▸ hodd,hcore'⟩
  apply lt_top_iff_ne_top.mpr
  intro ht
  have hh : H.index = 1 := by rw [←hi,ht,index_top]
  exact (ne_of_lt hH) (index_eq_one.mp hh)

/-- Beyond four this genuine MS2(a) witness accompanies the already forced
three-pair image and its actual Thompson and Baumann normalizers. -/
theorem nonsylow_four_lt_configuration
    {h : SmallMSPair KnownSimple.IsKnownSimple L R}
    {e : CentralMarking L} {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ P : Sylow 2 M, (P : Subgroup M) = T) :
    ChapterC.MSOddIndexRadical d.radical ∧
    (T).subgroupOf d.overgroup = d.radical ∧
    ∃ g : S,
      d.radical.map (SourceReduction.projection h e hz hn d) =
        (CFSG.Quasithin.ChapterB.Offenders.D 6).map (MulAut.conj g).toMonoidHom ∧
      normalizer (Stellmacher.elementaryAbelianMaxJ d.radical : Set d.overgroup) =
        normalizer (d.radical : Set d.overgroup) ∧
      normalizer (ChapterB.baumann d.radical : Set d.overgroup) =
        normalizer (d.radical : Set d.overgroup) := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨g,hg,_,hJ,hB⟩ := nonsylow_four_lt_thompson_configuration_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  exact ⟨nonsylow_odd_index_radical (e := e) (hz := hz) (hn := hn) hb2 hns,
    nonsylow_radical_restriction (e := e) (hz := hz) (hn := hn) hb2 hns,g,hg,hJ,hB⟩

end OriginalRadical
end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
