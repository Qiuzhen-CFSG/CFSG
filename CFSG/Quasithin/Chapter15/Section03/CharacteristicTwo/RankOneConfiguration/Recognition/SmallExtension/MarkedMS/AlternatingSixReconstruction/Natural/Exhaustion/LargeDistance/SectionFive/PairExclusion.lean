module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowRestriction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.MinimalParabolic.IndexThree
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.ShortSeedPropagation
public import Theory.GroupTheory.SmallIndexSolvable

/-!
# Excluding the two-transposition replacement image

Suppose the literal replacement radical maps onto two disjoint
transpositions in the canonical S₆ quotient. The overlapping three-cycle
(014), together with this plane, has order twelve. Its pullback has the
actual replacement radical as a Sylow subgroup of index three. The plane's
normalizer and this three-cycle generate S₆; lifting through the retained
two-core shows that every characteristic subgroup normal in this local
pullback would be normal in the replacement overgroup, contrary to MS3.

The proved index-three pushing-up theorem now makes the local two-residual
a short block. Its image is the same noncentral cubic, and the ambient
two-core normalizes it. Short-seed propagation therefore makes the original
replacement component short. The whole-core radius argument then forces
critical distance two on the original graph.

Both moved covers and all central attachments are retained. No Sylow
hypothesis on the original radical is added. The concluding consumers
reduce every order-four image, and the index-four original Sylow restriction,
to the still-open mixed-plane branch. The larger Sylow images and the
distance-four residual estimates remain with the large-distance assembly.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the rank-one argument of (5.1), printed pp.912--914; the local
pushing-up and short-seed propagation are Aschbacher--Smith C.1.29 and
C.1.21, printed pp.133 and128--129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.PairExclusion
local notation "S" => Equiv.Perm (Fin 6)
private abbrev A : Subgroup S := disjointTranspositions 6 2
private def c : S := Equiv.swap 0 1 * Equiv.swap 1 4
private def x : S := Equiv.swap 0 2 * Equiv.swap 1 3

private theorem c_order : orderOf c = 3 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

private theorem pair_normalizes : A ≤ normalizer (zpowers c : Set S) := by
  intro g hg
  obtain ⟨i,rfl⟩ := (mem_disjointTranspositions_iff (2 : Fin 4) g).mp hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  change zpowers ((MulAut.conj (initialWords 2 i)) c) = zpowers c
  have hc : ∀ i : Fin 4, (MulAut.conj (initialWords 2 i)) c = c ∨
      (MulAut.conj (initialWords 2 i)) c = c⁻¹ := by decide +kernel
  rcases hc i with hi | hi <;> rw [hi]
  exact zpowers_inv

private theorem local_card : Nat.card (zpowers c ⊔ A : Subgroup S) = 12 := by
  have hA : Nat.card A = 4 := card_disjointTranspositions (2 : Fin 4)
  rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ pair_normalizes
    (disjoint_of_coprime_natCard (by
      rw [Nat.card_zpowers,c_order,hA]; decide)), Nat.card_zpowers,c_order,hA]

private theorem normalizer_generate : normalizer (A : Set S) ⊔ zpowers c = ⊤ := by
  let N := normalizer (A : Set S) ⊔ zpowers c
  have h01 : Equiv.swap (0 : Fin 6) 1 ∈ N :=
    (show normalizer (A : Set S) ≤ N from le_sup_left)
      (A.le_normalizer ((mem_disjointTranspositions_iff (2 : Fin 4) _).mpr ⟨1,rfl⟩))
  have h23 : Equiv.swap (2 : Fin 6) 3 ∈ N :=
    (show normalizer (A : Set S) ≤ N from le_sup_left)
      (A.le_normalizer ((mem_disjointTranspositions_iff (2 : Fin 4) _).mpr ⟨2,rfl⟩))
  have hnorm (g : S) (hg : ∀ i : Fin 4, ∃ j : Fin 4,
      initialWords 2 j = g * initialWords 2 i * g⁻¹) : g ∈ N := by
    apply (show normalizer (A : Set S) ≤ N from le_sup_left)
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨a,ha,rfl⟩
      obtain ⟨i,rfl⟩ := (mem_disjointTranspositions_iff (2 : Fin 4) a).mp ha
      exact (mem_disjointTranspositions_iff (2 : Fin 4) _).mpr (hg i)
    · rw [card_map_of_injective (MulAut.conj g).injective]
  have hx : x ∈ N := hnorm x (by decide +kernel)
  have h45 : Equiv.swap (4 : Fin 6) 5 ∈ N := hnorm _ (by decide +kernel)
  have hc : c ∈ N := mem_sup_right (mem_zpowers c)
  have h14 : Equiv.swap (1 : Fin 6) 4 ∈ N := by
    have he : Equiv.swap (0 : Fin 6) 1 * c = Equiv.swap (1 : Fin 6) 4 := by decide +kernel
    rw [←he]; exact N.mul_mem h01 hc
  have h34 : Equiv.swap (3 : Fin 6) 4 ∈ N := by
    have he : x * Equiv.swap (1 : Fin 6) 4 * x⁻¹ = Equiv.swap (3 : Fin 6) 4 := by decide +kernel
    rw [←he]; exact N.mul_mem (N.mul_mem hx h14) (N.inv_mem hx)
  have h12 : Equiv.swap (1 : Fin 6) 2 ∈ N := by
    have he : Equiv.swap (1 : Fin 6) 4 * (Equiv.swap 3 4 * Equiv.swap 2 3 * Equiv.swap 3 4) *
        Equiv.swap 1 4 = Equiv.swap (1 : Fin 6) 2 := by decide +kernel
    rw [←he]
    exact N.mul_mem (N.mul_mem h14 (N.mul_mem (N.mul_mem h34 h23) h34)) h14
  apply top_unique
  rw [←Subgroup.closure_eq_top_of_mclosure_eq_top (Equiv.Perm.mclosure_swap_castSucc_succ 5)]
  apply (Subgroup.closure_le _).mpr
  rintro z ⟨i,rfl⟩
  fin_cases i
  · exact h01
  · exact h12
  · exact h23
  · exact h34
  · exact h45

private theorem characteristic_map_equiv {H K : Type*} [Group H] [Group K]
    (f : H ≃* K) (C : Subgroup H) [C.Characteristic] :
    (C.map f.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a z hz
  obtain ⟨y,hy,rfl⟩ := hz
  let b : MulAut H := f.trans (a.trans f.symm)
  exact ⟨b y,(characteristic_iff_le_comap.mp inferInstance b) hy,f.apply_symm_apply _⟩

private theorem local_characteristic {H : Type*} [Group H]
    (R F : Subgroup H) (hRF : R ≤ F) (hR : MSCharacteristicCondition R)
    (hgen : F ⊔ normalizer (R : Set H) = ⊤)
    (W : Sylow 2 F) (hW : (W : Subgroup F) = R.subgroupOf F) :
    MSCharacteristicCondition (W : Subgroup F) := by
  let f : W ≃* R := (MulEquiv.subgroupCongr hW).trans (subgroupOfEquivOfLe hRF)
  intro C hC hne hn
  let := hC
  let D := C.map f.toMonoidHom
  let : D.Characteristic := characteristic_map_equiv f C
  have he : D.map R.subtype = (C.map (W : Subgroup F).subtype).map F.subtype := by
    rw [map_map,map_map]
    congr 1
  have hnF : F ≤ normalizer (D.map R.subtype : Set H) := by
    rw [he]
    apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp
    rw [subgroupOf_map_subtype_eq]
    exact hn
  have hnD : (D.map R.subtype).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    rw [←hgen]
    exact sup_le hnF (normalizer_le_normalizer_characteristic_image R D)
  have hD := hR.eq_bot_of_normal D hnD
  exact hne ((map_eq_bot_iff_of_injective C f.injective).mp hD)

private theorem conjugate_local (g : S) :
    let B := A.map (MulAut.conj g).toMonoidHom
    let z := (MulAut.conj g) c
    orderOf z = 3 ∧ B ≤ normalizer (zpowers z : Set S) ∧
      Nat.card (zpowers z ⊔ B : Subgroup S) = 12 ∧
      normalizer (B : Set S) ⊔ zpowers z = ⊤ := by
  dsimp only
  have hc : (zpowers c).map (MulAut.conj g).toMonoidHom = zpowers ((MulAut.conj g) c) :=
    MonoidHom.map_zpowers _ _
  refine ⟨(MulAut.conj g).orderOf_eq c |>.trans c_order,?_,?_,?_⟩
  · rw [←hc]
    exact (map_mono pair_normalizes).trans (le_normalizer_map _)
  · rw [←hc,←Subgroup.map_sup,card_map_of_injective (MulAut.conj g).injective]
    exact local_card
  · rw [←hc,←map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective,
      ←Subgroup.map_sup,normalizer_generate,map_top_of_surjective _ (MulAut.conj g).surjective]

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

private theorem pair_local_group (hb : 2 < replacementDistance h d) (g : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      A.map (MulAut.conj g).toMonoidHom) :
    ∃ (F : Subgroup d.overgroup) (W : Sylow 2 F) (z : S),
      d.radical ≤ F ∧ pCore 2 d.overgroup ≤ F ∧
      (W : Subgroup F) = d.radical.subgroupOf F ∧ (W : Subgroup F).index = 3 ∧
      MSCharacteristicCondition (W : Subgroup F) ∧
      Stellmacher.SectionTwo.Hypotheses F ∧
      orderOf z = 3 ∧
      ((pResidual 2 F).map F.subtype).map (SourceReduction.projection h e hz hn d) = zpowers z := by
  let π := SourceReduction.projection h e hz hn d
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hπ : Function.Surjective π := by
    simpa only [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] using s.surjective
  have hk : π.ker = pCore 2 d.overgroup := SourceReduction.projection_kernel h e hz hn d
  let B := d.radical.map π
  let z := (MulAut.conj g) c
  have hB : Nat.card B = 4 := by
    change Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 4
    rw [him,card_map_of_injective (MulAut.conj g).injective]
    exact card_disjointTranspositions (2 : Fin 4)
  obtain ⟨hz3,hnB,hcard,hgen⟩ := conjugate_local g
  change orderOf z = 3 at hz3
  change A.map (MulAut.conj g).toMonoidHom ≤ normalizer (zpowers z : Set S) at hnB
  rw [←him] at hnB hcard hgen
  let J := zpowers z ⊔ B
  let F := J.comap π
  have hRF : d.radical ≤ F := fun r hr => mem_sup_right (mem_map_of_mem π hr)
  have hQF : pCore 2 d.overgroup ≤ F := (replacement_core_le_radical h d).trans hRF
  have hF : F.map π = J := map_comap_eq_self_of_surjective hπ J
  have hindex : (d.radical.subgroupOf F).index = 3 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup S) B J bot_le le_sup_right
    rw [relIndex_bot_left,relIndex_bot_left,hB,hcard] at hh
    have hi := relIndex_map_map π d.radical F
    rw [hk,sup_eq_left.mpr (replacement_core_le_radical h d),sup_eq_left.mpr hQF,hF] at hi
    change d.radical.relIndex F = 3
    change B.relIndex J = d.radical.relIndex F at hi
    rw [←hi]
    omega
  let W := (replacement_radical_isPGroup h d).comap_subtype.toSylow
    (show ¬2 ∣ (d.radical.subgroupOf F).index by rw [hindex]; decide)
  have hgenF : F ⊔ normalizer (d.radical : Set d.overgroup) = ⊤ := by
    have hn : normalizer (d.radical : Set d.overgroup) =
        (normalizer (B : Set S)).comap π := by
      rw [comap_normalizer_eq_of_surjective _ hπ,comap_map_eq,hk,
        sup_eq_left.mpr (replacement_core_le_radical h d)]
    have hm : (F ⊔ normalizer (d.radical : Set d.overgroup)).map π = ⊤ := by
      rw [Subgroup.map_sup,hF,hn,map_comap_eq_self_of_surjective hπ]
      apply top_unique
      rw [←hgen]
      exact sup_le le_sup_right (le_sup_left.trans le_sup_left)
    have hh := congrArg (Subgroup.comap π) hm
    rwa [comap_map_eq,hk,sup_eq_left.mpr (hQF.trans le_sup_left),comap_top] at hh
  have hchar := local_characteristic d.radical F hRF (replacement_characteristic h d) hgenF W rfl
  have hsolv : Group.IsSolvable F := by
    let : Group.IsNilpotent (W : Subgroup F) := W.isPGroup'.isNilpotent
    exact (W : Subgroup F).isSolvable_of_index_le_four (by change (d.radical.subgroupOf F).index ≤ 4; omega)
  let f := π.subgroupComap J
  have hf : Function.Surjective f := π.subgroupComap_surjective_of_surjective J hπ
  have heven : Even (Nat.card F) := by
    apply even_iff_two_dvd.mpr
    have hh := card_dvd_of_surjective f hf
    change Nat.card J ∣ Nat.card F at hh
    rw [hcard] at hh
    exact (by decide : 2 ∣ 12).trans hh
  have hself := centralizer_pCore_le_of_pCore_le F (replacement_self_centralizing h d) hQF
  refine ⟨F,W,z,hRF,hQF,rfl,hindex,hchar,⟨hsolv,heven,hself⟩,hz3,?_⟩
  let C := (zpowers z).subgroupOf J
  let D := B.subgroupOf J
  let : C.Normal := normal_subgroupOf_of_le_normalizer (sup_le (zpowers z).le_normalizer hnB)
  have hC : IsPPerfect 2 C := by
    apply (pResidual_eq_top_iff 2 C).mp
    apply top_unique
    intro t _
    apply mem_pResidual_of_orderOf_coprime
    have hc : Nat.card C = 3 := (Nat.card_congr (subgroupOfEquivOfLe
      (show zpowers z ≤ J from le_sup_left)).toEquiv).trans (by rw [Nat.card_zpowers,hz3])
    exact (show Nat.Coprime 2 (Nat.card C) by rw [hc]; decide).of_dvd_right (orderOf_dvd_natCard t)
  have hD : IsPGroup 2 D := ((replacement_radical_isPGroup h d).map π).comap_subtype
  have hCD : C ⊔ D = ⊤ := by
    rw [←subgroupOf_sup (show zpowers z ≤ J from le_sup_left) (show B ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hres : pResidual 2 J = C := pResidual_eq_of_isPPerfect_sup C D hC hD hCD
  have he : π.comp F.subtype = J.subtype.comp f := rfl
  rw [map_map,he,←map_map,map_pResidual_of_surjective 2 f hf,hres]
  exact map_subgroupOf_eq_of_le (show zpowers z ≤ J from le_sup_left)

/-- A two-transposition replacement image forces shortness of the actual
component and hence critical distance two, with either moved cover. -/
theorem distance_eq_two_of_pair_image_knownSimple (g : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      (disjointTranspositions 6 2).map (MulAut.conj g).toMonoidHom) :
    replacementDistance h d = 2 := by
  by_cases hb : 2 < replacementDistance h d
  · let s := fullSymmetricAction_knownSimple h e hz hn d hb
    obtain ⟨F,W,z,hRF,hQF,hW,hi,hchar,hF,hz3,himage⟩ := pair_local_group hb g him
    have hblock := (RankOne.Solvable.MinimalParabolic.index_three_residual hF W hi hchar).2.2.2.1
    let K := (pResidual 2 F).map F.subtype
    have hK : IsShort K := hblock.short.of_mulEquiv
      ((pResidual 2 F).equivMapOfInjective F.subtype F.subtype_injective)
    have hKL : K ≤ replacementComponent d := by
      exact (map_pResidual_le 2 F.subtype).trans_eq (replacement_residual h d)
    let := replacementComponent_normal h d
    let := h.relative_core_quasisimple e
    let f := subgroupOfEquivOfLe
      (show L.subgroupOf (L ⊔ R) ≤ d.overgroup from le_sup_left)
    let : IsQuasisimple ((replacementComponent d) ⧸ pCore 2 (replacementComponent d)) :=
      IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ f (pCore_map_iso 2 f)).symm
    have hcomp : (replacementComponent d).IsCComponent :=
      h.component.subgroupOf (show L.subgroupOf (L ⊔ R) ≤ d.overgroup from le_sup_left)
    have hp : IsPPerfect 2 (replacementComponent d) := by
      have he : pResidual 2 d.overgroup = replacementComponent d := replacement_residual h d
      rw [←he]
      exact isPPerfect_pResidual 2
    have hf := generalizedFitting_eq_pCore_of_selfCentralizing 2
      (subnormal_core_selfCentralizing (replacement_self_centralizing h d)
        (replacementComponent d) hcomp.subnormal)
    have hQK : pCore 2 d.overgroup ≤ normalizer (K : Set d.overgroup) :=
      hQF.trans (F.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image F (pResidual 2 F)))
    have hnc := RankOne.SymmetricSix.cubic_not_central_in_component
      (replacementComponent d) K hcomp.subnormal hKL s.projection
      s.projection_kernel.symm.le s.component_image z hz3 (by
        rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s])
    exact distance_eq_two_of_short_component (e := e) (hz := hz) (hn := hn)
      (RankOne.GlaubermanArgument.isBlock_of_short_seed K (replacementComponent d)
        hKL hK hcomp.subnormal hp hf hQK hnc).short
  · exact replacementDistance_eq_two h d (Nat.le_of_not_gt hb)

/-- The only order-four radical image remaining above distance two is the
mixed plane. The two-transposition alternative is now excluded. -/
theorem four_image_mixed_knownSimple (hb : 2 < replacementDistance h d)
    (hfour : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 4) :
    ∃ g : S, d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨_,g,hg | hg⟩ := SylowRestriction.four_image_models_knownSimple hb hfour
  · have he := distance_eq_two_of_pair_image_knownSimple g hg
    omega
  · exact ⟨g,hg⟩

/-- At index four in the restricted original Sylow, the literal replacement
image is necessarily mixed; the original and replacement radicals stay distinct. -/
theorem sylow_index_four_mixed_knownSimple (hb : 2 < replacementDistance h d)
    (P : Sylow 2 (L ⊔ R : Subgroup G)) (hP : (P : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    (hi : d.radical.relIndex ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup) = 4) :
    ∃ g : S, d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj g).toMonoidHom := by
  have hf := (SylowRestriction.original_sylow_restriction_knownSimple
    (e := e) (hz := hz) (hn := hn) hb P hP).2.2.1
  rw [hi] at hf
  exact four_image_mixed_knownSimple hb (by omega)

/-- The canonical minimum replacement also has distance two in the excluded
two-transposition branch, with its original quotient map unchanged. -/
theorem original_pair_replacement_distance_two_knownSimple (g : S)
    (him : (replacement h).radical.map (SourceReduction.projection h e hz hn (replacement h)) =
      (disjointTranspositions 6 2).map (MulAut.conj g).toMonoidHom) :
    replacementDistance h (replacement h) = 2 :=
  distance_eq_two_of_pair_image_knownSimple g him

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.PairExclusion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
