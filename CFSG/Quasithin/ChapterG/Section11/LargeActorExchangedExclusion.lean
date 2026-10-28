module
public import CFSG.Quasithin.ChapterG.Section11.CorrectedReduction
public import CFSG.Quasithin.ChapterG.Section10.Components.ExchangedFaithfulPair
public import Theory.Representation.NormalComponentConstituents.ElementaryKernel
public import Theory.Representation.NormalComponentConstituents.CenterlessQuotient
public import Theory.GroupTheory.GeneralizedFitting.ElementarySylowOrbit
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryRank

/-!
# Excluding exchanged natural constituents for a large elementary actor

The half-degree bound leaves only a natural S₆ constituent in degree four,
with whole degree eight and actor rank four. Its literal perfect normal
image is A₆. If the component-orbit kernel is central, ambient faithful
irreducibility kills it, and the actor embeds in Aut(A₆), contradicting
the elementary rank-three bound. If the kernel is noncentral, normality of
the elementary actor in the original Sylow makes the component's Sylow
subgroups elementary. This passes through the actual two-component orbit
and its quotient onto A₆, contradicting an explicit element of order four.

The result retains the original action, form, point, marked space, actor
and component. It closes the exchanged remainder of CorrectedReduction
under the stated bound; whole-component recognition is still required.
The literal rank-three flag application is in
Chapter14/Section04/CaseOneHS/LocalStructure/SourceAction/ExchangedNatural.
Source: Aschbacher--Smith G.10.15, G.11.6 and 14.3.24,
printed pp.362--366,1000. The rank-four faithful exclusion adapts the
checked calculation in Chapter14's ComponentCatalogueLargeActorDegreesNatural.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11.ExchangedRecognition

variable {D U : Type*} [Group D] [Finite D] [AddCommGroup U]
  [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {ρ : Representation (ZMod 2) D U} {B : LinearMap.BilinForm (ZMod 2) U}
  {v : U} {W : Submodule (ZMod 2) U} {X : Subgroup D}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

private theorem exchanged_conjugation_injective
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (hi : IsIrreducible ρ)
    {L : Subgroup D} (hL : IsComponent D L)
    {I : Submodule (ZMod 2) U}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤)
      X I)
    (hgen : Homogeneous.orbitSpan ρ X I = ⊤) :
    letI := componentOrbit_top_normal L
    Function.Injective (MulAut.conjNormal.comp X.subtype :
      X →* MulAut (componentOrbit L ⊤)) := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful
    hi H hL.componentOrbit_top_ne_bot
  let f : X →* MulAut H := MulAut.conjNormal.comp X.subtype
  apply (injective_iff_map_eq_one f).mpr
  intro z hz
  have hzi : (z : D)⁻¹ = z := inv_eq_iff_mul_eq_one.mpr (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (z : D) z.property)
  have hzI : (z : D) ∈ subspaceStabilizer ρ I := by
    by_contra hn
    have hm : I.map (ρ (z : D)⁻¹) ≠ I := by
      rw [hzi]
      exact fun he => hn ((subspace_map_eq_iff ρ I _).mp he)
    have ho := hI.conjugation_not_inner ρ hfix z hm
    apply ho
    change f z ∈ MulAut.innerSubgroup H
    rw [hz]
    exact (MulAut.innerSubgroup H).one_mem
  have hzc : (z : D) ∈ centralizer (H : Set D) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer]
    exact hz
  have he := h.spanning_constituent_stabilizer_centralizer_eq_bot hI.isIrrPlus hgen
  apply Subtype.ext
  apply mem_bot.mp
  rw [← he]
  exact ⟨⟨hzI,z.property⟩,hzc⟩

omit [Finite D] [FiniteDimensional (ZMod 2) U] [IsElementaryAbelian 2 X] in
private theorem natural_six_orbit_quotient
    (H : Subgroup D) [H.Normal] [Group.IsPerfect H]
    (I : Submodule (ZMod 2) U) (hH : H ≤ subspaceStabilizer ρ I)
    (hne : I ≠ ⊥) (hfix : fixedSpace ρ H = ⊥)
    (hm : ChapterG.Section06.HasModelOn
      (kerRepresentation (ChapterG.Section09.constituentAction ρ H
        (X ⊓ subspaceStabilizer ρ I) I hH inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin 6))) :
    ∃ p : H →* alternatingGroup (Fin 6), Function.Surjective p ∧
      ∀ a : H, p a = 1 ↔ (invariantSubspace ρ H I hH).toRepresentation a = 1 := by
  let Y := X ⊓ subspaceStabilizer ρ I
  let P := H ⊔ Y
  let σ := ChapterG.Section09.constituentAction ρ H Y I hH inf_le_right
  let q := QuotientGroup.mk' σ.ker
  let ι := Subgroup.inclusion (show H ≤ P from le_sup_left)
  let r := q.comp ι
  have hrange : r.range = (H.subgroupOf P).map q := by
    rw [MonoidHom.range_comp]
    congr 1
    ext a
    constructor
    · rintro ⟨b,rfl⟩; exact b.property
    · intro ha; exact ⟨⟨a,ha⟩,rfl⟩
  let : r.range.Normal := hrange ▸ Subgroup.Normal.map inferInstance q
    (QuotientGroup.mk'_surjective _)
  obtain ⟨e,_,_⟩ := hm
  let d := Subgroup.topEquiv.symm.trans e
  let j := d.toMonoidHom.comp r
  have hj (a : H) : j a = 1 ↔ (invariantSubspace ρ H I hH).toRepresentation a = 1 := by
    constructor
    · intro ha
      have hq : q (ι a) = 1 := d.injective (by
        change d (q (ι a)) = 1 at ha
        simpa only [map_one] using ha)
      exact (QuotientGroup.eq_one_iff _).mp hq
    · intro ha
      change d (q (ι a)) = 1
      have hq : q (ι a) = 1 := (QuotientGroup.eq_one_iff (ι a)).mpr ha
      rw [hq,map_one]
  have hjrange : j.range = r.range.map d.toMonoidHom := MonoidHom.range_comp _ _
  let : j.range.Normal := hjrange ▸ Subgroup.Normal.map inferInstance d.toMonoidHom d.surjective
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  have hjne : j.range ≠ ⊥ := by
    intro hz
    apply hne
    apply bot_unique
    rw [← hfix]
    intro u hu a
    have ha := (hj a).mp (mem_bot.mp (hz ▸ (show j a ∈ j.range from ⟨a,rfl⟩)))
    exact congrArg (fun f : Module.End (ZMod 2) I => (f ⟨u,hu⟩ : U)) ha
  let : Nontrivial j.range := j.range.nontrivial_iff_ne_bot.mpr hjne
  have hA : j.range = alternatingGroup (Fin 6) :=
    Equiv.Perm.eq_alternatingGroup_of_perfect_normal (by simp) j.range
  let p := (MulEquiv.subgroupCongr hA).toMonoidHom.comp j.rangeRestrict
  refine ⟨p, (MulEquiv.subgroupCongr hA).surjective.comp j.rangeRestrict_surjective, ?_⟩
  intro a
  exact (Subtype.ext_iff).trans (hj a)

private theorem alternating_six_not_elementary_sylow
    (h : ∀ S : Sylow 2 (alternatingGroup (Fin 6)), IsElementaryAbelian 2 S) : False := by
  let a : alternatingGroup (Fin 6) :=
    ⟨Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 4 5, by decide⟩
  have ha : orderOf a = 4 :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by decide +kernel) (by decide +kernel)
  have hp : IsPGroup 2 (zpowers a) := IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers,ha]; norm_num)
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  let := h S
  have ha2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) a (hS (mem_zpowers a))
  have hd := orderOf_dvd_of_pow_eq_one ha2
  rw [ha] at hd
  norm_num at hd

private theorem no_exchanged_six_of_actor_four
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable D) {L : Subgroup D} (hL : IsComponent D L)
    (hm : ⁅L,X⁆ ≠ ⊥) {I : Submodule (ZMod 2) U}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I)
    (hv : v ∉ I) (hgeo : ChapterG.Section10.ExchangedConstituentGeometry ρ B v W X I)
    (hfour : finrank (ZMod 2) (Additive X) = 4)
    (hmodel : ChapterG.Section06.HasModelOn
      (kerRepresentation (ChapterG.Section09.constituentAction ρ
        (componentOrbit L ⊤) (X ⊓ subspaceStabilizer ρ I) I hI.invariant inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin 6))) : False := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  have hi := h.irreducible_of_not_solvable hn
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ h.faithful hi H
    hL.componentOrbit_top_ne_bot
  obtain ⟨p,hp,hkill⟩ := natural_six_orbit_quotient H I hI.invariant
    (hI.isIrrPlus.ne_bot ρ) hfix hmodel
  have hcenter : center H = ⊥ := center_eq_bot_of_constituent_quotient ρ h.faithful hi
    H I hI.invariant (hI.isIrrPlus.ne_bot ρ) p hp
    (alternatingGroup.center_eq_bot (by simp)) (fun a ha => (hkill a).mp ha)
  let R := invariantSubspace ρ H I hI.invariant
  have hnoncentral : ¬ R.toRepresentation.asGroupHom.ker ≤ center H := by
    intro hk
    have hj : Function.Injective p := (injective_iff_map_eq_one p).mpr (by
      intro a ha
      apply mem_bot.mp
      rw [← hcenter]
      exact hk (show a ∈ R.toRepresentation.asGroupHom.ker from Units.ext ((hkill a).mp ha)))
    let e := MulEquiv.ofBijective p ⟨hj,hp⟩
    obtain ⟨x,_,hc,_,_⟩ := exchanged_lowRank_pair h cover hw hS hn hL hm hI hgeo
    have hgen : Homogeneous.orbitSpan ρ X I = ⊤ := by
      apply top_unique
      rw [← hc.sup_eq_top]
      exact sup_le (Homogeneous.le_orbitSpan _ _ I) (le_iSup (fun y : X => I.map (ρ y)) x)
    let j : X →* MulAut (alternatingGroup (Fin 6)) :=
      (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal.comp X.subtype)
    have hj : Function.Injective j := (MulAut.congr e).injective.comp
      (exchanged_conjugation_injective h hi hL hI hgen)
    let : IsElementaryAbelian 2 j.range := IsElementaryAbelian.of_injective
      (MonoidHom.ofInjective hj).symm.toMonoidHom (MonoidHom.ofInjective hj).symm.injective
    have hb := AlternatingSix.ShadowLocal.elementary_card_le_eight j.range
    rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv,
      Nat.card_congr Additive.ofMul, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod,hfour] at hb
    norm_num at hb
  obtain ⟨S,_,_,hXS⟩ := hS
  have hnX : (S : Subgroup D) ≤ normalizer (X : Set D) :=
    (normal_subgroupOf_iff_le_normalizer ‹X ≤ (S : Subgroup D)›).mp hXS
  obtain ⟨x,_,hsep⟩ := h.exchanged_pair_separates hn hL hm S hnX
    (cover.some.component_normalizer_index_le_two hL) hI hv
  let N := R.toRepresentation.asGroupHom.ker
  let : IsElementaryAbelian 2 ((((S : Subgroup D).subgroupOf H) ⊓ N) : Subgroup H) :=
    ExchangedKernel.kernel_sylow_elementary ρ H X S hnX R x hsep
  have hcomp (P : Sylow 2 L) : IsElementaryAbelian 2 P :=
    ExchangedKernel.component_sylow_elementary_of_kernel hL S N hnoncentral P
  have hind : (normalizer (L : Set D)).index = 2 := by
    have hb := cover.some.component_normalizer_index_le_two hL
    have hpos := (normalizer (L : Set D)).index_ne_zero_of_finite
    have h1 : (normalizer (L : Set D)).index ≠ 1 := by
      intro he
      let : L.Normal := normalizer_eq_top_iff.mp (index_eq_one.mp he)
      have heH : H = L := le_antisymm
        (iSup_conjugates_le_of_le_normalizer L ⊤ L le_rfl (by rw [normalizer_eq_top]))
        (le_componentOrbit L ⊤)
      let : IsQuasisimple H := heH.symm ▸ hL.2
      rcases IsQuasisimple.normal_le_center_or_eq_top N with hc | ht
      · exact hnoncentral hc
      · have hle : I ≤ fixedSpace ρ H := by
          intro u hu a
          have ha : R.toRepresentation.asGroupHom a = 1 := MonoidHom.mem_ker.mp (by
            change a ∈ N
            rw [ht]
            exact mem_top a)
          exact congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2) I => (f.val ⟨u,hu⟩ : U)) ha
        exact hI.isIrrPlus.ne_bot ρ (bot_unique (hfix ▸ hle))
    omega
  exact alternating_six_not_elementary_sylow
    (ExchangedOrbit.elementary_sylow_image p hp (ExchangedOrbit.orbit_sylow_elementary hL hind hcomp))

/-- Under the half-degree actor bound, every remaining exchanged natural
constituent is impossible. The original whole-component hypothesis remains
explicit; this theorem does not assert its classification. -/
theorem whole_of_remaining_of_large
    (h : ChapterG.Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (ChapterG.Section09.SQTKCover KnownSimple.IsKnownSimple D))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable D)
    (hlarge : finrank (ZMod 2) U ≤ 2 * finrank (ZMod 2) (Additive X))
    (hrem : RemainingComponentModels ρ B v W X) :
    ∃ L : Subgroup D, IsComponent D L ∧ ⁅L,X⁆ ≠ ⊥ ∧
      ChapterG.Section10.ComponentOrthogonalData ρ B L ∧
      ChapterG.Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X L
        (componentOrbit L ⊤) (finrank (ZMod 2) (Additive X)) := by
  obtain ⟨L,hL,hm,horth,hwhole | hex⟩ := hrem
  · exact ⟨L,hL,hm,horth,hwhole⟩
  · obtain ⟨I,hI,hv,hgeo,_,_,_,_,n,hnl,hnu,_,hmodel⟩ := hex
    rcases exchanged_natural_ranks h cover hw hS hn hL hm hI hgeo n hnl hnu hmodel with
      h5 | h6 | h8
    · obtain ⟨_,_,hd,hr,_⟩ := h5
      omega
    · obtain ⟨rfl,_,hd,hr⟩ := h6
      have hfour : finrank (ZMod 2) (Additive X) = 4 := by omega
      exact (no_exchanged_six_of_actor_four h cover hw hS hn hL hm hI hv hgeo hfour hmodel).elim
    · obtain ⟨_,_,hd,hr,_⟩ := h8
      omega

end CFSG.Quasithin.ChapterG.Section11.ExchangedRecognition
