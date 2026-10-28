module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.Core
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.InvolutionCentralizerControl
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.Thompson

/-!
# The actual partner section kernel centralizes the fixed module

An element acting trivially on V/E cannot exchange the two supports.
In the original intersection M∩Mc it normalizes the Thompson image, so
it normalizes each order-two factor intersection. It centralizes those
involutions, and trivial action on V/E then forces trivial action on their
displacement planes. Those planes generate E.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker

private theorem support_fixer_of_fixed_displacement
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (F : Factor ρ) (B : Subgroup D)
    (hBF : B≤F.actor) (hcB : Nat.card B=2)
    (hq : cubicRatio ρ=2) (hd : Module.finrank (ZMod 2) F.Space=4)
    (g:D) (hgB : g∈normalizer (B:Set D))
    (hmove : ∀v,ρ g v-v∈fixedSpace ρ B) :
    ∀z∈F.space⊓fixedSpace ρ B,ρ g z=z := by
  obtain ⟨t,hto⟩ := exists_prime_orderOf_dvd_card' (G:=B) 2 (by rw [hcB])
  have ht : orderOf (t:D)=2 := by simpa only [Subgroup.orderOf_coe] using hto
  have ht2 : (t:D)^2=1 := ht ▸ pow_orderOf_eq_one (t:D)
  have heB : zpowers (t:D)=B := eq_of_le_of_card_ge (zpowers_le.mpr t.property) (by
    rw [Nat.card_zpowers,ht,hcB])
  have hc : (t:D)*g=g*(t:D) := normalizer_le_centralizer_of_card_two B hcB hgB t t.property
  let R := LinearMap.range (ρ (t:D)-LinearMap.id)
  have hR : R≤F.space⊓fixedSpace ρ B := by
    rintro _ ⟨v,rfl⟩
    constructor
    · exact F.embedding.moved_le_range (Submodule.subset_span ⟨t,hBF t.property,v,trivial,rfl⟩)
    · have hh : ρ (t:D) v-v∈fixedSpace ρ (zpowers (t:D)) :=
        (mem_fixedSpace_zpowers_iff ρ (t:D) _).mpr
          (involution_fixes_displacement ρ (by simpa only [pow_two] using ht2) v)
      exact (congrArg (fixedSpace ρ) heB) ▸ hh
  have hdim := DecomposableMarker.factor_involution_fixed_dimension F B hBF hcB hq hd
  have hlo : 2≤Module.finrank (ZMod 2) R := by
    obtain ⟨hel,hr,hquad,_⟩ := involution_actor_rank_and_fixedCodim ρ (t:D) ht
    have hh : cubicRatio ρ≤actionRatio ρ (zpowers (t:D)) :=
      iInf_le_of_le _ (iInf_le_of_le ⟨hel,isCubic_of_isQuadratic hquad⟩ le_rfl)
    rw [hq,actionRatio,hr,Nat.cast_one,div_one] at hh
    have hh' : 2≤fixedCodim ρ (zpowers (t:D)) := by exact_mod_cast hh
    rwa [fixedCodim_zpowers_eq_displacement_rank] at hh'
  have he : R=F.space⊓fixedSpace ρ B := Submodule.eq_of_le_of_finrank_eq hR (by
    have hh := Submodule.finrank_mono hR
    omega)
  intro z hz
  obtain ⟨v,rfl⟩ := he.symm ▸ hz
  have hfix := hmove v ⟨t,t.property⟩
  have hcomm : ρ (t:D) (ρ g v)=ρ g (ρ (t:D) v) := by
    rw [←Module.End.mul_apply,←map_mul,hc,map_mul,Module.End.mul_apply]
  change ρ g (ρ (t:D) v-v)=ρ (t:D) v-v
  rw [map_sub]
  change ρ (t:D) (ρ g v-v)=ρ g v-v at hfix
  rw [map_sub,hcomm] at hfix
  exact sub_eq_sub_iff_add_eq_add.mpr
    ((sub_eq_sub_iff_add_eq_add.mp hfix).trans (add_comm _ _))

variable {G : Type*} [Group G] [Finite G]

private theorem stabilizes_support_of_fixed_quotient
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (F H E : Submodule (ZMod 2) W)
    (hd : Disjoint F H) (hsplit : E=(F⊓E)⊔(H⊓E)) (hproper : ¬ F≤E)
    (g:D) (hp : F.map (ρ g)=F ∨ F.map (ρ g)=H)
    (hm : ∀v,ρ g v-v∈E) : g∈subspaceStabilizer ρ F := by
  rcases hp with hp|hp
  · exact (subspace_map_eq_iff ρ F g).mp hp
  · apply False.elim
    apply hproper
    intro v hv
    obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp (hsplit ▸ hm v)
    have hg : ρ g v∈H := hp ▸ Submodule.mem_map_of_mem hv
    have hab : v+a=ρ g v-b := by
      rw [sub_eq_iff_eq_add.mp he.symm]
      abel
    have hz : v+a=0 := by
      have hh := hd.le_bot ⟨F.add_mem hv ha.1,hab ▸ H.sub_mem hg hb.1⟩
      exact hh
    have hv' : v=-a := eq_neg_of_add_eq_zero_left hz
    exact hv' ▸ E.neg_mem ha.2

private theorem quintic_section_kernel_centralizes_fixed
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G)≤M) (hn : M≤normalizer (V:Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀g k,(c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom=
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀g k,(c.ambientFactor d k).space.map (imageRepresentation M V hn g)=
      (c.ambientFactor d (π g k)).space)
    (hdec : SourceCases.Decomposable (imageRepresentation M V hn) (T:Subgroup G) M
      (actionHom M V hn).rangeRestrict c d π)
    (hq : cubicRatio (imageRepresentation M V hn)=2)
    (hJi : ((ChapterB.thompsonJ (T:Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict=
      ((T:Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict⊓
        Jhat (imageRepresentation M V hn))
    (X : Subgroup G) (hXM : X≤M)
    (hXJ : (X.subgroupOf M).map (actionHom M V hn).rangeRestrict≤
      normalizer ((((T:Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict⊓
        Jhat (imageRepresentation M V hn) : Subgroup _):Set _))
    (hmove : ⁅X,V⁆≤thompsonFixed T V) : X≤centralizer (thompsonFixed T V:Set G) := by
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let f : M →* D := (actionHom M V hn).rangeRestrict
  let S : Sylow 2 D := (T.subtype hTM).mapSurjective (actionHom M V hn).rangeRestrict_surjective
  let J := (S:Subgroup D)⊓Jhat ρ
  let E := fixedSpace ρ J
  have hE : plane V E=thompsonFixed T V :=
    (congrArg (fun A:Subgroup D => plane V (fixedSpace ρ A)) hJi.symm).trans
      (plane_thompson_image hTM hn)
  obtain ⟨_,_,_,_,hdim⟩ := hdec.ratio_two_dimensions hq
  obtain ⟨_,p,m,hpm,hmark,i,j,hij,hall,hgen,hdis,hcom,hcompl,_⟩ := hdec
  have hcard (k:d.Index) : Nat.card (c.ambientFactor d k).actor=2*p := by
    obtain ⟨l,hl⟩ := hmark k
    exact (Nat.card_range_of_injective (c.ambientFactor d k).embedding.group_injective).trans
      ((Nat.card_congr hl.dihedral.some.toEquiv).trans DihedralGroup.nat_card)
  have hpodd : Odd p := by
    rcases (CyclicSource.primeDimensionOptions_iff p m).mp hpm with ⟨rfl,_⟩|⟨rfl,_⟩ <;> decide
  have hnormal : ((c.ambientFactor d i).actor⊔(c.ambientFactor d j).actor).Normal := by
    rw [hgen]
    exact Jhat_normal ρ
  obtain ⟨hBi,hBj,_⟩ := DecomposableMarker.sylow_pair S _ _ hpodd (hcard i) (hcard j)
    hdis hcom hnormal
  obtain ⟨hZi,hZj,hEsplit⟩ := DecomposableMarker.two_factor_fixed S _ _ hpodd (hcard i) (hcard j)
    hdis hcom hnormal (c.ambient_cross d hij) (c.ambient_cross d hij.symm)
    hcompl hq (hdim i).1 (hdim j).1
  rw [hgen] at hZi hZj hEsplit
  change E=(c.ambientFactor d i).space⊓E⊔(c.ambientFactor d j).space⊓E at hEsplit
  intro x hx z hz
  let g : D := f ⟨x,hXM hx⟩
  have hgJ : g∈normalizer (J:Set D) := hXJ (mem_map_of_mem f hx)
  have hdisp (v:Additive V) : ρ g v-v∈E := by
    have hh := hmove (commutator_mem_commutator hx v.toMul.property)
    rw [←hE] at hh
    obtain ⟨w,hw,he⟩ := hh
    have he' : w=(ρ g v-v).toMul := by
      apply Subtype.ext
      change (w:G)=⁅x,(v.toMul:G)⁆ at he
      rw [he]
      simp only [toMul_sub,div_eq_mul_inv]
      rfl
    change Additive.ofMul w∈E at hw
    rw [he'] at hw
    exact hw
  have hproper : ¬(c.ambientFactor d i).space≤E := by
    intro hh
    have hh' := Submodule.finrank_mono (le_inf le_rfl hh)
    rw [(hdim i).2,hZi] at hh'
    omega
  have hgF : g∈subspaceStabilizer ρ (c.ambientFactor d i).space := by
    apply stabilizes_support_of_fixed_quotient ρ _ _ E hcompl.disjoint hEsplit hproper g
      ?_ hdisp
    rcases hall (π g i) with hi|hj
    · exact Or.inl ((hs g i).trans (congrArg (fun k => (c.ambientFactor d k).space) hi))
    · exact Or.inr ((hs g i).trans (congrArg (fun k => (c.ambientFactor d k).space) hj))
  have hπi : π g i=i := by
    apply (c.ambient_spaces_independent d).injective (c.ambient_space_ne_bot d)
    exact (hs g i).symm.trans ((subspace_map_eq_iff ρ _ g).mpr hgF)
  have hπj : π g j=j := by
    rcases hall (π g j) with hh|hh
    · exact False.elim (hij ((π g).injective (hπi.trans hh.symm)))
    · exact hh
  have hfix (k:d.Index) (hk : π g k=k)
      (hBk : Nat.card ((S:Subgroup D)⊓(c.ambientFactor d k).actor : Subgroup D)=2) :
      ∀v∈(c.ambientFactor d k).space⊓E,ρ g v=v := by
    let F := c.ambientFactor d k
    let B := (S:Subgroup D)⊓F.actor
    have hFJ : F.actor≤Jhat ρ := by
      rw [←c.ambient_actors_generate d]
      exact le_iSup (fun k => (c.ambientFactor d k).actor) k
    have hBJ : B≤J := inf_le_inf_left _ hFJ
    have hBg : g∈normalizer (B:Set D) := by
      have he : B=J⊓F.actor := by
        change (S:Subgroup D)⊓F.actor=((S:Subgroup D)⊓Jhat ρ)⊓F.actor
        rw [inf_assoc,inf_eq_right.mpr hFJ]
      rw [he]
      exact le_normalizer_inf (zpowers_le.mpr hgJ)
        (zpowers_le.mpr (mem_normalizer_iff_map_conj_eq.mpr
          ((hp g k).trans (congrArg (fun k => (c.ambientFactor d k).actor) hk))))
        (mem_zpowers g)
    intro v hv
    exact support_fixer_of_fixed_displacement ρ F B inf_le_right hBk hq (hdim k).1
      g hBg (fun w => fixedSpace_antitone ρ hBJ (hdisp w)) v
      ⟨hv.1,fixedSpace_antitone ρ hBJ hv.2⟩
  rw [←hE] at hz
  obtain ⟨w,hw,rfl⟩ := hz
  change Additive.ofMul w∈E at hw
  obtain ⟨a,ha,b,hb,he⟩ := Submodule.mem_sup.mp (hEsplit ▸ hw)
  have hwfix : ρ g (Additive.ofMul w)=Additive.ofMul w := by
    rw [←he,map_add,hfix i hπi hBi a ha,hfix j hπj hBj b hb]
  have heq := congrArg (fun v:Additive V => (v.toMul:G)) hwfix
  change x*(w:G)*x⁻¹=(w:G) at heq
  exact (mul_inv_eq_iff_eq_mul.mp heq).symm

/-- On every actual section H/E containing the original V/E, the partner
kernel centralizes E. The original factor actions and Thompson image are
constructed internally, and no faithful quotient action is assumed. -/
theorem PreparedChosenModule.decomposable_five_section_kernel_centralizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M≠Mc) (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
    letI := h.elementary
    ∀ {U : Submodule (ZMod 2) (Additive V)}
      (c : FactorData (imageRepresentation M V h.normalized)
        (Jhat (imageRepresentation M V h.normalized)) U)
      (d : Decomposition c.representation), d.FittingFull →
    ∀ (s : ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      ∀ H : Subgroup G, V≤H → Mc≤normalizer (thompsonFixed T V:Set G) →
        commutatorPreimage Mc H (thompsonFixed T V)≤centralizer (thompsonFixed T V:Set G) := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive H hVH hMcE
  let V := localModule T M
  let E := thompsonFixed T V
  let K := commutatorPreimage Mc H E
  let f := (actionHom M V h.normalized).rangeRestrict
  have hKM : K≤M := by
    have hKV : ⁅K,V⁆≤V := ((commutator_mono le_rfl hVH).trans
      (commutator_commutatorPreimage_le Mc H E hMcE)).trans inf_le_left
    exact (le_normalizer_iff_commutator_le_right.mpr hKV).trans
      (hM.1.1.2 ⟨V,h.nontrivial,IsElementaryAbelian.isPGroup 2 V,rfl⟩ h.normalized)
  have hMcC : Mc∈maximalTwoLocalOvergroups (centralizer (centralInvolutions T:Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T:Subgroup G)≤Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hMc : Mc∈maximalTwoLocalOvergroups (T:Subgroup G) := ⟨hMcC.1,hTMc⟩
  let A := ((M⊓Mc).subgroupOf M).map f
  have hSA : ((T:Subgroup G).subgroupOf M).map f≤A :=
    map_mono (subgroupOf_mono M (le_inf hM.1.2 hTMc))
  have hnot := h.decomposable_five_third_image_not_contains hG T hempty hM hJ rfl
    c d hd s π hp hs hdec hfive hMc hne.symm
  have hAJ := (s.image_contains_or_normalizes_of_prime_five hM.1.2 h.normalized
    c d π hp hdec hfive A hSA).resolve_left hnot
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun A hA => hA.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  exact quintic_section_kernel_centralizes_fixed hM.1.2 h.normalized c d π hp hs hdec hq hJi
    K hKM ((map_mono (subgroupOf_mono M (le_inf hKM
      (commutatorPreimage_le Mc H E)))).trans hAJ)
    ((commutator_mono le_rfl hVH).trans (commutator_commutatorPreimage_le Mc H E hMcE))

end CFSG.Quasithin.Chapter15.Section01
