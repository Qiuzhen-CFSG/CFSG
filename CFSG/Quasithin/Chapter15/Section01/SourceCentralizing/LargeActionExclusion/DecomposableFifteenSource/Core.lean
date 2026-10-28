module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticCore
public import Theory.Representation.BinaryOffender.CyclicInvolutionFixedKernel
public import Theory.GroupTheory.ChainCentralizerTwoCore
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.Thompson

/-!
# The full original module in the partner core when its module is E

The partner core centralizes its own local module. If that module is the
original Thompson fixed group E, its restriction to each quintic support
fixes the marked plane pointwise. Cyclicity of the Sylow action on the
support restricts this action to the original factor involution. Thus its
displacement on V lies in E. The characteristic-two normal-chain lemma
then puts the whole original V in the actual partner core.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker

private theorem cyclic_support_fixer_displacement
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [Finite W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (F : Factor ρ)
    (B C : Subgroup D) (hBF : B≤F.actor) (hBC : B≤C)
    (hC : C≤subspaceStabilizer ρ F.space)
    (hcB : Nat.card B=2) (hq : cubicRatio ρ=2)
    (hd : Module.finrank (ZMod 2) F.Space=4)
    (Z : Submodule (ZMod 2) W) (hZF : Z≤F.space)
    (hZB : Z≤fixedSpace ρ B) (hdZ : Module.finrank (ZMod 2) Z=2)
    [IsCyclic (restrictedSubgroup ρ F.space C)]
    (g : D) (hgC : g∈C) (hgZ : ∀z∈Z,ρ g z=z) :
    ∀v∈F.space,ρ g v-v∈Z := by
  have he : Z=F.space⊓fixedSpace ρ B := Submodule.eq_of_le_of_finrank_eq
    (le_inf hZF hZB) (hdZ.trans
      (DecomposableMarker.factor_involution_fixed_dimension F B hBF hcB hq hd).symm)
  obtain ⟨b,hbo⟩ := exists_prime_orderOf_dvd_card' (G:=B) 2 (by rw [hcB])
  have hb2 : (b:D)^2=1 := congrArg Subtype.val (hbo ▸ pow_orderOf_eq_one b)
  have hbne : (b:D)≠1 := by
    intro hh
    have hh' : b=1 := Subtype.ext hh
    rw [hh',orderOf_one] at hbo
    contradiction
  have hbB : zpowers (b:D)=B := eq_of_le_of_card_ge (zpowers_le.mpr b.property) (by
    rw [Nat.card_zpowers,hcB]
    have hbD : orderOf (b:D)=2 := by simpa only [Subgroup.orderOf_coe] using hbo
    rw [hbD])
  let f := subgroupActionHom ρ F.space C hC
  let σ := subspaceImageRepresentation ρ F.space
  let P := restrictedSubgroup ρ F.space C
  let t := f ⟨b,hBC b.property⟩
  let x := f ⟨g,hgC⟩
  have htP : t∈P := by
    change t∈restrictedSubgroup ρ F.space C
    rw [←subgroupActionHom_range ρ F.space C hC]
    exact ⟨⟨b,hBC b.property⟩,rfl⟩
  have hxP : x∈P := by
    change x∈restrictedSubgroup ρ F.space C
    rw [←subgroupActionHom_range ρ F.space C hC]
    exact ⟨⟨g,hgC⟩,rfl⟩
  have ht2 : t^2=1 := by rw [←map_pow,show (⟨b,hBC b.property⟩:C)^2=1 from Subtype.ext hb2,map_one]
  have htne : t≠1 := by
    intro ht
    have hfix : ∀v∈F.space,ρ (b:D) v=v := by
      intro v hv
      exact congrArg (fun a => (σ a ⟨v,hv⟩ : W)) ht
    obtain ⟨a,ha⟩ := hBF b.property
    have hfa : F.action a=1 := by
      ext v
      apply F.embedding.space_injective
      rw [F.embedding.equivariant,ha]
      exact hfix _ ⟨v,rfl⟩
    have ha1 : a=1 := F.faithful (hfa.trans F.action.map_one.symm)
    exact hbne (ha.symm.trans ((congrArg F.embedding.groupMap ha1).trans F.embedding.groupMap.map_one))
  have hfixed : fixedSpace σ (zpowers t)=Z.comap F.space.subtype := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    change σ t v=v ↔ (v:W)∈Z
    rw [he]
    change σ t v=v ↔ (v:W)∈F.space ∧ (v:W)∈fixedSpace ρ B
    constructor
    · intro hv
      refine ⟨v.property,?_⟩
      rw [←hbB]
      apply (mem_fixedSpace_zpowers_iff ρ (b:D) (v:W)).mpr
      exact congrArg Subtype.val hv
    · intro hv
      apply Subtype.ext
      exact (mem_fixedSpace_zpowers_iff ρ (b:D) v).mp (hbB.symm ▸ hv.2)
  have hx : x∈zpowers t := by
    rw [←subspaceKernel_eq_zpowers_of_cyclic σ
      (subspaceImageRepresentation_injective ρ F.space) P t htP ht2 htne]
    refine ⟨hxP,?_⟩
    intro v hv
    rw [hfixed] at hv
    apply Subtype.ext
    exact hgZ v hv
  have hx2 : x^2=1 := by
    obtain ⟨n,hn⟩ := mem_zpowers_iff.mp hx
    rw [←hn,←zpow_natCast,←zpow_mul,mul_comm, zpow_mul, zpow_natCast,ht2,one_zpow]
  have hxcase : x=1 ∨ x=t := by
    by_cases hh : x=1
    · exact Or.inl hh
    · right
      exact congrArg P.subtype (IsCyclic.eq_of_orderOf_eq_two
        (G:=P) (x:=⟨x,hxP⟩) (y:=⟨t,htP⟩)
        (orderOf_eq_prime (Subtype.ext hx2) (fun he => hh (congrArg P.subtype he)))
        (orderOf_eq_prime (Subtype.ext ht2) (fun he => htne (congrArg P.subtype he))))
  intro v hv
  have hmove : σ x ⟨v,hv⟩-⟨v,hv⟩∈fixedSpace σ (zpowers t) := by
    rcases hxcase with hh | hh
    · rw [hh,map_one,Module.End.one_apply,sub_self]
      exact zero_mem _
    · rw [hh,mem_fixedSpace_zpowers_iff]
      exact involution_fixes_displacement σ (by simpa only [pow_two] using ht2) _
  rw [hfixed] at hmove
  exact hmove

variable {G : Type*} [Group G] [Finite G]

private theorem quintic_centralizer_displacement
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G)≤M) (hn : M≤normalizer (V:Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T:=T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀g k,(c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom=
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀g k,(c.ambientFactor d k).space.map (imageRepresentation M V hn g)=
      (c.ambientFactor d (π g k)).space)
    (hdec : SourceCases.Decomposable (imageRepresentation M V hn) (T:Subgroup G) M
      (actionHom M V hn).rangeRestrict c d π)
    (hq : cubicRatio (imageRepresentation M V hn)=2) (hfive : s.prime=5)
    (hJi : ((ChapterB.thompsonJ (T:Subgroup G) 1).subgroupOf M).map
      (actionHom M V hn).rangeRestrict=
      ((T:Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict⊓
        Jhat (imageRepresentation M V hn))
    (X : Subgroup G) (hXT : X≤(T:Subgroup G))
    (hXC : X≤centralizer (thompsonFixed T V:Set G)) :
    ⁅X,V⁆≤thompsonFixed T V := by
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let f := (actionHom M V hn).rangeRestrict
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
  obtain ⟨hZi,hZj,_⟩ := DecomposableMarker.two_factor_fixed S _ _ hpodd (hcard i) (hcard j)
    hdis hcom hnormal (c.ambient_cross d hij) (c.ambient_cross d hij.symm)
    hcompl hq (hdim i).1 (hdim j).1
  rw [hgen] at hZi hZj
  have hsupport (x:G) (hx:x∈X) (k:d.Index) :
      x∈normalizer (plane V (c.ambientFactor d k).space:Set G) := by
    have hfirst := s.centralizer_le_stabilizer
      ⟨hXT hx,(hXC.trans (centralizer_le inf_le_right)) hx⟩
    rcases s.covers k with rfl|rfl
    · exact hfirst
    · exact s.stabilizes_second ⟨hXT hx,hfirst⟩
  have hmove (x:G) (hx:x∈X) (k:d.Index)
      (hBk : Nat.card ((S:Subgroup D)⊓(c.ambientFactor d k).actor : Subgroup D)=2)
      (hZk : Module.finrank (ZMod 2) ((c.ambientFactor d k).space⊓E : Submodule _ _)=2) :
      ∀v∈(c.ambientFactor d k).space,ρ (f ⟨x,hTM (hXT hx)⟩) v-v∈E := by
    let F := c.ambientFactor d k
    let B := (S:Subgroup D)⊓F.actor
    let C := (S:Subgroup D)⊓subspaceStabilizer ρ F.space
    have hFs : F.actor≤subspaceStabilizer ρ F.space := by
      apply le_subspaceStabilizer
      rintro a ⟨a,rfl⟩ v ⟨v,rfl⟩
      exact ⟨F.action a v,F.embedding.equivariant a v⟩
    have hBC : B≤C := le_inf inf_le_left (inf_le_right.trans hFs)
    let : IsCyclic (restrictedSubgroup ρ F.space C) :=
      quintic_support_two_cyclic F (c.support_stabilizer_normalizes_actor d π hp hs k)
        (s.marking k) (by
          change CyclicSource.DihedralMarking (s.marking k) 5 2
          simpa only [hfive] using s.dihedral k)
        C S.isPGroup'.to_inf_left inf_le_right
    have hBJ : B≤J := inf_le_inf_left _ (by
        change F.actor≤Jhat ρ
        rw [←c.ambient_actors_generate d]
        exact le_iSup (fun k => (c.ambientFactor d k).actor) k)
    have hxC : f ⟨x,hTM (hXT hx)⟩∈C := by
      refine ⟨mem_map_of_mem f (hXT hx),?_⟩
      apply (subspace_map_eq_iff ρ F.space _).mp
      apply plane_injective V
      rw [←plane_conjugate hn F.space ⟨x,hTM (hXT hx)⟩]
      exact mem_normalizer_iff_map_conj_eq.mp (hsupport x hx k)
    have hxfix : ∀v∈F.space⊓E,ρ (f ⟨x,hTM (hXT hx)⟩) v=v := by
      intro v hv
      have hvE : (v.toMul:G)∈thompsonFixed T V :=
        hE ▸ mem_map_of_mem V.subtype hv.2
      apply Additive.toMul.injective
      apply Subtype.ext
      change x*(v.toMul:G)*x⁻¹=(v.toMul:G)
      rw [←hXC hx _ hvE,mul_inv_cancel_right]
    exact fun v hv => (cyclic_support_fixer_displacement ρ F B C inf_le_right hBC
      inf_le_right hBk hq (hdim k).1 (F.space⊓E) inf_le_left
      (inf_le_right.trans (fixedSpace_antitone ρ hBJ)) hZk _ hxC hxfix v hv).2
  rw [commutator_le]
  intro x hx v hv
  let w : Additive V := Additive.ofMul ⟨v,hv⟩
  obtain ⟨a,ha,b,hb,hab⟩ := Submodule.mem_sup.mp
    (show w∈(c.ambientFactor d i).space⊔(c.ambientFactor d j).space from
      hcompl.sup_eq_top ▸ Submodule.mem_top)
  have hw : ρ (f ⟨x,hTM (hXT hx)⟩) w-w∈E := by
    rw [←hab,map_add]
    have he : ρ (f ⟨x,hTM (hXT hx)⟩) a+ρ (f ⟨x,hTM (hXT hx)⟩) b-(a+b)=
        (ρ (f ⟨x,hTM (hXT hx)⟩) a-a)+(ρ (f ⟨x,hTM (hXT hx)⟩) b-b) := by abel
    rw [he]
    exact E.add_mem (hmove x hx i hBi hZi a ha) (hmove x hx j hBj hZj b hb)
  rw [←hE]
  refine ⟨(ρ (f ⟨x,hTM (hXT hx)⟩) w-w).toMul,hw,?_⟩
  simp only [toMul_sub,div_eq_mul_inv]
  change x*v*x⁻¹*v⁻¹=⁅x,v⁆
  rfl

/-- The full Sylow centralizer of the original fixed group acts trivially
on the original chosen module modulo that same fixed group. -/
theorem PreparedChosenModule.decomposable_five_fixed_centralizer_displacement
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
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
      ⁅(T:Subgroup G)⊓centralizer (thompsonFixed T V:Set G),V⁆≤thompsonFixed T V := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun A hA => hA.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  exact quintic_centralizer_displacement hM.1.2 h.normalized c d s π hp hs
    hdec hq hfive hJi _ inf_le_left inf_le_right

/-- If the actual partner module is the full original Thompson fixed group,
the whole original chosen module lies in its literal two-core. -/
theorem PreparedChosenModule.decomposable_five_full_partner_module_le_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (h : PreparedChosenModule T M V) (hfull : V = localModule T M) :
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
      localModule T Mc = thompsonFixed T V →
      ⁅Mc.pCoreIn 2,V⁆ ≤ thompsonFixed T V ∧ V ≤ Mc.pCoreIn 2 := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive he
  let V := localModule T M
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let Q := C.pCoreIn 2
  obtain ⟨_,hQ,hQT,_,hself,hEC,_,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive
  change Q=Mc.pCoreIn 2 at hQ
  have hCE : C = centralizer (E:Set G) := congrArg (fun A:Subgroup G => centralizer (A:Set G)) he
  have hVC : V≤C := by
    rw [hCE]
    exact V.le_centralizer.trans (centralizer_le inf_le_left)
  have hQE : Q≤centralizer (E:Set G) := (pCoreIn_le 2 C).trans_eq hCE
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun A hA => hA.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  have hmove := quintic_centralizer_displacement hM.1.2 h.normalized c d s π hp hs
    hdec hq hfive hJi Q hQT hQE
  have hVCcore : V≤Q := le_twoCore_of_relative_chain C Q E V
    (pCoreIn_le 2 C) hEC hVC
    (C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C)))
    (hCE.le.trans (Subgroup.centralizer_le_normalizer _))
    (isPGroup_pCoreIn 2 C) hself (hVC.trans hCE.le) (by rwa [commutator_comm])
  exact ⟨by rwa [hQ] at hmove,hVCcore.trans_eq hQ⟩

end CFSG.Quasithin.Chapter15.Section01
