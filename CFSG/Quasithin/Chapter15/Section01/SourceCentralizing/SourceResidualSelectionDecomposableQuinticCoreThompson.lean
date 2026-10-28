module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticCore
public import Stellmacher.ElementaryAbelianMaxJFixedCenter
public import Theory.GroupTheory.ConjugateSpanNormalizer

/-!
# The quintic partner core and its characteristic Thompson-center envelope

An involution preserving the two original supports acts on either support
as the identity or its unique factor involution. It therefore centralizes
the original Thompson fixed subgroup E. Every elementary subgroup of Q
acts on E through at most the support exchange. Elementary replacement by
E excludes that exchange for maximum elementary subgroups of Q.

Consequently J(Q) centralizes E, and E and its entire partner-kernel span
lie in the characteristic elementary group Ω₁Z(J(Q)). No cardinality
assumption on the partner module is used.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u
variable {G : Type*} [Group G] [Finite G]

/-- Any involution in a cyclic quintic support action is trivial or agrees
with the chosen nontrivial factor involution on that entire support. -/
theorem DecomposableMarker.quintic_involution_restriction
    {D W : Type u} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} (F : Factor ρ)
    (hN : subspaceStabilizer ρ F.space≤normalizer (F.actor : Set D))
    (l : CyclicSource.LocalGeneration F.action) (hm : CyclicSource.DihedralMarking l 5 2)
    (A : Subgroup D) (hA : IsPGroup 2 A) (hAS : A≤subspaceStabilizer ρ F.space)
    (r : D) (hrA : r∈A) (hrF : r∈F.actor) (hr : orderOf r=2)
    (a : D) (haA : a∈A) (ha : a^2=1) :
    (∀v∈F.space,ρ a v=v) ∨ (∀v∈F.space,ρ a v=ρ r v) := by
  let f := subgroupActionHom ρ F.space A hAS
  let r₀ : A := ⟨r,hrA⟩
  let a₀ : A := ⟨a,haA⟩
  let : IsCyclic (restrictedSubgroup ρ F.space A) := quintic_support_two_cyclic F hN l hm A hA hAS
  have hfr : f r₀≠1 := by
    intro he
    have hfix : ∀v∈F.space,ρ r v=v := by
      intro v hv
      exact congrArg (fun x => (subspaceImageRepresentation ρ F.space x ⟨v,hv⟩:W)) he
    have hr1 : r=1 := by
      obtain ⟨r',rfl⟩ := hrF
      have hh : F.action r'=1 := by
        ext v
        apply F.embedding.space_injective
        exact (F.embedding.equivariant r' v).trans (hfix _ ⟨v,rfl⟩)
      rw [F.faithful (hh.trans F.action.map_one.symm),map_one]
    rw [hr1,orderOf_one] at hr
    contradiction
  by_cases hfa : f a₀=1
  · left
    intro v hv
    exact congrArg (fun x => (subspaceImageRepresentation ρ F.space x ⟨v,hv⟩:W)) hfa
  · right
    let ar : restrictedSubgroup ρ F.space A :=
      ⟨f a₀,(subgroupActionHom_range ρ F.space A hAS) ▸ ⟨a₀,rfl⟩⟩
    let rr : restrictedSubgroup ρ F.space A :=
      ⟨f r₀,(subgroupActionHom_range ρ F.space A hAS) ▸ ⟨r₀,rfl⟩⟩
    have har : orderOf ar=2 := orderOf_eq_prime (Subtype.ext (by
      change (f a₀)^2=1
      rw [←map_pow,show a₀^2=1 from Subtype.ext ha,map_one]))
      (fun he => hfa (congrArg Subtype.val he))
    have hrr : orderOf rr=2 := orderOf_eq_prime (Subtype.ext (by
      change (f r₀)^2=1
      rw [←map_pow,show r₀^2=1 from Subtype.ext (hr ▸ pow_orderOf_eq_one r),map_one]))
      (fun he => hfr (congrArg Subtype.val he))
    have he := congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two har hrr)
    intro v hv
    exact congrArg (fun x => (subspaceImageRepresentation ρ F.space x ⟨v,hv⟩:W)) he

private theorem factor_stabilizes
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} (F : Factor ρ) :
    F.actor≤subspaceStabilizer ρ F.space := by
  apply le_subspaceStabilizer
  rintro a ⟨a,rfl⟩ v ⟨v,rfl⟩
  exact ⟨F.action a v,F.embedding.equivariant a v⟩

private theorem sylow_factor_card_two
    {D : Type*} [Group D] [Finite D] (S : Sylow 2 D)
    (L : Subgroup D) (hL : L.IsSubnormal) (hc : Nat.card L=10) :
    Nat.card ((S:Subgroup D)⊓L : Subgroup D)=2 := by
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal L hL
  have hh := P.card_eq_multiplicity
  rw [hc,show 2^Nat.factorization 10 2=2 by decide +kernel,hP] at hh
  rw [←map_subgroupOf_eq_of_le (show (S:Subgroup D)⊓L≤L from inf_le_right)]
  simpa only [inf_subgroupOf_right,card_map_of_injective L.subtype_injective] using hh

/-- A literal Sylow involution preserving one original quintic support
centralizes the whole original Thompson fixed subgroup. -/
theorem DecomposableMarker.ThompsonPair.involution_centralizes_fixed
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T:Subgroup G)≤M) (hn : M≤normalizer (V:Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T:=T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀g k,(c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀g k,(c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hdec : SourceCases.Decomposable (imageRepresentation M V hn) (T:Subgroup G) M
      (actionHom M V hn).rangeRestrict c d π) (hfive : s.prime=5)
    (hJi : ((ChapterB.thompsonJ (T:Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict =
      ((T:Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn))
    (a : G) (haT : a∈(T:Subgroup G)) (ha : a^2=1)
    (haN : a∈normalizer (plane V (c.ambientFactor d s.first).space : Set G)) :
    a∈centralizer (thompsonFixed T V : Set G) := by
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let f : M →* D := (actionHom M V hn).rangeRestrict
  let S : Sylow 2 D := (T.subtype hTM).mapSurjective (actionHom M V hn).rangeRestrict_surjective
  let J : Subgroup D := ((ChapterB.thompsonJ (T:Subgroup G) 1).subgroupOf M).map f
  let a₀ : M := ⟨a,hTM haT⟩
  have ha2 : (f a₀)^2=1 := by rw [←map_pow,show a₀^2=1 from Subtype.ext ha,map_one]
  have haS : f a₀∈(S:Subgroup D) := mem_map_of_mem f haT
  have hJplane : plane V (fixedSpace ρ J)=thompsonFixed T V := plane_thompson_image hTM hn
  obtain ⟨_,_,_,_,_,i,j,hij,hall,hgen,hdis,hcom,_,_⟩ := hdec
  have hsub (k : d.Index) : (c.ambientFactor d k).actor.IsSubnormal := by
    have hnormal : ((c.ambientFactor d i).actor⊔(c.ambientFactor d j).actor).Normal := by
      rw [hgen]; exact Jhat_normal ρ
    have hRL : (c.ambientFactor d j).actor≤normalizer ((c.ambientFactor d i).actor : Set D) :=
      (show (c.ambientFactor d j).actor≤centralizer ((c.ambientFactor d i).actor : Set D) from
        fun b hb a ha => (hcom a ha b hb).eq).trans (Subgroup.centralizer_le_normalizer _)
    have hLR : (c.ambientFactor d i).actor≤normalizer ((c.ambientFactor d j).actor : Set D) :=
      (show (c.ambientFactor d i).actor≤centralizer ((c.ambientFactor d j).actor : Set D) from
        fun a ha b hb => (hcom a ha b hb).symm.eq).trans (Subgroup.centralizer_le_normalizer _)
    rcases hall k with hk | hk
    · rw [hk]
      exact Subgroup.IsSubnormal.trans le_sup_left
        (normal_subgroupOf_of_le_normalizer (sup_le (c.ambientFactor d i).actor.le_normalizer hRL)).isSubnormal
        hnormal.isSubnormal
    · rw [hk]
      exact Subgroup.IsSubnormal.trans le_sup_right
        (normal_subgroupOf_of_le_normalizer (sup_le hLR (c.ambientFactor d j).actor.le_normalizer)).isSubnormal
        hnormal.isSubnormal
  have hac (k : d.Index) : a∈centralizer (thompsonPlane T V (c.ambientFactor d k).space : Set G) := by
    let F := c.ambientFactor d k
    have hNk : a∈normalizer (plane V F.space : Set G) := by
      rcases s.covers k with rfl | rfl
      · exact haN
      · exact s.stabilizes_second ⟨haT,haN⟩
    have hastab : f a₀∈subspaceStabilizer ρ F.space := by
      apply (subspace_map_eq_iff ρ F.space (f a₀)).mp
      apply plane_injective V
      exact (plane_conjugate hn F.space a₀).symm.trans (mem_normalizer_iff_map_conj_eq.mp hNk)
    have hcF : Nat.card F.actor=10 := by
      have hm := (s.dihedral k).dihedral
      rw [hfive] at hm
      exact (Nat.card_range_of_injective F.embedding.group_injective).trans
        ((Nat.card_congr hm.some.toEquiv).trans DihedralGroup.nat_card)
    have hcr := sylow_factor_card_two S F.actor (hsub k) hcF
    obtain ⟨r,hr⟩ := exists_prime_orderOf_dvd_card' (G:=((S:Subgroup D)⊓F.actor : Subgroup D)) 2
      (by rw [hcr])
    have hrD : orderOf (r:D)=2 := by simpa only [orderOf_coe] using hr
    let A : Subgroup D := (S:Subgroup D)⊓subspaceStabilizer ρ F.space
    have hrA : (r:D)∈A := ⟨r.property.1,factor_stabilizes F r.property.2⟩
    have hm : CyclicSource.DihedralMarking (s.marking k) 5 2 := by simpa only [hfive] using s.dihedral k
    have hres := quintic_involution_restriction F
      (c.support_stabilizer_normalizes_actor d π hp hs k) (s.marking k)
      (show CyclicSource.DihedralMarking (s.marking k) 5 2 from hm)
      A S.isPGroup'.to_inf_left inf_le_right r hrA r.property.2 hrD (f a₀) ⟨haS,hastab⟩ ha2
    have hrJ : (r:D)∈J := by
      change (r:D)∈((ChapterB.thompsonJ (T:Subgroup G) 1).subgroupOf M).map (actionHom M V hn).rangeRestrict
      rw [hJi]
      refine ⟨r.property.1,?_⟩
      exact (c.ambient_actors_generate d ▸ le_iSup (fun k => (c.ambientFactor d k).actor) k) r.property.2
    rintro z ⟨hzF,hzE⟩
    obtain ⟨v,hv,rfl⟩ := hzF
    have hvJ : Additive.ofMul v∈fixedSpace ρ J := by
      have hh : (v:G)∈plane V (fixedSpace ρ J) := hJplane.symm ▸ hzE
      obtain ⟨w,hw,he⟩ := hh
      have he' : w=v := Subtype.ext he
      exact he' ▸ hw
    have hfix : ρ (f a₀) (Additive.ofMul v)=Additive.ofMul v := by
      rcases hres with hh | hh
      · exact hh _ hv
      · exact (hh _ hv).trans (hvJ ⟨r,hrJ⟩)
    have he := congrArg (fun w : Additive V => (w.toMul:G)) hfix
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  apply mem_centralizer_iff.mpr
  have hh : thompsonFixed T V≤centralizer ({a}:Set G) := by
    rw [s.thompson_split]
    exact sup_le (by intro z hz; exact mem_centralizer_singleton_iff.mpr (hac s.first z hz))
      (by intro z hz; exact mem_centralizer_singleton_iff.mpr (hac s.second z hz))
  intro z hz
  exact mem_centralizer_singleton_iff.mp (hh hz)

private theorem core_maxJ_centralizes_exchanged_pair
    (T S Q E Z₁ Z₂ : Subgroup G) [IsElementaryAbelian 2 E]
    (hQT : Q≤T) (hEQ : E≤Q) (hi : S.relIndex T=2)
    (hE : Nat.card E=16) (hZ₁ : Nat.card Z₁=4)
    (hZ₁E : Z₁≤E) (hdZ : Disjoint Z₁ Z₂)
    (hinv : ∀a∈Q,a^2=1→a∈S→a∈centralizer (E:Set G))
    (hexchange : ∀q∈Q,q∉S→Z₁.map (MulAut.conj q).toMonoidHom=Z₂) :
    elementaryAbelianMaxJ Q≤centralizer (E:Set G) := by
  apply sSup_le
  intro A hA
  let : IsElementaryAbelian 2 A := hA.2.1
  have hSC : A⊓S≤centralizer (E:Set G) := by
    intro a ha
    exact hinv a (hA.1 ha.1) (elemPow_eq_one_of_isElementaryAbelian (p:=2) a ha.1) ha.2
  by_contra hnot
  obtain ⟨a,ha,hane⟩ := Set.not_subset.mp hnot
  have haS : a∉S := fun hh => hane (hSC ⟨ha,hh⟩)
  have hex := hexchange a (hA.1 ha) haS
  let C := A⊓centralizer (E : Set G)
  let I := E⊓C
  let D := A⊓S
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le inf_le_left
  have hDC : D≤C := by
    intro d hd
    exact ⟨hd.1,hSC hd⟩
  have hcardA : Nat.card A≤2*Nat.card C := by
    have hind : S.relIndex A≤2 := by
      simpa only [hi] using relIndex_le_of_le_right (H:=S) (hA.1.trans hQT)
        (show S.relIndex T≠0 from by rw [hi]; decide)
    have he : Nat.card D*S.relIndex A=Nat.card A := by
      simpa only [D,relIndex_bot_left,inf_relIndex_left] using
        relIndex_mul_relIndex (⊥ : Subgroup G) D A bot_le inf_le_left
    have hcd := card_le_of_le hDC
    nlinarith
  have hIZ : Disjoint I Z₁ := by
    apply disjoint_def.mpr
    intro x hx hxZ
    have hax : a*x*a⁻¹=x := by
      have hc : a*x=x*a := congrArg Subtype.val
        (mul_comm (⟨a,ha⟩ : A) ⟨x,hx.2.1⟩)
      rw [hc,mul_inv_cancel_right]
    have hxZ₂ : x∈Z₂ := hax ▸ (hex ▸ mem_map_of_mem (MulAut.conj a).toMonoidHom hxZ)
    exact disjoint_def.mp hdZ hxZ hxZ₂
  have hIZcomm : Z₁≤centralizer (I : Set G) := by
    intro z hz i hi
    exact congrArg Subtype.val (mul_comm (⟨i,hi.1⟩ : E) ⟨z,hZ₁E hz⟩)
  have hcardI : Nat.card I≤4 := by
    have hp := card_sup_eq_mul_of_normalizes_of_disjoint I Z₁
      (hIZcomm.trans (Subgroup.centralizer_le_normalizer _)) hIZ
    have hb := card_le_of_le (sup_le (show I≤E from inf_le_left) hZ₁E)
    rw [hp,hZ₁,hE] at hb
    omega
  have hCE : C≤centralizer (E : Set G) := inf_le_right
  let : IsElementaryAbelian 2 (E⊔C : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer hCE
  have hmax := hA.2.2 (E⊔C) (sup_le hEQ (inf_le_left.trans hA.1)) inferInstance
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes E C
    (hCE.trans (Subgroup.centralizer_le_normalizer _))
  change Nat.card E*Nat.card C=Nat.card I*Nat.card (E⊔C : Subgroup G) at hprod
  rw [hE] at hprod
  have hpos : 0<Nat.card C := Nat.card_pos
  nlinarith

omit [Finite G] in
private theorem kernel_envelope_normalizer (Q : Subgroup G) :
    normalizer (Q : Set G)≤normalizer (omegaOneCenterAmbient (elementaryAbelianMaxJ Q) : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hQg : Q.map (MulAut.conj g).toMonoidHom=Q := mem_normalizer_iff_map_conj_eq.mp hg
  change (omegaOneCenterAmbient (elementaryAbelianMaxJ Q)).map (MulAut.conj g).toMonoidHom=_
  rw [←omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,
    ←elementaryAbelianMaxJ_map_equiv,hQg]

/-- The original fixed subgroup and its full partner-kernel span lie in
Ω₁Z(J(Q)) for every actual quintic branch. -/
theorem PreparedChosenModule.decomposable_five_partner_fixed_envelope
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
    ∀ (s : DecomposableMarker.ThompsonPair (T := T) h.normalized c d)
      (π : internalActionImage M V h.normalized →* Equiv.Perm d.Index),
      (∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
        (c.ambientFactor d (π g k)).actor) →
      (∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V h.normalized g) =
        (c.ambientFactor d (π g k)).space) →
      SourceCases.Decomposable (imageRepresentation M V h.normalized) (T : Subgroup G) M
        (actionHom M V h.normalized).rangeRestrict c d π →
      cubicRatio (imageRepresentation M V h.normalized) = 2 → s.prime = 5 →
      let Uc := localModule T Mc
      let E := thompsonFixed T V
      let C := centralizer (Uc : Set G)
      let Q := C.pCoreIn 2
      let F := conjugateSpanBy E C
      let A := omegaOneCenterAmbient (elementaryAbelianMaxJ Q)
      elementaryAbelianMaxJ Q≤centralizer (E : Set G) ∧ E≤A ∧ F≤A ∧
        IsElementaryAbelian 2 F ∧ Mc≤normalizer (A : Set G) ∧ Mc≤normalizer (F : Set G) := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  let Uc := localModule T Mc
  let E := thompsonFixed T (localModule T M)
  let C := centralizer (Uc : Set G)
  let Q := C.pCoreIn 2
  let F := conjugateSpanBy E C
  let A := omegaOneCenterAmbient (elementaryAbelianMaxJ Q)
  let Z₁ := thompsonPlane T (localModule T M) (c.ambientFactor d s.first).space
  let Z₂ := thompsonPlane T (localModule T M) (c.ambientFactor d s.second).space
  let S := (T : Subgroup G)⊓normalizer (plane (localModule T M) (c.ambientFactor d s.first).space : Set G)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le inf_le_left
  obtain ⟨hCMc,hcore,hQT,_,_,_,_,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive
  have hEQ : E≤Q := (h.decomposable_five_fixed_le_partner_core
    hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive).trans_eq hcore.symm
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun A hA => hA.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  have hJE : elementaryAbelianMaxJ Q≤centralizer (E:Set G) := by
    apply core_maxJ_centralizes_exchanged_pair (T:Subgroup G) S Q E Z₁ Z₂
      hQT hEQ s.stabilizer_index s.fixed_card (s.thompson_card s.first)
      inf_le_right (disjoint_iff.mpr s.thompson_disjoint)
    · intro a ha ha2 haS
      exact s.involution_centralizes_fixed hM.1.2 h.normalized c d π hp hs hdec hfive hJi
        a (hQT ha) ha2 haS.2
    · intro q hq hqS
      exact (s.thompson_exchanges q (hQT hq) (fun hh => hqS ⟨hQT hq,hh⟩)).1
  have hEA : E≤A := elementary_centralizer_maxJ_le_omegaCenter Q E hEQ
    (le_centralizer_iff.mp hJE)
  have hMcQ : Mc≤normalizer (Q : Set G) := by
    change Mc≤normalizer (C.pCoreIn 2 : Set G)
    rw [hcore]
    exact Mc.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))
  have hMcA : Mc≤normalizer (A : Set G) := hMcQ.trans (kernel_envelope_normalizer Q)
  have hFA : F≤A := conjugateSpanBy_le hEA (hCMc.trans hMcA)
  let : IsElementaryAbelian 2 A := omegaOneCenterAmbient_elementaryAbelian _
  have hMcC : Mc∈maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G)≤Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hIE : M⊓Mc≤normalizer (E : Set G) := (h.decomposable_five_partner_control
    hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive).2.1
  have hMcCN : Mc≤normalizer (C : Set G) :=
    (le_normalizer_conjugateSpanBy (centralInvolutions T) Mc).trans
      (normalizer_le_normalizer_centralizer _)
  have hIF : M⊓Mc≤normalizer (F : Set G) :=
    normalizes_conjugateSpanBy E C (M⊓Mc) hIE (inf_le_right.trans hMcCN)
  have hMcF : Mc≤normalizer (F : Set G) := by
    intro m hm
    obtain ⟨a,ha,c,hc,rfl⟩ :=
      source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ Mc ⟨hMcC.1,hTMc⟩ m hm
    exact (normalizer (F : Set G)).mul_mem (hIF ⟨ha.2,ha.1⟩)
      ((le_normalizer_conjugateSpanBy E C) hc.2)
  exact ⟨hJE,hEA,hFA,IsElementaryAbelian.of_le hFA,hMcA,hMcF⟩


end CFSG.Quasithin.Chapter15.Section01
