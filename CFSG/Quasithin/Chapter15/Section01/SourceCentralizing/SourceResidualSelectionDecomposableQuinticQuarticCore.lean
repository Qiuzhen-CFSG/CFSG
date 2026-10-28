module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticCoreThompson
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionSwapCore
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.DecomposableFifteenSource.Core
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionQuarticReplacement
public import Theory.LinearAlgebra.OrderFourFixedLine
public import Theory.Representation.BinaryTwoPowerDegree
-- Internal proof split: reuse the original Sylow-pair and factor-fixed calculations.
import all CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Decomposable.Thompson

/-!
# Quartic support action in the actual partner core

A support-preserving core element whose square moves the first support
has order four in that support action. Its squared action is the unique
factor involution, of displacement rank two. The order-four fixed-line
calculation therefore makes its displacement have rank three. The actual
core contains this displacement, and the original support exchange gives
an eight-subgroup in each of the two separate support intersections.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
variable {G : Type*} [Group G] [Finite G]

private theorem quartic_support_displacement_rank
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (F : Factor ρ)
    (A B : Subgroup D) (hA : IsPGroup 2 A)
    (hAS : A≤subspaceStabilizer ρ F.space) (hBA : B≤A) (hBF : B≤F.actor)
    (hcB : Nat.card B=2) (hq : cubicRatio ρ=2)
    (hd : Module.finrank (ZMod 2) F.Space=4)
    (hdF : Module.finrank (ZMod 2) F.space=4)
    [IsCyclic (restrictedSubgroup ρ F.space A)]
    (q : A) (hq2 : (subgroupActionHom ρ F.space A hAS q)^2≠1) :
    Module.finrank (ZMod 2) (LinearMap.range
      (subspaceImageRepresentation ρ F.space (subgroupActionHom ρ F.space A hAS q)-1))=3 := by
  let f := subgroupActionHom ρ F.space A hAS
  let σ := subspaceImageRepresentation ρ F.space
  let x := f q
  let P := restrictedSubgroup ρ F.space A
  have hxP : x∈P := by
    change x∈restrictedSubgroup ρ F.space A
    rw [←subgroupActionHom_range ρ F.space A hAS]
    exact ⟨q,rfl⟩
  obtain ⟨n,hn⟩ := hA q
  have hx4 : x^4=1 := BinaryTwoPowerDegree.pow_eq_one_of_finrank_le σ
    (subspaceImageRepresentation_injective ρ F.space)
    (m:=2) (by rw [hdF]; decide) x (by rw [←map_pow,hn,map_one])
  obtain ⟨b,hbo⟩ := exists_prime_orderOf_dvd_card' (G:=B) 2 (by rw [hcB])
  have hb2 : (b:D)^2=1 := congrArg Subtype.val (hbo ▸ pow_orderOf_eq_one b)
  have hbne : (b:D)≠1 := by
    intro he
    have hh : b=1 := Subtype.ext he
    rw [hh,orderOf_one] at hbo
    contradiction
  have hbB : zpowers (b:D)=B := eq_of_le_of_card_ge (zpowers_le.mpr b.property) (by
    rw [Nat.card_zpowers,hcB]
    simpa only [orderOf_coe] using hbo.ge)
  let t := f ⟨b,hBA b.property⟩
  have htP : t∈P := by
    change t∈restrictedSubgroup ρ F.space A
    rw [←subgroupActionHom_range ρ F.space A hAS]
    exact ⟨⟨b,hBA b.property⟩,rfl⟩
  have ht2 : t^2=1 := by
    rw [←map_pow,show (⟨b,hBA b.property⟩:A)^2=1 from Subtype.ext hb2,map_one]
  have htne : t≠1 := by
    intro he
    have hfix : ∀v∈F.space,ρ (b:D) v=v := by
      intro v hv
      exact congrArg (fun a => (σ a ⟨v,hv⟩:W)) he
    obtain ⟨a,ha⟩ := hBF b.property
    have hfa : F.action a=1 := by
      ext v
      apply F.embedding.space_injective
      rw [F.embedding.equivariant,ha]
      exact hfix _ ⟨v,rfl⟩
    have ha1 : a=1 := F.faithful (hfa.trans F.action.map_one.symm)
    exact hbne (ha.symm.trans ((congrArg F.embedding.groupMap ha1).trans F.embedding.groupMap.map_one))
  have hsquare : x^2=t := by
    have hxs : orderOf (⟨x^2,P.pow_mem hxP 2⟩:P)=2 := by
      apply orderOf_eq_prime (Subtype.ext (by change (x^2)^2=1; rw [←pow_mul]; exact hx4))
      exact fun he => hq2 (congrArg P.subtype he)
    have hts : orderOf (⟨t,htP⟩:P)=2 :=
      orderOf_eq_prime (Subtype.ext ht2) (fun he => htne (congrArg P.subtype he))
    exact congrArg P.subtype (IsCyclic.eq_of_orderOf_eq_two hxs hts)
  let E := F.space⊓fixedSpace ρ B
  have hdimE : Module.finrank (ZMod 2) E=2 := factor_involution_fixed_dimension F B hBF hcB hq hd
  have hker : (σ t-1).ker=E.comap F.space.subtype := by
    ext v
    simp only [LinearMap.mem_ker,LinearMap.sub_apply,Module.End.one_apply,sub_eq_zero]
    change σ t v=v ↔ (v:W)∈E
    constructor
    · intro hv
      refine ⟨v.property,?_⟩
      rw [←hbB]
      apply (mem_fixedSpace_zpowers_iff ρ (b:D) (v:W)).mpr
      exact congrArg Subtype.val hv
    · intro hv
      apply Subtype.ext
      exact (mem_fixedSpace_zpowers_iff ρ (b:D) v).mp (hbB.symm ▸ hv.2)
  have hdimker : Module.finrank (ZMod 2) (σ t-1).ker=2 := by
    rw [hker,(Submodule.comapSubtypeEquivOfLe (show E≤F.space from inf_le_left)).finrank_eq,hdimE]
  have hdimx2 : Module.finrank (ZMod 2) ((σ x)^2-1).range=2 := by
    rw [←map_pow,hsquare]
    have hh := (σ t-1).finrank_range_add_finrank_ker
    rw [hdF,hdimker] at hh
    omega
  have hdimx := LinearMap.order_four_fixed_line hdF (σ x)
    (by rw [←map_pow,hx4,map_one])
    (by intro he; apply hq2; apply subspaceImageRepresentation_injective ρ F.space; simpa only [map_pow,map_one] using he)
    (by rw [hdimx2]; decide)
  change Module.finrank (ZMod 2) (LinearMap.range (σ x-1))=3
  have hh := (σ x-1).finrank_range_add_finrank_ker
  rw [hdF,hdimx] at hh
  omega

private theorem quartic_first_core_intersection
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T:Subgroup G)≤M) (hn : M≤normalizer (V:Set G))
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
    (Q : Subgroup G) (hQT : Q≤(T:Subgroup G)) (hVQ : V≤normalizer (Q:Set G))
    (q : G) (hqQ : q∈Q)
    (hqN : q∈normalizer (plane V (c.ambientFactor d s.first).space:Set G))
    (hq2 : q^2∉centralizer (plane V (c.ambientFactor d s.first).space:Set G)) :
    8≤Nat.card (Q⊓plane V (c.ambientFactor d s.first).space : Subgroup G) := by
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let f : M→*D := (actionHom M V hn).rangeRestrict
  let S : Sylow 2 D := (T.subtype hTM).mapSurjective (actionHom M V hn).rangeRestrict_surjective
  let F := c.ambientFactor d s.first
  let A : Subgroup D := (S:Subgroup D)⊓subspaceStabilizer ρ F.space
  let B : Subgroup D := (S:Subgroup D)⊓F.actor
  let q₀ : M := ⟨q,hTM (hQT hqQ)⟩
  have hqd : f q₀∈A := by
    refine ⟨mem_map_of_mem f (hQT hqQ),?_⟩
    apply (subspace_map_eq_iff ρ F.space _).mp
    apply plane_injective V
    exact (plane_conjugate hn F.space q₀).symm.trans (mem_normalizer_iff_map_conj_eq.mp hqN)
  have hFs : F.actor≤subspaceStabilizer ρ F.space := by
    apply le_subspaceStabilizer
    rintro a ⟨a,rfl⟩ v ⟨v,rfl⟩
    exact ⟨F.action a v,F.embedding.equivariant a v⟩
  let qA : A := ⟨f q₀,hqd⟩
  let g := subgroupActionHom ρ F.space A inf_le_right
  let σ := subspaceImageRepresentation ρ F.space
  have hqA2 : (g qA)^2≠1 := by
    intro he
    apply hq2
    rintro v ⟨w,hw,rfl⟩
    have hh := congrArg (fun x => (σ x ⟨Additive.ofMul w,hw⟩ : Additive V)) he
    have hfix : ρ (f (q₀^2)) (Additive.ofMul w)=Additive.ofMul w := by
      rw [map_pow,map_pow]
      exact hh
    have hh' := congrArg (fun v:Additive V => (v.toMul:G)) hfix
    change q^2*(w:G)*(q^2)⁻¹=(w:G) at hh'
    exact (mul_inv_eq_iff_eq_mul.mp hh').symm
  let : IsCyclic (restrictedSubgroup ρ F.space A) := quintic_support_two_cyclic F
    (c.support_stabilizer_normalizes_actor d π hp hs s.first) (s.marking s.first)
    (by change CyclicSource.DihedralMarking (s.marking s.first) 5 2; simpa only [hfive] using s.dihedral s.first)
    A S.isPGroup'.to_inf_left inf_le_right
  have hdims := (hdec.ratio_two_dimensions hq).2.choose_spec.2.2
  have hdF := hdims s.first
  obtain ⟨_,p,m,hpm,hmark,i,j,hij,hall,hgen,hdis,hcom,hcompl,_⟩ := hdec
  have hcard (k:d.Index) : Nat.card (c.ambientFactor d k).actor=2*p := by
    obtain ⟨l,hl⟩ := hmark k
    exact (Nat.card_range_of_injective (c.ambientFactor d k).embedding.group_injective).trans
      ((Nat.card_congr hl.dihedral.some.toEquiv).trans DihedralGroup.nat_card)
  have hpodd : Odd p := by
    rcases (CyclicSource.primeDimensionOptions_iff p m).mp hpm with ⟨rfl,_⟩|⟨rfl,_⟩ <;> decide
  have hnormal : ((c.ambientFactor d i).actor⊔(c.ambientFactor d j).actor).Normal := by
    rw [hgen]; exact Jhat_normal ρ
  obtain ⟨hBi,hBj,_⟩ := sylow_pair S _ _ hpodd (hcard i) (hcard j) hdis hcom hnormal
  have hBc : Nat.card B=2 := by
    rcases hall s.first with hi | hj
    · simpa only [B,F,hi] using hBi
    · simpa only [B,F,hj] using hBj
  have hr := quartic_support_displacement_rank ρ F A B S.isPGroup'.to_inf_left inf_le_right
    (le_inf inf_le_left (inf_le_right.trans hFs)) inf_le_right hBc hq hdF.1 hdF.2 qA hqA2
  let R := (LinearMap.range (σ (g qA)-1)).map F.space.subtype
  have hR3 : Module.finrank (ZMod 2) R=3 := by
    rw [Submodule.finrank_map_subtype_eq]
    exact hr
  have hR8 : Nat.card (plane V R)=8 := by rw [plane_card,hR3]; rfl
  have hm : ⁅Q,V⁆≤Q := le_normalizer_iff_commutator_le_left.mp hVQ
  have hRQ : plane V R≤Q⊓plane V F.space := by
    rintro x ⟨u,hu,rfl⟩
    obtain ⟨v,⟨w,rfl⟩,he⟩ := hu
    have he' : (((σ (g qA)-1) w).val.toMul)=u := congrArg Additive.toMul he
    rw [←he']
    refine ⟨?_,?_⟩
    · change ((q*(w.val.toMul:G)*q⁻¹)/(w.val.toMul:G))∈Q
      rw [div_eq_mul_inv]
      exact hm (commutator_mem_commutator hqQ w.val.toMul.property)
    · exact mem_map_of_mem V.subtype (show (σ (g qA) w-w:F.space).val∈F.space from
        (σ (g qA) w-w:F.space).property)
  exact hR8 ▸ card_le_of_le hRQ

/-- A support-preserving core element whose square is nontrivial on the
first support forces an eight-subgroup in each separate support intersection. -/
theorem PreparedChosenModule.decomposable_five_quartic_core_support_intersections
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
      ∀q∈Mc.pCoreIn 2,
        q∈normalizer (plane V (c.ambientFactor d s.first).space:Set G) →
        q^2∉centralizer (plane V (c.ambientFactor d s.first).space:Set G) →
        8≤Nat.card ((V⊓Mc.pCoreIn 2)⊓plane V (c.ambientFactor d s.first).space : Subgroup G) ∧
        8≤Nat.card ((V⊓Mc.pCoreIn 2)⊓plane V (c.ambientFactor d s.second).space : Subgroup G) := by
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive q hqQ hqN hq2
  let Q := Mc.pCoreIn 2
  let W := V⊓Q
  let V₁ := plane V (c.ambientFactor d s.first).space
  let V₂ := plane V (c.ambientFactor d s.second).space
  obtain ⟨hCMc,hcore,hQT,_,_,_,hUE,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu hfull c d hd s π hp hs hdec hq hfive
  have hQT' : Q≤(T:Subgroup G) := by
    change Mc.pCoreIn 2≤(T:Subgroup G)
    rw [←hcore]
    exact hQT
  have hVC : V≤centralizer (localModule T Mc:Set G) :=
    V.le_centralizer.trans (centralizer_le ((hUE.trans inf_le_left).trans inf_le_left))
  have hQN : Mc≤normalizer (Q:Set G) := Mc.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))
  have hVQ : V≤normalizer (Q:Set G) := hVC.trans (hCMc.trans hQN)
  have h₁ := quartic_first_core_intersection hM.1.2 h.normalized c d s π hp hs hdec hq hfive
    Q hQT' hVQ q hqQ hqN hq2
  have he₁ : W⊓V₁=Q⊓V₁ := by
    change (V⊓Q)⊓V₁=Q⊓V₁
    rw [inf_right_comm,inf_eq_right.mpr (plane_le _)]
    exact inf_comm _ _
  have hc₁ : 8≤Nat.card (W⊓V₁ : Subgroup G) := he₁.symm ▸ h₁
  have hMcC : Mc∈maximalTwoLocalOvergroups (centralizer (centralInvolutions T:Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T:Subgroup G)≤Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  have hTW : (T:Subgroup G)≤normalizer (W:Set G) :=
    (le_inf (hM.1.2.trans h.normalized) (hTMc.trans hQN)).trans inf_normalizer_le_normalizer_inf
  let S₀ := (T:Subgroup G)⊓normalizer (V₁:Set G)
  have hSne : S₀≠(T:Subgroup G) := by
    intro he
    have hi : S₀.relIndex (T:Subgroup G)=2 := s.stabilizer_index
    rw [he,relIndex_self] at hi
    omega
  obtain ⟨t,ht,htS⟩ := SetLike.exists_of_lt (lt_of_le_of_ne (show S₀≤(T:Subgroup G) from inf_le_left) hSne)
  have htex : V₁.map (MulAut.conj t).toMonoidHom=V₂ :=
    (s.exchanges t ht (fun hh => htS ⟨ht,hh⟩)).1
  have hWmap : W.map (MulAut.conj t).toMonoidHom=W := mem_normalizer_iff_map_conj_eq.mp (hTW ht)
  have hmap : (W⊓V₁).map (MulAut.conj t).toMonoidHom=W⊓V₂ := by
    rw [map_inf _ _ _ (MulAut.conj t).injective,
      hWmap,htex]
  have hc₂ : 8≤Nat.card (W⊓V₂ : Subgroup G) := by
    rw [←hmap,card_map_of_injective (MulAut.conj t).injective]
    exact hc₁
  exact ⟨hc₁,hc₂⟩

private theorem elementary_support_action_index
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T:Subgroup G)≤M) (hn : M≤normalizer (V:Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T:=T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀g k,(c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom=
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀g k,(c.ambientFactor d k).space.map (imageRepresentation M V hn g)=
      (c.ambientFactor d (π g k)).space)
    (hfive : s.prime=5) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAT : A≤(T:Subgroup G)) (k:d.Index)
    (hAN : A≤normalizer (plane V (c.ambientFactor d k).space:Set G)) :
    (centralizer (plane V (c.ambientFactor d k).space:Set G)).relIndex A≤2 := by
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let f : M→*D := (actionHom M V hn).rangeRestrict
  let S : Sylow 2 D := (T.subtype hTM).mapSurjective (actionHom M V hn).rangeRestrict_surjective
  let F := c.ambientFactor d k
  let B : Subgroup D := (S:Subgroup D)⊓subspaceStabilizer ρ F.space
  have haB (a:A) : f ⟨a,hTM (hAT a.property)⟩∈B := by
    refine ⟨mem_map_of_mem f (hAT a.property),?_⟩
    apply (subspace_map_eq_iff ρ F.space _).mp
    apply plane_injective V
    exact (plane_conjugate hn F.space ⟨a,hTM (hAT a.property)⟩).symm.trans
      (mem_normalizer_iff_map_conj_eq.mp (hAN a.property))
  let γ : A→*B := {
    toFun := fun a => ⟨f ⟨a,hTM (hAT a.property)⟩,haB a⟩
    map_one' := Subtype.ext f.map_one
    map_mul' := fun a b => Subtype.ext
      (f.map_mul ⟨a,hTM (hAT a.property)⟩ ⟨b,hTM (hAT b.property)⟩) }
  let g₀ := subgroupActionHom ρ F.space B inf_le_right
  let g := g₀.comp γ
  let σ := subspaceImageRepresentation ρ F.space
  let P := restrictedSubgroup ρ F.space B
  let : IsCyclic P := quintic_support_two_cyclic F
    (c.support_stabilizer_normalizes_actor d π hp hs k) (s.marking k)
    (by change CyclicSource.DihedralMarking (s.marking k) 5 2; simpa only [hfive] using s.dihedral k)
    B S.isPGroup'.to_inf_left inf_le_right
  have hgle : g.range≤P := by
    rintro x ⟨a,rfl⟩
    change g a∈restrictedSubgroup ρ F.space B
    rw [←subgroupActionHom_range ρ F.space B inf_le_right]
    exact ⟨γ a,rfl⟩
  let : IsCyclic g.range := isCyclic_of_injective (inclusion hgle) (inclusion_injective hgle)
  let : IsElementaryAbelian 2 g.range := IsElementaryAbelian.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  have hcard : Nat.card g.range≤2 := Nat.le_of_dvd (by decide) (by
    have hh := IsElementaryAbelian.exponent_dvd_p 2 g.range
    rwa [IsCyclic.exponent_eq_card] at hh)
  have hk : g.ker=(centralizer (plane V F.space:Set G)).subgroupOf A := by
    ext a
    constructor
    · intro ha
      rintro v ⟨w,hw,rfl⟩
      have hh := congrArg (fun x => (σ x ⟨Additive.ofMul w,hw⟩ : Additive V)) ha
      have he := congrArg (fun v:Additive V => (v.toMul:G)) hh
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro ha
      apply subspaceImageRepresentation_injective ρ F.space
      ext v
      change (a:G)*(v.val.toMul:G)*(a:G)⁻¹=(v.val.toMul:G)
      have hc : (v.val.toMul:G)*(a:G)=(a:G)*(v.val.toMul:G) :=
        ha _ (mem_map_of_mem V.subtype v.property)
      rw [←hc,mul_inv_cancel_right]
  have he : Nat.card g.range=(centralizer (plane V F.space:Set G)).relIndex A := by
    rw [←index_ker,hk]
    rfl
  exact he ▸ hcard

/-- Genuine order-four action on either preserved support forces the
whole original module into the actual partner two-core. -/
theorem PreparedChosenModule.decomposable_five_partner_core_quartic_forces_module
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
      ∀q∈Mc.pCoreIn 2,
        q∈normalizer (plane V (c.ambientFactor d s.first).space : Set G) →
        q^2∉centralizer (plane V (c.ambientFactor d s.first).space : Set G) →
        V≤Mc.pCoreIn 2 := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive q hqQ hqN hq2
  let V := localModule T M
  let Uc := localModule T Mc
  let E := thompsonFixed T V
  let C := centralizer (Uc : Set G)
  let Q := C.pCoreIn 2
  let J := elementaryAbelianMaxJ Q
  let F := conjugateSpanBy E C
  let W := V⊓Q
  let V₁ := plane V (c.ambientFactor d s.first).space
  let V₂ := plane V (c.ambientFactor d s.second).space
  obtain ⟨hCMc,hcore,hQT,_,hself,_,hUE,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive
  obtain ⟨hJE,_,hFA,hFel,_,hMcF⟩ := h.decomposable_five_partner_fixed_envelope
    hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive
  have hJQ : J≤Q := sSup_le fun _ hA => hA.1
  have hFJ : F≤J := by
    intro f hf
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp (hFA hf)).1
  have hFC : F≤centralizer (J:Set G) := by
    intro f hf
    exact mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff _ _).mp (hFA hf)).2.2
  have hVC : V≤C := V.le_centralizer.trans (centralizer_le ((hUE.trans inf_le_left).trans inf_le_left))
  have hCQ : C≤normalizer (Q:Set G) := C.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hVQ : V≤normalizer (Q:Set G) := hVC.trans hCQ
  have hQV : Q≤normalizer (V:Set G) := hQT.trans (hM.1.2.trans h.normalized)
  have hmove : ⁅Q,V⁆≤W := le_inf
    (le_normalizer_iff_commutator_le_right.mp hQV)
    (le_normalizer_iff_commutator_le_left.mp hVQ)
  have hqQ' : q∈Q := by
    change q∈(centralizer (localModule T Mc : Set G)).pCoreIn 2
    rw [hcore]
    exact hqQ
  obtain ⟨hc₁,hc₂⟩ := h.decomposable_five_quartic_core_support_intersections
    hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive q hqQ hqN hq2
  rw [←hcore] at hc₁ hc₂
  have hact (A:Subgroup G) (hA:A∈elementaryAbelianMaxSubgroups Q) :
      A≤normalizer (W:Set G) ∧ A≤normalizer (V₁:Set G) ∧ A≤normalizer (V₂:Set G) ∧
      (centralizer (V₁:Set G)).relIndex A≤2 ∧ (centralizer (V₂:Set G)).relIndex A≤2 ∧
      (¬A≤centralizer (V₁:Set G) → Nat.card (V₁⊓centralizer (A:Set G) : Subgroup G)≤4) ∧
      (¬A≤centralizer (V₂:Set G) → Nat.card (V₂⊓centralizer (A:Set G) : Subgroup G)≤4) := by
    let : IsElementaryAbelian 2 A := hA.2.1
    have hAJ : A≤J := le_sSup hA
    have hAT : A≤(T:Subgroup G) := hA.1.trans hQT
    have hAN : A≤normalizer (V₁:Set G) := by
      intro a ha
      exact s.centralizer_le_stabilizer ⟨hAT ha,
        (hAJ.trans hJE |>.trans (centralizer_le (show thompsonPlane T V
          (c.ambientFactor d s.first).space≤E from inf_le_right))) ha⟩
    have hAN₂ : A≤normalizer (V₂:Set G) := fun a ha => s.stabilizes_second ⟨hAT ha,hAN ha⟩
    have hAW : A≤normalizer (W:Set G) :=
      (le_inf (hA.1.trans hQV) (hA.1.trans Q.le_normalizer)).trans inf_normalizer_le_normalizer_inf
    have hfix (k:d.Index) (hnA:¬A≤centralizer (plane V (c.ambientFactor d k).space:Set G)) :
        Nat.card (plane V (c.ambientFactor d k).space⊓centralizer (A:Set G) : Subgroup G)≤4 := by
      obtain ⟨a,ha,hac⟩ := Set.not_subset.mp hnA
      have hh := (s.involution_support_displacement_and_fixed hM.1.2 h.normalized c d π hp hs
        hfive a (hAT ha) (elemPow_eq_one_of_isElementaryAbelian (p:=2) a ha) (hAN ha) k).1.resolve_left hac
      exact (card_le_of_le ((inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr ha))).trans hh)).trans_eq
        (s.thompson_card k)
    exact ⟨hAW,hAN,hAN₂,
      elementary_support_action_index hM.1.2 h.normalized c d s π hp hs hfive A hAT s.first hAN,
      elementary_support_action_index hM.1.2 h.normalized c d s π hp hs hfive A hAT s.second hAN₂,
      hfix s.first,hfix s.second⟩
  have hFfixed (f:G) (hf:f∈F) :
      (f∉centralizer (V₁:Set G) → Nat.card (V₁⊓centralizer ({f}:Set G) : Subgroup G)≤4) ∧
      (f∉centralizer (V₂:Set G) → Nat.card (V₂⊓centralizer ({f}:Set G) : Subgroup G)≤4) := by
    let : IsElementaryAbelian 2 F := hFel
    have hfT := hQT (hJQ (hFJ hf))
    have hfN : f∈normalizer (V₁:Set G) := s.centralizer_le_stabilizer
      ⟨hfT,(hFJ.trans hJE |>.trans (centralizer_le (show thompsonPlane T V
        (c.ambientFactor d s.first).space≤E from inf_le_right))) hf⟩
    have hh (k:d.Index) (hn:f∉centralizer (plane V (c.ambientFactor d k).space:Set G)) :
        Nat.card (plane V (c.ambientFactor d k).space⊓centralizer ({f}:Set G) : Subgroup G)≤4 := by
      have hfix := (s.involution_support_displacement_and_fixed hM.1.2 h.normalized c d π hp hs
        hfive f hfT (elemPow_eq_one_of_isElementaryAbelian (p:=2) f hf) hfN k).1.resolve_left hn
      exact (card_le_of_le hfix).trans_eq (s.thompson_card k)
    exact ⟨hh s.first,hh s.second⟩
  obtain ⟨hWJ,hFV⟩ := maxJ_envelope_centralizes_of_large_support_intersections
    Q V W V₁ V₂ F inf_le_left inf_le_right s.complement (disjoint_iff.mpr s.disjoint)
    hc₁ hc₂ hFC hact hFfixed
  have hJV : ⁅J,V⁆≤E :=
    (commutator_mono (le_inf (hJQ.trans hQT) hJE) le_rfl).trans
      (h.decomposable_five_fixed_centralizer_displacement
        hG T hempty hM hmany hJ rfl c d hd s π hp hs hdec hq hfive)
  have hEF : E≤F := le_conjugateSpanBy E C
  have hVcore : V≤Q := le_twoCore_of_relative_three_step_chain C Q J F V
    (pCoreIn_le 2 C) (hJQ.trans (pCoreIn_le 2 C)) (hFJ.trans (hJQ.trans (pCoreIn_le 2 C)))
    hVC hCQ (hCQ.trans (normalizer_le_normalizer_elementaryAbelianMaxJ Q))
    (hCMc.trans hMcF) (isPGroup_pCoreIn 2 C) hself
    (le_centralizer_iff.mp hFV)
    (by rw [commutator_comm]; exact hJV.trans hEF)
    (by rw [commutator_comm]; exact hmove.trans hWJ)
  exact hVcore.trans_eq hcore


end CFSG.Quasithin.Chapter15.Section01
