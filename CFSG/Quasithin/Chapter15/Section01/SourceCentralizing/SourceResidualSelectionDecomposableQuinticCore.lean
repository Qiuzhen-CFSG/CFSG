module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionDecomposableQuinticSelectionCore
public import Theory.Representation.SmallBinaryFiveOvergroup
public import Theory.Representation.BinaryOffender.DihedralProductDisplacement
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# The actual quintic fixed subgroup lies in the partner core

A nontrivial normal subgroup of the literal Sylow image contains a central
involution. Cyclicity of the Sylow action on a quintic support identifies
its two restrictions with the two factor involutions. Its displacement is
exactly the original Thompson fixed subgroup. Apply this to the image of
the partner two-core. If that image is trivial, characteristic two puts
the whole original module in the core instead.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.RatioDecomposition DecomposableMarker
universe u
variable {G : Type*} [Group G] [Finite G]

private theorem normal_two_contains_central_involution
    {D : Type*} [Group D] [Finite D] (S : Subgroup D) (hS : IsPGroup 2 S)
    (B : Subgroup D) (hBS : B≤S) (hn : S≤normalizer (B : Set D)) (hne : B≠⊥) :
    ∃ z∈B, orderOf z=2 ∧ z∈centralizer (S : Set D) := by
  let N := B.subgroupOf S
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  have hN : N≠⊥ := by
    intro he
    have hh := congrArg (map S.subtype) he
    rw [map_subgroupOf_eq_of_le hBS,Subgroup.map_bot] at hh
    exact hne hh
  have hI := center_inf_ne_bot_of_normal hS N hN
  let I := center S⊓N
  obtain ⟨x,hx,hx1⟩ := I.bot_or_exists_ne_one.resolve_left hI
  let z := x^(orderOf x/2)
  have hz : orderOf z=2 := orderOf_pow_orderOf_div (Nat.ne_of_gt (orderOf_pos x))
    (hS.dvd_orderOf hx1)
  have hmem : z∈I := I.pow_mem hx _
  refine ⟨z,hmem.2,by simpa only [orderOf_coe] using hz,?_⟩
  intro y hy
  exact congrArg Subtype.val (mem_center_iff.mp hmem.1 ⟨y,hy⟩)

/-- The actual normal quintic support has cyclic two-subgroup actions. -/
theorem DecomposableMarker.quintic_support_two_cyclic
    {D W : Type u} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} (F : Factor ρ)
    (hN : subspaceStabilizer ρ F.space≤normalizer (F.actor : Set D))
    (l : CyclicSource.LocalGeneration F.action) (hm : CyclicSource.DihedralMarking l 5 2)
    (A : Subgroup D) (hA : IsPGroup 2 A) (hAS : A≤subspaceStabilizer ρ F.space) :
    IsCyclic (restrictedSubgroup ρ F.space A) := by
  obtain ⟨k,J,hk,_,_,hn,_⟩ := F.faithful_normal_support_image_data hN
  let H := k.range
  let : H.Normal := hn
  let : FiniteDimensional (ZMod 2) F.space := Module.Finite.of_surjective J.toLinearMap J.surjective
  let e : F.Carrier ≃* H := MonoidHom.ofInjective hk
  let P := (pResidual 2 H).map H.subtype
  have hP : Nat.card P=5 := by
    rw [card_map_of_injective H.subtype_injective,
      ←map_pResidual_of_surjective 2 e.toMonoidHom e.surjective,
      card_map_of_injective (f:=e.toMonoidHom) e.injective,←l.kernel_eq_twoResidual]
    exact hm.card_kernel
  exact (SmallBinaryFiveOvergroup.two_subgroup
    (subspaceImageRepresentation ρ F.space) (subspaceImageRepresentation_injective ρ F.space)
    (J.finrank_eq.symm.trans hm.dimension) P hP _ (by
      rw [←subgroupActionHom_range ρ F.space A hAS]
      exact hA.of_surjective _ (subgroupActionHom ρ F.space A hAS).rangeRestrict_surjective)).1

omit [Finite G] in
private theorem factor_actor_faithful
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} (F : Factor ρ)
    {a : D} (ha : a∈F.actor) (hfix : ∀v∈F.space,ρ a v=v) : a=1 := by
  obtain ⟨a,rfl⟩ := ha
  have hh : F.action a=1 := by
    ext v
    apply F.embedding.space_injective
    exact (F.embedding.equivariant a v).trans (hfix _ ⟨v,rfl⟩)
  rw [F.faithful (hh.trans F.action.map_one.symm),map_one]

omit [Finite G] in
private theorem factor_actor_stabilizes
    {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
    {ρ : Representation (ZMod 2) D W} (F : Factor ρ) :
    F.actor≤subspaceStabilizer ρ F.space := by
  apply le_subspaceStabilizer
  rintro a ⟨a,rfl⟩ v ⟨v,rfl⟩
  exact ⟨F.action a v,F.embedding.equivariant a v⟩

private theorem central_involution_factor_product
    {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (S : Sylow 2 D) (F H : Factor ρ)
    (hcF : Nat.card F.actor=10) (hd : Disjoint F.actor H.actor)
    (hcom : ∀a∈F.actor,∀b∈H.actor,Commute a b) (hn : (F.actor⊔H.actor).Normal)
    (hcompl : IsCompl F.space H.space)
    (hcross : H.space≤fixedSpace ρ F.actor)
    (hcross' : F.space≤fixedSpace ρ H.actor)
    (hp : ∀g∈(S:Subgroup D),
      (F.actor.map (MulAut.conj g).toMonoidHom=F.actor ∧ F.space.map (ρ g)=F.space) ∨
      (F.actor.map (MulAut.conj g).toMonoidHom=H.actor ∧ F.space.map (ρ g)=H.space))
    (hcyc : ∀A:Subgroup D,IsPGroup 2 A→A≤subspaceStabilizer ρ F.space→
      IsCyclic (restrictedSubgroup ρ F.space A))
    (t : D) (ht : t∈(S:Subgroup D))
    (htF : F.actor.map (MulAut.conj t).toMonoidHom=H.actor)
    (htW : F.space.map (ρ t)=H.space)
    (hq : cubicRatio ρ=2)
    (z : D) (hzS : z∈(S:Subgroup D)) (hz : orderOf z=2)
    (hzC : z∈centralizer (S:Set D)) :
    z∈F.actor⊔H.actor ∧ 4≤Module.finrank (ZMod 2) (LinearMap.range (ρ z-1)) := by
  have hRL : H.actor≤normalizer (F.actor:Set D) :=
    (show H.actor≤centralizer (F.actor:Set D) from
      fun b hb a ha => (hcom a ha b hb).eq).trans (Subgroup.centralizer_le_normalizer _)
  have hFn : (F.actor.subgroupOf (F.actor⊔H.actor)).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le F.actor.le_normalizer hRL)
  have hFs : F.actor.IsSubnormal := Subgroup.IsSubnormal.trans le_sup_left hFn.isSubnormal hn.isSubnormal
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal F.actor hFs
  have hcSF : Nat.card ((S:Subgroup D)⊓F.actor : Subgroup D)=2 := by
    have hh := P.card_eq_multiplicity
    rw [hcF] at hh
    rw [show 2 ^ Nat.factorization 10 2 = 2 by decide +kernel] at hh
    rw [hP] at hh
    rw [←map_subgroupOf_eq_of_le (show (S:Subgroup D)⊓F.actor≤F.actor from inf_le_right)]
    simpa only [inf_subgroupOf_right,card_map_of_injective F.actor.subtype_injective] using hh
  obtain ⟨a,hao⟩ := exists_prime_orderOf_dvd_card' (G:=((S:Subgroup D)⊓F.actor : Subgroup D)) 2
    (by rw [hcSF])
  have haoD : orderOf (a:D)=2 := by simpa only [orderOf_coe] using hao
  have haS : (a:D)∈(S:Subgroup D) := a.property.1
  have haF : (a:D)∈F.actor := a.property.2
  have ha2 : (a:D)^2=1 := congrArg Subtype.val (hao ▸ pow_orderOf_eq_one a)
  have ha1 : (a:D)≠1 := by
    intro he
    have hh : a=1 := Subtype.ext he
    rw [hh,orderOf_one] at hao
    contradiction
  have hzstab : z∈subspaceStabilizer ρ F.space := by
    rcases hp z hzS with hp | hp
    · exact (subspace_map_eq_iff ρ F.space z).mp hp.2
    · have he : z*(a:D)*z⁻¹=a := by rw [←hzC a haS,mul_inv_cancel_right]
      have hh := mem_map_of_mem (MulAut.conj z).toMonoidHom haF
      rw [hp.1] at hh
      change z*(a:D)*z⁻¹∈H.actor at hh
      rw [he] at hh
      exact (ha1 (disjoint_def.mp hd haF hh)).elim
  let S₀ := (S:Subgroup D)⊓subspaceStabilizer ρ F.space
  let f := subgroupActionHom ρ F.space S₀ inf_le_right
  let a₀ : S₀ := ⟨a,haS,factor_actor_stabilizes F haF⟩
  let z₀ : S₀ := ⟨z,hzS,hzstab⟩
  let : IsCyclic (restrictedSubgroup ρ F.space S₀) := hcyc S₀ S.isPGroup'.to_inf_left inf_le_right
  have hfa : f a₀≠1 := by
    intro he
    apply ha1
    apply factor_actor_faithful F haF
    intro v hv
    have hh := congrArg (fun x => (subspaceImageRepresentation ρ F.space x ⟨v,hv⟩:W)) he
    exact hh
  have hza : ∀v∈F.space,ρ z v=ρ a v := by
    have hfz : f z₀≠1 := by
      intro he
      have hfix : ∀v∈F.space,ρ z v=v := by
        intro v hv
        exact congrArg (fun x => (subspaceImageRepresentation ρ F.space x ⟨v,hv⟩:W)) he
      have hfixH : ∀v∈H.space,ρ z v=v := by
        intro v hv
        rw [←htW] at hv
        obtain ⟨u,hu,rfl⟩ := hv
        rw [←Module.End.mul_apply,←map_mul,←hzC t ht,map_mul,Module.End.mul_apply,hfix u hu]
      have hez : ρ z=ρ 1 := by
        ext v
        obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp (hcompl.sup_eq_top.ge (Submodule.mem_top (x := v)))
        rw [map_add,hfix u hu,hfixH w hw,map_one,Module.End.one_apply]
      have hzz : z=1 := hf hez
      rw [hzz,orderOf_one] at hz
      contradiction
    let ar : restrictedSubgroup ρ F.space S₀ := ⟨f a₀,(subgroupActionHom_range ρ F.space S₀ inf_le_right) ▸ ⟨a₀,rfl⟩⟩
    let zr : restrictedSubgroup ρ F.space S₀ := ⟨f z₀,(subgroupActionHom_range ρ F.space S₀ inf_le_right) ▸ ⟨z₀,rfl⟩⟩
    have har : orderOf ar=2 := orderOf_eq_prime (Subtype.ext (by
      change f a₀^2=1
      rw [←map_pow,show a₀^2=1 from Subtype.ext ha2,map_one]))
      (fun he => hfa (congrArg Subtype.val he))
    have hzr : orderOf zr=2 := orderOf_eq_prime (Subtype.ext (by
      change f z₀^2=1
      rw [←map_pow,show z₀^2=1 from Subtype.ext (hz ▸ pow_orderOf_eq_one z),map_one]))
      (fun he => hfz (congrArg Subtype.val he))
    have he := congrArg Subtype.val (IsCyclic.eq_of_orderOf_eq_two hzr har)
    intro v hv
    exact congrArg (fun x => (subspaceImageRepresentation ρ F.space x ⟨v,hv⟩:W)) he
  let b := t*(a:D)*t⁻¹
  have hbH : b∈H.actor := htF ▸ mem_map_of_mem (MulAut.conj t).toMonoidHom haF
  have hb2 : orderOf b=2 := by
    change orderOf (MulAut.conj t (a:D))=2
    rw [(MulAut.conj t).orderOf_eq,haoD]
  have hzb : ∀v∈H.space,ρ z v=ρ b v := by
    intro v hv
    rw [←htW] at hv
    obtain ⟨u,hu,rfl⟩ := hv
    have hbt : b*t=t*(a:D) := by dsimp [b]; group
    rw [←Module.End.mul_apply,←map_mul,←hzC t ht,map_mul,Module.End.mul_apply,hza u hu,
      ←Module.End.mul_apply,←map_mul,←hbt,map_mul,Module.End.mul_apply]
  have he : z=(a:D)*b := by
    apply hf
    ext v
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp (hcompl.sup_eq_top.ge (Submodule.mem_top (x := v)))
    rw [map_add,hza u hu,hzb w hw]
    rw [show ρ ((a:D)*b)=ρ a*ρ b from map_mul ρ (a:D) b]
    change ρ a u + ρ b w = ρ a (ρ b (u+w))
    have hbu : ρ b u=u := hcross' hu ⟨b,hbH⟩
    rw [map_add,map_add,hbu]
    have hbw : ρ b w∈H.space := (factor_actor_stabilizes H hbH w).mpr hw
    have haw : ρ a (ρ b w)=ρ b w := hcross hbw ⟨a,haF⟩
    rw [haw]
  refine ⟨he ▸ mul_mem_sup haF hbH,?_⟩
  have hlo (x:D) (hx:orderOf x=2) :
      2≤Module.finrank (ZMod 2) (LinearMap.range (ρ x-LinearMap.id)) := by
    obtain ⟨hel,hr,hquad,_⟩ := involution_actor_rank_and_fixedCodim ρ x hx
    have hh : cubicRatio ρ≤actionRatio ρ (zpowers x) :=
      iInf_le_of_le _ (iInf_le_of_le ⟨hel,isCubic_of_isQuadratic hquad⟩ le_rfl)
    rw [hq,actionRatio,hr,Nat.cast_one,div_one] at hh
    have hn : 2≤fixedCodim ρ (zpowers x) := by exact_mod_cast hh
    rwa [fixedCodim_zpowers_eq_displacement_rank] at hn
  have haRank := hlo a haoD
  have hbRank := hlo b hb2
  have hmove := displacement_rank_product_of_fixed_supplement ρ F.actor H.actor hcom
    (by rw [←F.space_eq_support,←H.space_eq_support]; exact hcompl.disjoint)
    (by rw [←F.space_eq_support,←H.space_eq_support,hcompl.sup_eq_top,top_sup_eq]) haF hbH
  rw [←he] at hmove
  change 4≤Module.finrank (ZMod 2) (LinearMap.range (ρ z-LinearMap.id))
  omega

private theorem thompson_central_involution_displacement
    {T : Sylow 2 G} {M V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    {U : Submodule (ZMod 2) (Additive V)}
    (c : FactorData (imageRepresentation M V hn) (Jhat (imageRepresentation M V hn)) U)
    (d : Decomposition c.representation) (s : ThompsonPair (T := T) hn c d)
    (π : internalActionImage M V hn →* Equiv.Perm d.Index)
    (hp : ∀ g k, (c.ambientFactor d k).actor.map (MulAut.conj g).toMonoidHom =
      (c.ambientFactor d (π g k)).actor)
    (hs : ∀ g k, (c.ambientFactor d k).space.map (imageRepresentation M V hn g) =
      (c.ambientFactor d (π g k)).space)
    (hdec : SourceCases.Decomposable (imageRepresentation M V hn) (T : Subgroup G) M
      (actionHom M V hn).rangeRestrict c d π)
    (hq : cubicRatio (imageRepresentation M V hn)=2) (hfive : s.prime=5)
    (hJi : ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
        (actionHom M V hn).rangeRestrict =
      ((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict ⊓
        Jhat (imageRepresentation M V hn))
    (z : internalActionImage M V hn)
    (hzS : z∈((T : Subgroup G).subgroupOf M).map (actionHom M V hn).rangeRestrict)
    (hz : orderOf z=2)
    (hzC : z∈centralizer ((((T : Subgroup G).subgroupOf M).map
      (actionHom M V hn).rangeRestrict : Subgroup (internalActionImage M V hn)) :
        Set (internalActionImage M V hn))) :
    plane V (LinearMap.range (imageRepresentation M V hn z-LinearMap.id)) =
      thompsonFixed T V := by
  let D := internalActionImage M V hn
  let ρ := imageRepresentation M V hn
  let f : M →* D := (actionHom M V hn).rangeRestrict
  let S : Sylow 2 D := (T.subtype hTM).mapSurjective (actionHom M V hn).rangeRestrict_surjective
  have hdim := (hdec.ratio_two_dimensions hq).1
  obtain ⟨_,_,_,_,_,i,j,hij,hall,hgen,hdis,hcom,hcompl,t,ht,htij,_⟩ := hdec
  have emark (k : d.Index) : (c.ambientFactor d k).actor ≃* DihedralGroup 5 := by
    have hm := (s.dihedral k).dihedral
    rw [hfive] at hm
    exact (MonoidHom.ofInjective (c.ambientFactor d k).embedding.group_injective).symm.trans hm.some
  have hnormal : ((c.ambientFactor d i).actor ⊔ (c.ambientFactor d j).actor).Normal := by
    rw [hgen]; exact Jhat_normal ρ
  have hcyc (A : Subgroup D) (hA : IsPGroup 2 A)
      (hAS : A≤subspaceStabilizer ρ (c.ambientFactor d i).space) :
      IsCyclic (restrictedSubgroup ρ (c.ambientFactor d i).space A) := by
    apply quintic_support_two_cyclic (c.ambientFactor d i)
      (c.support_stabilizer_normalizes_actor d π hp hs i) (s.marking i) _ A hA hAS
    change CyclicSource.DihedralMarking (s.marking i) 5 2
    simpa only [hfive] using s.dihedral i
  have hperm (g : D) (_hg : g∈(S:Subgroup D)) :
      ((c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom=(c.ambientFactor d i).actor ∧
        (c.ambientFactor d i).space.map (ρ g)=(c.ambientFactor d i).space) ∨
      ((c.ambientFactor d i).actor.map (MulAut.conj g).toMonoidHom=(c.ambientFactor d j).actor ∧
        (c.ambientFactor d i).space.map (ρ g)=(c.ambientFactor d j).space) := by
    rcases hall (π g i) with hi | hj
    · exact Or.inl ⟨(hp g i).trans (congrArg (fun k => (c.ambientFactor d k).actor) hi),
        (hs g i).trans (congrArg (fun k => (c.ambientFactor d k).space) hi)⟩
    · exact Or.inr ⟨(hp g i).trans (congrArg (fun k => (c.ambientFactor d k).actor) hj),
        (hs g i).trans (congrArg (fun k => (c.ambientFactor d k).space) hj)⟩
  obtain ⟨hzin,hrank⟩ := central_involution_factor_product ρ (imageRepresentation_injective M V hn)
    S (c.ambientFactor d i) (c.ambientFactor d j)
    ((Nat.card_congr (emark i).toEquiv).trans (by rw [DihedralGroup.nat_card]))
    hdis hcom hnormal hcompl (c.ambient_cross d hij.symm) (c.ambient_cross d hij)
    hperm hcyc (f t) (mem_map_of_mem f ht)
    ((hp (f t) i).trans (congrArg (fun k => (c.ambientFactor d k).actor) htij))
    ((hs (f t) i).trans (congrArg (fun k => (c.ambientFactor d k).space) htij)) hq z hzS hz hzC
  rw [hgen] at hzin
  let J : Subgroup D := ((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map f
  let C := fixedSpace ρ J
  have hE : plane V C=thompsonFixed T V := plane_thompson_image hTM hn
  have hC4 : Module.finrank (ZMod 2) C=4 := by
    apply Nat.pow_right_injective (by decide : 1<2)
    change 2^Module.finrank (ZMod 2) C=16
    rw [←plane_card,hE,s.fixed_card]
  have hzJ : z∈J := by
    change z∈((ChapterB.thompsonJ (T:Subgroup G) 1).subgroupOf M).map (actionHom M V hn).rangeRestrict
    rw [hJi]
    exact ⟨hzS,hzin⟩
  have hCz : C≤fixedSpace ρ (zpowers z) := by
    intro v hv
    rw [mem_fixedSpace_zpowers_iff]
    exact hv ⟨z,hzJ⟩
  change 4≤Module.finrank (ZMod 2) (LinearMap.range (ρ z-LinearMap.id)) at hrank
  have hCzdim := Submodule.finrank_mono hCz
  have hdimz := fixedCodim_add_finrank ρ (zpowers z)
  rw [fixedCodim_zpowers_eq_displacement_rank,hdim] at hdimz
  change Module.finrank (ZMod 2) (LinearMap.range (ρ z-LinearMap.id)) +
    Module.finrank (ZMod 2) (fixedSpace ρ (zpowers z)) = 8 at hdimz
  have hfix : C=fixedSpace ρ (zpowers z) :=
    Submodule.eq_of_le_of_finrank_eq hCz (by omega)
  have hrle : LinearMap.range (ρ z-LinearMap.id)≤C := by
    rw [hfix]
    rintro _ ⟨v,rfl⟩
    rw [mem_fixedSpace_zpowers_iff]
    have hz2 : z^2=1 := hz ▸ pow_orderOf_eq_one z
    exact involution_fixes_displacement ρ (by simpa only [pow_two] using hz2) v
  have he : LinearMap.range (ρ z-LinearMap.id)=C :=
    Submodule.eq_of_le_of_finrank_eq hrle (by
      have hh := Submodule.finrank_mono hrle
      omega)
  exact (congrArg (plane V) he).trans hE

/-- The original prime-five Thompson fixed subgroup lies in the actual
partner two-core, with no residual or module-cardinality assumption. -/
theorem PreparedChosenModule.decomposable_five_fixed_le_partner_core
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
      thompsonFixed T V ≤ Mc.pCoreIn 2 := by
  subst V
  let := h.elementary
  intro U c d hd s π hp hs hdec hq hfive
  let V := localModule T M
  let E := thompsonFixed T V
  let C := centralizer (localModule T Mc : Set G)
  let Q := C.pCoreIn 2
  obtain ⟨hCMc,hQMc,hQT,_,hself,hEC,hUE,_⟩ := h.decomposable_five_partner_kernel_core
    hG T hempty hM hmany hJ hu rfl c d hd s π hp hs hdec hq hfive
  change Q=Mc.pCoreIn 2 at hQMc
  change Q≤(T:Subgroup G) at hQT
  change C⊓centralizer (Q:Set G)≤Q at hself
  have hVC : V≤C := by
    apply le_centralizer_iff.mpr
    exact (hUE.trans inf_le_left).trans inf_le_left |>.trans
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hQN : Mc≤normalizer (Q:Set G) := by
    rw [hQMc]
    exact Mc.le_normalizer.trans (normalizer_le_normalizer_characteristic_image Mc (pCore 2 Mc))
  have hMcC : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T:Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T:Subgroup G)≤Mc := by
    intro t ht
    exact hMcC.2 (fun z hz => (centralInvolutions_le_centralizer_sylow T hz t ht).symm)
  let D := internalActionImage M V h.normalized
  let ρ := imageRepresentation M V h.normalized
  let f : M →* D := (actionHom M V h.normalized).rangeRestrict
  let S : Sylow 2 D := (T.subtype hM.1.2).mapSurjective (actionHom M V h.normalized).rangeRestrict_surjective
  let B : Subgroup D := (Q.subgroupOf M).map f
  have hBS : B≤(S:Subgroup D) := map_mono (subgroupOf_mono M hQT)
  have hBn : (S:Subgroup D)≤normalizer (B:Set D) := by
    apply le_normalizer_iff.mpr
    rintro x ⟨t,ht,rfl⟩ y ⟨q,hq,rfl⟩
    refine ⟨t*q*t⁻¹,?_,by simp only [map_mul,map_inv]; rfl⟩
    exact le_normalizer_iff.mp (hTMc.trans hQN) t ht q hq
  have hr := source_centralizing_full_cases_twoRank hG T hM U c d hd π hp hs
    (Or.inr (Or.inr (Or.inl hdec)))
  have ha := (h.thompson_actors T hM.1.2 hq
    (fun A hA => hA.rank_le_of_primeRank_le hr)).1
  have hm := (h.source_thompson_escape_and_movement hG T hempty hM hmany hJ).2
  have hJi := (chosen_thompson_images_of_source_decomposable T hM.1.2 h.normalized
    hm ha c d π hp hdec).1
  rw [←hQMc]
  by_cases hB : B=⊥
  · have hQV : Q≤centralizer (V:Set G) := by
      intro q hq
      have hh : f ⟨q,hM.1.2 (hQT hq)⟩=1 := by
        have hh := mem_map_of_mem f (show (⟨q,hM.1.2 (hQT hq)⟩:M)∈Q.subgroupOf M from hq)
        rwa [show (Q.subgroupOf M).map f=B from rfl,hB,mem_bot] at hh
      have hk : (⟨q,hM.1.2 (hQT hq)⟩:M)∈(actionHom M V h.normalized).ker := congrArg Subtype.val hh
      rw [actionHom_ker] at hk
      exact hk
    exact inf_le_left.trans (le_inf hVC (le_centralizer_iff.mp hQV) |>.trans hself)
  · obtain ⟨z,hzB,hz,hzC⟩ := normal_two_contains_central_involution (S:Subgroup D)
      S.isPGroup' B hBS hBn hB
    have he := thompson_central_involution_displacement hM.1.2 h.normalized c d s π hp hs
      hdec hq hfive hJi z (hBS hzB) hz hzC
    rw [←he]
    obtain ⟨q,hq,rfl⟩ := hzB
    have hcomm : ⁅Q,V⁆≤Q := le_normalizer_iff_commutator_le_left.mp (hVC.trans (hCMc.trans hQN))
    rintro x ⟨v,hv,rfl⟩
    obtain ⟨w,rfl⟩ := hv
    change ((imageRepresentation M V h.normalized (f q) w).toMul:G)/(w.toMul:G)∈Q
    change ((q:G)*(w.toMul:G)*(q:G)⁻¹)/(w.toMul:G)∈Q
    rw [div_eq_mul_inv]
    exact hcomm (commutator_mem_commutator hq w.toMul.property)

end CFSG.Quasithin.Chapter15.Section01
