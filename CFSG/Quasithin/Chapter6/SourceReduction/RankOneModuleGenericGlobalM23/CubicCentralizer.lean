module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalM23.CubicFusion
public import Theory.GroupTheory.Recognition.QuasithinM23.CubicCentralizer
public import Theory.GroupTheory.Recognition.QuasithinM23.CubicQuotient
/-!
# The original commuting cubic–involution centralizer

For the original central involution z, the ambient centralizer C_G(z) lies
in the exceptional local J and has exactly O₂(J) as its two-core. A cubic
in C_G(z) fixes a plane on this core. Its centralizer in the actual PSL₃(2)
quotient is cyclic of order three, so its full centralizer in C_G(z) has
order twelve; modulo the same cubic it is elementary abelian of order four.

This is the local centralizer calculation in Aschbacher–Smith 5.2.15,
printed pp.654–655 (`refs/quasithin.pdf`). No splitting, ambient generation
or recognition hypothesis is used.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

theorem Preparation.linear_nonmaximal_commuting_centralizer
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G)) :
    ∃ z : G, orderOf z = 2 ∧
      ∀ c : centralizer ({z} : Set G), orderOf c = 3 →
        Nat.card (centralizer ({c} : Set (centralizer ({z} : Set G)))) = 12 ∧
          ∀ x ∈ centralizer ({c} : Set (centralizer ({z} : Set G))), x^2 ∈ zpowers c := by
  obtain ⟨_,hc⟩ := d.linear_maximal_or_exceptional h hH hp F hm hF he
  obtain ⟨_,J,hJ,hKJ,_⟩ := hc.resolve_left hnonmax
  have hn := (d.block_overcomponent_parameter h hH.1.1.2 hp F hm hF (.inl he) hJ.1 hKJ).1
  have hb := d.linear_four_overcomponent_exceptional (hn ▸ h) hH.1.1.2 hp F hm hF he hJ.1 hKJ
  obtain ⟨hU,hcard,_⟩ := d.linear_overcomponent_action h hH.1.1.2 hp F hm hF he hJ.1 hKJ.le
  rw [hn] at hcard
  have hcard : Nat.card (pCore 2 J) = 16 := hcard
  let := hU
  obtain ⟨_,_,z,hzU,hz,_,hCJ,hcore,hquot,_⟩ :=
    d.linear_exceptional_centralizer_geometry h hH hp F hm hF he hJ hKJ
  let C := centralizer ({z} : Set G)
  let eU : pCore 2 C ≃* pCore 2 J :=
    ((pCore 2 C).equivMapOfInjective C.subtype C.subtype_injective).trans
      ((MulEquiv.subgroupCongr hcore).trans
        ((pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective).symm)
  let : IsElementaryAbelian 2 (pCore 2 C) :=
    IsElementaryAbelian.of_injective eU.toMonoidHom eU.injective
  have hCU : centralizer (pCore 2 J : Set J) = pCore 2 J :=
    le_antisymm (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T
      (h.qtke.evenCharacteristic T) hJ.1) (fun x hx y hy => setLike_mul_comm hy hx)
  let qJ := hb.2.1.some.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 J))
  have hqJ : Function.Surjective qJ := hb.2.1.some.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkJ : qJ.ker = pCore 2 J :=
    (MonoidHom.ker_comp_of_injective _ hb.2.1.some.toMonoidHom hb.2.1.some.injective).trans
      (QuotientGroup.ker_mk' _)
  refine ⟨z,hz,?_⟩
  intro c hc
  let cJ : J := ⟨c,hCJ c.property⟩
  have hzJ : z ∈ J := pCoreIn_le 2 J hzU
  have hzUJ : (⟨z,hzJ⟩ : J) ∈ pCore 2 J := by
    obtain ⟨u,hu,he⟩ := hzU
    exact (Subtype.ext he : u = ⟨z,hzJ⟩) ▸ hu
  have hcJ : orderOf cJ = 3 := (Subgroup.orderOf_coe cJ).symm.trans
    ((Subgroup.orderOf_coe c).trans hc)
  have hfix := QuasithinM23.exceptional_cubic_core_centralizer_card (pCore 2 J) hcard qJ hqJ hkJ hCU
    cJ hcJ ⟨z,hzJ⟩ hzUJ (fun he => by
      have hz1 : z = 1 := congrArg Subtype.val he
      simp [hz1] at hz) (show Commute cJ ⟨z,hzJ⟩ from
      Subtype.ext (mem_centralizer_singleton_iff.mp c.property))
  let f : C →* J := inclusion hCJ
  have hmapU : (pCore 2 C).map f = pCore 2 J := by
    apply map_injective (f := J.subtype) J.subtype_injective
    rw [map_map]
    exact hcore
  let e : (pCore 2 C ⊓ centralizer ({c} : Set C) : Subgroup C) ≃
      (pCore 2 J ⊓ centralizer ({cJ} : Set J) : Subgroup J) :=
    Equiv.ofBijective (fun x => ⟨f x, hmapU ▸ mem_map_of_mem f x.property.1,
      mem_centralizer_singleton_iff.mpr (by
        change f x * f c = f c * f x
        simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp x.property.2))⟩) (by
        constructor
        · intro x y hxy
          exact Subtype.ext (inclusion_injective hCJ (congrArg Subtype.val hxy))
        · intro y
          obtain ⟨x,hx,hxy⟩ := (show (y : J) ∈ (pCore 2 C).map f from hmapU.symm ▸ y.property.1)
          refine ⟨⟨x,hx,mem_centralizer_singleton_iff.mpr ?_⟩,Subtype.ext hxy⟩
          apply inclusion_injective hCJ
          change f (x*c) = f (c*x)
          rw [map_mul,map_mul,hxy]
          exact mem_centralizer_singleton_iff.mp y.property.2)
  have hfixC : Nat.card (pCore 2 C ⊓ centralizer ({c} : Set C) : Subgroup C) = 4 :=
    (Nat.card_congr e).trans hfix
  let qC := hquot.some.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
  have hkC : qC.ker = pCore 2 C :=
    (MonoidHom.ker_comp_of_injective _ hquot.some.toMonoidHom hquot.some.injective).trans
      (QuotientGroup.ker_mk' _)
  exact QuasithinM23.elementary_psl3Two_cubic_centralizer (pCore 2 C) qC hkC c hc hfixC

/-- The same order-twelve centralizer calculation at every actual involution. -/
theorem Preparation.linear_nonmaximal_involution_cubic_centralizer
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    (t : G) (ht : orderOf t = 2)
    (c : centralizer ({t} : Set G)) (hc : orderOf c = 3) :
    Nat.card (centralizer ({c} : Set (centralizer ({t} : Set G)))) = 12 ∧
      ∀ x ∈ centralizer ({c} : Set (centralizer ({t} : Set G))), x^2 ∈ zpowers c := by
  obtain ⟨z,hz,hlocal⟩ := d.linear_nonmaximal_commuting_centralizer h hH hp F hm hF he hnonmax
  obtain ⟨g,hg⟩ := isConj_iff.mp (d.linear_nonmaximal_involutions_isConj h hH hp F hm hF he hnonmax ht hz)
  let e : centralizer ({t} : Set G) ≃* centralizer ({z} : Set G) :=
    (CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g) t).trans
      (MulEquiv.subgroupCongr (congrArg (fun w : G => centralizer ({w} : Set G)) hg))
  obtain ⟨hcard,hsquare⟩ := hlocal (e c) ((e.orderOf_eq c).trans hc)
  let eC := CentralizerSmallKernelTransport.centralizerEquiv e c
  refine ⟨(Nat.card_congr eC.toEquiv).trans hcard,?_⟩
  intro x hx
  obtain ⟨k,hk⟩ := hsquare (e x) (mem_centralizer_singleton_iff.mpr (by
    simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hx)))
  refine ⟨k,e.injective ?_⟩
  simpa only [map_zpow,map_pow] using hk


/-- Every involution centralizer in the literal cubic-centralizer quotient is E₄.
The quotient also has one involution class. -/
theorem Preparation.linear_nonmaximal_cubic_quotient_centralizers
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hnonmax : residual H ∉ Chapter1.LStar G (T : Subgroup G))
    (c : G) (hc : orderOf c = 3) :
    (∀ a b : QuasithinM23.cubicCentralizerQuotient c,
      orderOf a = 2 → orderOf b = 2 → IsConj a b) ∧
    (∀ t : QuasithinM23.cubicCentralizerQuotient c, orderOf t = 2 →
      Nat.card (centralizer ({t} : Set (QuasithinM23.cubicCentralizerQuotient c))) = 4 ∧
        IsElementaryAbelian 2 (centralizer ({t} : Set (QuasithinM23.cubicCentralizerQuotient c)))) := by
  let X := centralizer ({c} : Set G)
  let Z := QuasithinM23.centralizerCyclic c
  let q := QuotientGroup.mk' Z
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : Nat.card q.ker = 3 := by
    rw [QuotientGroup.ker_mk',Nat.card_zpowers,←Subgroup.orderOf_coe]
    exact hc
  have hodd : Odd (Nat.card q.ker) := by rw [hk]; decide
  have hcentral : q.ker ≤ center X := by
    rw [QuotientGroup.ker_mk']
    exact QuasithinM23.centralizerCyclic_le_center c
  have hfus := d.linear_nonmaximal_cubic_centralizer_involutions_isConj h hH hp F hm hF he hnonmax c hc
  have hqfus := QuasithinM23.odd_quotient_involutions_isConj q hq hodd hfus
  refine ⟨hqfus,?_⟩
  intro a ha
  obtain ⟨t,htmap,htsq⟩ := OddCentralLifting.exists_involution_lift q hodd hq a (ha ▸ pow_orderOf_eq_one a)
  have ht : orderOf t = 2 := by
    apply orderOf_eq_prime htsq
    intro he
    rw [←htmap,he,map_one,orderOf_one] at ha
    omega
  have htG : orderOf (t : G) = 2 := (Subgroup.orderOf_coe t).trans ht
  have hct : Commute c (t : G) := (mem_centralizer_singleton_iff.mp t.property).symm
  let c' : centralizer ({(t : G)} : Set G) := ⟨c,mem_centralizer_singleton_iff.mpr hct.eq⟩
  obtain ⟨hcard,hsquare⟩ := d.linear_nonmaximal_involution_cubic_centralizer h hH hp F hm hF he hnonmax
    t htG c' ((Subgroup.orderOf_coe c').symm.trans hc)
  let e := QuasithinM23.commutingCentralizerEquiv c (t : G) hct
  have hcard' : Nat.card (centralizer ({t} : Set X)) = 12 :=
    (Nat.card_congr e.toEquiv).trans hcard
  have hsquare' (x : X) (hx : x ∈ centralizer ({t} : Set X)) : x^2 ∈ q.ker := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k,hk⟩ := hsquare (e ⟨x,hx⟩).val (e ⟨x,hx⟩).property
    refine ⟨k,Subtype.ext ?_⟩
    have hh := congrArg (fun v : centralizer ({(t : G)} : Set G) => (v : G)) hk
    change c^k = ((e ⟨x,hx⟩).val : G)^2 at hh
    rw [QuasithinM23.commutingCentralizerEquiv_coe] at hh
    exact hh
  obtain ⟨_,hcard'',hel⟩ := QuasithinM23.central_cubic_quotient_centralizer q hq hk hcentral t ht hcard' hsquare'
  exact htmap ▸ ⟨hcard'',hel⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
