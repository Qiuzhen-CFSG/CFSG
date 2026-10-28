module
public import Theory.SpecificGroups.Alternating.SevenComponent
public import Theory.GroupTheory.PrimeOrderLift
public import CFSG.Quasithin.Chapter10.SourceA5ElementComponent

/-!
# Excluding an A7 quotient in the original point centralizer

Every cubic normalizing an A7 C-component lies in that component by its
outer two-group and the ambient cubic rank bound. A commuting order-five
element would then survive with it modulo O₂, but a five-cycle in seven
letters has centralizer of order ten. This gives the source contradiction
without the full universal A.3.18 interface or an A7 block marking.

Source: Aschbacher–Smith 10.2.1, printed p.743, and A.3.18, pp.51–52.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.FixedCenterOvercomponent

private theorem seven_not_commute_three_five
    (x y : alternatingGroup (Fin 7)) (hx : orderOf x = 3) (hy : orderOf y = 5)
    (hxy : Commute x y) : False := by
  have hy' : orderOf (y : Equiv.Perm (Fin 7)) = 5 := (orderOf_coe y).trans hy
  have hcycle : (y : Equiv.Perm (Fin 7)).IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by rw [hy']; decide) (by rw [hy']; decide)
  have htype : (y : Equiv.Perm (Fin 7)).cycleType = {5} := by
    rw [hcycle.cycleType, ← hcycle.orderOf, hy']
  have hcard : Nat.card (centralizer ({(y : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))) = 10 := by
    rw [Equiv.Perm.nat_card_centralizer, htype]
    norm_num
  have hmem : (x : Equiv.Perm (Fin 7)) ∈
      centralizer ({(y : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7))) :=
    mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hxy.eq)
  have hd := orderOf_dvd_natCard (⟨x,hmem⟩ : centralizer ({(y : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7))))
  have hx' : orderOf (⟨x,hmem⟩ : centralizer ({(y : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))) = 3 :=
    (orderOf_coe _).symm.trans ((orderOf_coe x).trans hx)
  rw [hx', hcard] at hd
  norm_num at hd

theorem seven_quotient_not_commute_three_five
    {I : Type*} [Group I] [Finite I]
    (e : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7))
    (x y : I) (hx : orderOf x=3) (hy : orderOf y=5) (hxy : Commute x y) : False := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker=pCore 2 I := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    rw [he]
    exact pCore_isPGroup
  apply seven_not_commute_three_five (f x) (f y)
  · exact (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hk x (by rw [hx]; decide)).trans hx
  · exact (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hk y (by rw [hy]; decide)).trans hy
  · exact hxy.map f

theorem seven_component_not_commute_three_five
    {X : Type*} [Group X] [Finite X]
    (I : Subgroup X) (hI : I.IsCComponent)
    (e : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7)) (hr : primeRank 3 X≤2)
    (x y : X) (hx : orderOf x=3) (hy : orderOf y=5) (hyI : y∈I)
    (hxN : x∈normalizer (I:Set X)) (hxy : Commute x y) : False := by
  have hxI := alternatingGroup.SevenComponent.order_three_mem I hI e hr hx hxN
  exact seven_quotient_not_commute_three_five e (⟨x,hxI⟩:I) (⟨y,hyI⟩:I)
    ((orderOf_coe _).symm.trans hx) ((orderOf_coe _).symm.trans hy) (Subtype.ext hxy.eq)


open Chapter3.Section02

theorem source_fixed_center_not_seven_quotient
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (v : G) (hv : orderOf v=2) (I : Subgroup G) (hLI : L≤I)
    (hIX : I≤centralizer ({v}:Set G))
    (hI : (I.subgroupOf (centralizer ({v}:Set G))).IsCComponent)
    (hNI : centralizer ({v}:Set G)≤normalizer (I:Set G))
    (eI : (I ⧸ pCore 2 I) ≃* alternatingGroup (Fin 7))
    (x : G) (hx3 : orderOf x=3) (hxX : x∈centralizer ({v}:Set G))
    (hxL : x∈centralizer (L:Set G)) : False := by
  let X := centralizer ({v}:Set G)
  let J := I.subgroupOf X
  let d : J ≃* I := subgroupOfEquivOfLe hIX
  let eJ : (J ⧸ pCore 2 J) ≃* alternatingGroup (Fin 7) :=
    (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans eI
  let : J.Normal := (normal_subgroupOf_iff_le_normalizer hIX).mpr hNI
  have hq5 : 5 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr eL.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  obtain ⟨y,hy5⟩ := exists_prime_orderOf_dvd_card' (G:=L) 5
    (hq5.trans (card_quotient_dvd_card (pCore 2 L)))
  let xX : X := ⟨x,hxX⟩
  let yX : X := ⟨y,hIX (hLI y.property)⟩
  have hr : primeRank 3 X≤2 :=
    (D.simpleQTKE.involution_centralizer_sqtk hv).stronglyQuasithin 3 (by decide) (by decide)
  apply seven_component_not_commute_three_five J hI eJ hr xX yX
  · exact (orderOf_coe xX).symm.trans hx3
  · exact (orderOf_coe yX).symm.trans ((orderOf_coe y).trans hy5)
  · exact hLI y.property
  · rw [normalizer_eq_top]
    trivial
  · exact Subtype.ext (hxL y y.property).symm

end CFSG.Quasithin.Chapter10.FixedCenterOvercomponent
