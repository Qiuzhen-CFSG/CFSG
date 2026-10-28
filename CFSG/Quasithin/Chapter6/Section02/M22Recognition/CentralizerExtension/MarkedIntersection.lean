module
public import CFSG.Quasithin.Chapter6.Section02.M22Recognition.CentralizerExtension.SourceQuotient
public import CFSG.Quasithin.Chapter6.Section02.NaturalHyperplanes
public import Theory.GroupTheory.QuaternionCentralProductSymmetricFiveImage
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.QuotientIntersection
public import Theory.GroupTheory.PrimeOrderLift

/-!
# The actual cubic conjugate-core intersection

In the source involution centralizer, let P be the normal plus extraspecial
core and V the natural SL₂(4) layer. Restricting the marked M/V ≃ S₅ quotient
to P gives an elementary image of order four with kernel P ∩ V of order
eight. The image cannot be the even four: its full Sylow action on the
hyperplane would have commutator Z_S of order four, while the extraspecial
commutator lies in the center of order two.

The actual outer four-group and its cubic conjugate have disjoint quotient
images. Thus P ∩ Pᵈ lies in V. Its two hyperplane kernels meet exactly in
Z_S by the natural-module calculation, proving P ∩ Pᵈ = Z_S with the
original right-conjugation convention. The final source consumer removes
this formerly explicit marked-intersection premise from the elementary
sixteen/symmetric-four centralizer construction.

Source: Aschbacher–Smith, Proposition 6.2.13, printed p.688.
The earlier natural reduction, compatible quotient and core/orbit inputs
remain explicit; no ambient M₂₂ recognition is asserted here.
-/
public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
open Source
variable {G : Type*} [Group G] [Finite G]
private def coreToLocal {H M : Subgroup G} (P : Subgroup H)
    (hPM : P.map H.subtype ≤ M) : P →* M where
  toFun p := ⟨((p : H) : G), hPM (mem_map_of_mem H.subtype p.property)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

omit [Finite G] in
private theorem coreToLocal_injective {H M : Subgroup G} (P : Subgroup H)
    (hPM : P.map H.subtype ≤ M) : Function.Injective (coreToLocal P hPM) := by
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun z : M => (z : G)) h))

omit [Finite G] in
private theorem coreToLocal_range {H M : Subgroup G} (P : Subgroup H)
    (hPM : P.map H.subtype ≤ M) :
    (coreToLocal P hPM).range = (P.map H.subtype).subgroupOf M := by
  ext x
  constructor
  · rintro ⟨p,rfl⟩
    exact mem_map_of_mem H.subtype p.property
  · rintro ⟨p,hp,hpx⟩
    exact ⟨⟨p,hp⟩,Subtype.ext hpx⟩

/-- The extraspecial core has an actual hyperplane kernel in the marked quotient. -/
theorem source_core_kernel_geometry {H M V : Subgroup G}
    (P : Subgroup H) [P.Normal] (hP : CoreData P)
    (hPM : P.map H.subtype ≤ M)
    [IsElementaryAbelian 2 V] [(V.subgroupOf M).Normal]
    (hZV : coreCenter P ≤ V.subgroupOf H)
    (e : (M ⧸ V.subgroupOf M) ≃* Equiv.Perm (Fin 5)) :
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (V.subgroupOf M))
    Nat.card (P.map H.subtype ⊓ V : Subgroup G) = 8 ∧
      IsElementaryAbelian 2 (((P.map H.subtype).subgroupOf M).map q) ∧
      Nat.card (((P.map H.subtype).subgroupOf M).map q) = 4 := by
  let i := coreToLocal P hPM
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (V.subgroupOf M))
  let f := q.comp i
  have hker (p : P) : p ∈ f.ker ↔ ((p : H) : G) ∈ V := by
    change e (QuotientGroup.mk' (V.subgroupOf M) (i p)) = 1 ↔ _
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff (i p)
  have hZ : center P ≤ f.ker := by
    intro z hz
    apply (hker z).mpr
    exact hZV (mem_map_of_mem P.subtype hz)
  let j : f.ker →* V := {
    toFun x := ⟨(((x : P) : H) : G), (hker x).mp x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y h
    exact Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun z : V => (z : G)) h)))
  have hke : IsElementaryAbelian 2 f.ker := IsElementaryAbelian.of_injective j hj
  obtain ⟨d⟩ := hP.plusType
  obtain ⟨hE,hk,hf⟩ := d.symmetricFive_image f hZ hke
  have hr : f.range = ((P.map H.subtype).subgroupOf M).map q := by
    rw [MonoidHom.range_comp,coreToLocal_range]
  have hkmap : f.ker.map (H.subtype.comp P.subtype) = P.map H.subtype ⊓ V := by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨mem_map_of_mem H.subtype p.property,(hker p).mp hp⟩
    · rintro ⟨⟨p,hp,rfl⟩,hv⟩
      exact ⟨⟨p,hp⟩,(hker ⟨p,hp⟩).mpr hv,rfl⟩
  refine ⟨?_,hr ▸ hE,hr ▸ hf⟩
  rw [←hkmap,card_map_of_injective (show Function.Injective (H.subtype.comp P.subtype) from
    fun x y h => Subtype.ext (Subtype.ext h)),hk]

private theorem even_sylow_intersection_card (T : Sylow 2 (Equiv.Perm (Fin 5))) :
    Nat.card ((T : Subgroup _) ⊓ alternatingGroup (Fin 5) : Subgroup _) ≤ 4 := by
  have hp := T.isPGroup'.to_le (inf_le_left :
    ((T : Subgroup _) ⊓ alternatingGroup (Fin 5) : Subgroup _) ≤ T)
  obtain ⟨k,hk⟩ := hp.exists_card_eq
  have hd := card_dvd_of_le (inf_le_right :
    ((T : Subgroup _) ⊓ alternatingGroup (Fin 5) : Subgroup _) ≤ alternatingGroup (Fin 5))
  rw [nat_card_alternatingGroup,Nat.card_fin,hk] at hd
  have hb' : k ≤ 2 := by
    by_contra h
    have hd8 : 8 ∣ 60 := (show (2 : ℕ)^3 ∣ 2^k from pow_dvd_pow 2 (by omega)).trans hd
    norm_num at hd8
  rw [hk]
  interval_cases k <;> norm_num

private theorem core_commutator_le_center {H : Subgroup G}
    (P : Subgroup H) [P.Normal] (hP : CoreData P) :
    ⁅P.map H.subtype,P.map H.subtype⁆ ≤ (coreCenter P).map H.subtype := by
  obtain ⟨d⟩ := hP.plusType
  let : IsElementaryAbelian 2 (P ⧸ center P) := d.quotient_elementary
  apply commutator_le.mpr
  rintro _ ⟨a,ha,rfl⟩ _ ⟨b,hb,rfl⟩
  have hc : ⁅(⟨a,ha⟩ : P),(⟨b,hb⟩ : P)⁆ ∈ center P := by
    apply (QuotientGroup.eq_one_iff _).mp
    change (QuotientGroup.mk' (center P)) ⁅(⟨a,ha⟩ : P),(⟨b,hb⟩ : P)⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  exact mem_map_of_mem H.subtype (mem_map_of_mem P.subtype hc)

/-- The extraspecial source core has the outer four-group image in the same marked quotient. -/
theorem source_core_outer_image
    {κ : GroupClass} {T : Sylow 2 G} {L M V₀ : Subgroup G} {n : ℕ}
    (h611 : Hypothesis611 κ T L M V₀ n)
    (hnat : IsNaturalModule L (layer L V₀) 2)
    (H : Subgroup G) (P : Subgroup H) [P.Normal] (hP : CoreData P)
    (hZS : coreCenter P ≤ (ZS (T : Subgroup G) L V₀).subgroupOf H)
    (hPT : P.map H.subtype ≤ (T : Subgroup G))
    [((layer L V₀).subgroupOf M).Normal]
    (hq : CompatibleSymmetricFiveQuotient ((layer L V₀).subgroupOf M) (L.subgroupOf M))
    (e : (M ⧸ (layer L V₀).subgroupOf M) ≃* Equiv.Perm (Fin 5))
    (hL : (L.subgroupOf M).map
      (e.toMonoidHom.comp (QuotientGroup.mk' ((layer L V₀).subgroupOf M))) = alternatingGroup (Fin 5)) :
    let q := e.toMonoidHom.comp (QuotientGroup.mk' ((layer L V₀).subgroupOf M))
    ¬ ((P.map H.subtype).subgroupOf M).map q ≤ alternatingGroup (Fin 5) := by
  let V := layer L V₀
  let Pa := P.map H.subtype
  let A := Pa ⊓ V
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (V.subgroupOf M))
  let B := (Pa.subgroupOf M).map q
  let : IsElementaryAbelian 2 V₀ := h611.V_mem.2.1
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_injective
    (inclusion h611.layer_le_V) (inclusion_injective h611.layer_le_V)
  have hPM : Pa ≤ M := hPT.trans h611.sylow_le
  have hZV : coreCenter P ≤ V.subgroupOf H := fun x hx => (hZS hx).1
  obtain ⟨hA,hBE,hB⟩ := source_core_kernel_geometry P hP hPM hZV e
  let : IsElementaryAbelian 2 B := hBE
  have hsurj : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Tb := (T.subtype h611.sylow_le).mapSurjective hsurj
  have hBT : B ≤ Tb := map_mono (by intro x hx; exact hPT hx)
  have hk : q.ker = V.subgroupOf M :=
    (MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk' (V.subgroupOf M)) e).trans
      (QuotientGroup.ker_mk' _)
  change ¬ B ≤ alternatingGroup (Fin 5)
  intro hEven
  have hfull : B = (Tb : Subgroup _) ⊓ alternatingGroup (Fin 5) :=
    eq_of_le_of_card_ge (le_inf hBT hEven)
      ((even_sylow_intersection_card Tb).trans (by rw [hB]))
  have hTL : (T : Subgroup G) ≤ normalizer (L : Set G) :=
    h611.sylow_le.trans ((normal_subgroupOf_iff_le_normalizer h611.L_le).mp h611.L_normal)
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  have hbar : (S : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L := by
    rw [hS,subgroupOf_map_subtype]
  have hcomm : ⁅A,(T : Subgroup G) ⊓ L⁆ = ZS (T : Subgroup G) L V₀ := by
    simpa only [hbar,ZS,coe_inf,Set.inf_eq_inter] using
      hnat.eight_sylow_commutator S A inf_le_right hA
  have hZcard : Nat.card (ZS (T : Subgroup G) L V₀) = 4 := by
    simpa only [hbar,ZS,coe_inf,Set.inf_eq_inter, show (2 : ℕ)^2=4 from rfl] using
      (hnat.sylow_fixed_geometry S).1
  have hImage : (((T : Subgroup G) ⊓ L).subgroupOf M).map q = B := by
    change (((T : Subgroup G).subgroupOf M) ⊓ L.subgroupOf M).map q = B
    rw [map_inf_of_ker_le q _ _ (hk ▸ hq.kernel_le_layer),hL]
    exact hfull.symm
  have hBound : ⁅A,(T : Subgroup G) ⊓ L⁆ ≤ (coreCenter P).map H.subtype := by
    apply commutator_le.mpr
    intro a ha s hs
    let sm : M := ⟨s,h611.sylow_le hs.1⟩
    have him : q sm ∈ B := hImage ▸ mem_map_of_mem q hs
    obtain ⟨pm,hpm,he⟩ := him
    have hdiff : ((pm : G)⁻¹ * s) ∈ V := by
      have hh : pm⁻¹ * sm ∈ q.ker := by
        change q (pm⁻¹ * sm) = 1
        rw [map_mul,map_inv,he,inv_mul_cancel]
      change pm⁻¹ * sm ∈ V.subgroupOf M
      rwa [hk] at hh
    have hac : ⁅a,(pm : G)⁻¹ * s⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (congrArg (fun x : V => (x : G)) (mul_comm (⟨a,ha.2⟩ : V) ⟨_,hdiff⟩))
    have heq : ⁅a,s⁆ = ⁅a,(pm : G)⁆ := by
      have hh := commutatorElement_mul_right_eq_mul_conj a (pm : G) ((pm : G)⁻¹*s)
      rw [mul_inv_cancel_left,hac,mul_one,mul_inv_cancel_right] at hh
      exact hh
    rw [heq]
    exact core_commutator_le_center P hP (commutator_mem_commutator ha.1 hpm)
  have hc := card_le_of_le hBound
  rw [hcomm,hZcard,card_map_of_injective H.subtype_injective,coreCenter_card hP] at hc
  omega

/-- The literal marked source conjugate cores meet in the natural Sylow plane. -/
theorem source_core_cubic_intersection
    {κ : GroupClass} {T : Sylow 2 G} {L M V₀ : Subgroup G} {n : ℕ}
    (h611 : Hypothesis611 κ T L M V₀ n)
    (hnat : IsNaturalModule L (layer L V₀) 2)
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (P : Subgroup H) [P.Normal] (hP : CoreData P)
    (hZS : coreCenter P ≤ (ZS (T : Subgroup G) L V₀).subgroupOf H)
    (hSP : (ZS (T : Subgroup G) L V₀).subgroupOf H ≤ P)
    (hPT : P.map H.subtype ≤ (T : Subgroup G))
    [((layer L V₀).subgroupOf M).Normal]
    (hq : CompatibleSymmetricFiveQuotient ((layer L V₀).subgroupOf M) (L.subgroupOf M))
    (d : G) (hdL : d ∈ L)
    (hdT : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G)) (hd : orderOf d = 3) :
    P.map H.subtype ⊓ (P.map H.subtype).map (MulAut.conj d⁻¹).toMonoidHom =
      ZS (T : Subgroup G) L V₀ := by
  obtain ⟨e,hL⟩ := hq.quotient
  let V := layer L V₀
  let Pa := P.map H.subtype
  let A := Pa ⊓ V
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (V.subgroupOf M))
  let B := (Pa.subgroupOf M).map q
  let f := (MulAut.conj d⁻¹).toMonoidHom
  let : IsElementaryAbelian 2 V₀ := h611.V_mem.2.1
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.of_injective
    (inclusion h611.layer_le_V) (inclusion_injective h611.layer_le_V)
  have hPM : Pa ≤ M := hPT.trans h611.sylow_le
  have hZV : coreCenter P ≤ V.subgroupOf H := fun x hx => (hZS hx).1
  obtain ⟨hA,hBE,hB⟩ := source_core_kernel_geometry P hP hPM hZV e
  let : IsElementaryAbelian 2 B := hBE
  have hsurj : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Tb := (T.subtype h611.sylow_le).mapSurjective hsurj
  have hBT : B ≤ Tb := map_mono (by intro x hx; exact hPT hx)
  have hk : q.ker = V.subgroupOf M :=
    (MonoidHom.ker_mulEquiv_comp (QuotientGroup.mk' (V.subgroupOf M)) e).trans
      (QuotientGroup.ker_mk' _)
  have hout : ¬ B ≤ alternatingGroup (Fin 5) :=
    source_core_outer_image h611 hnat H P hP hZS hPT hq e hL
  let dm : M := ⟨d,h611.L_le hdL⟩
  have hdq : orderOf (q dm) = 3 := by
    have hp : IsPGroup 2 q.ker := hk ▸ (IsElementaryAbelian.isPGroup 2 V).comap_subtype
    have hdm : orderOf dm = 3 := (Subgroup.orderOf_coe dm).symm.trans hd
    exact (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hp dm (by rw [hdm];decide)).trans hdm
  have hImage : (((T : Subgroup G) ⊓ L).subgroupOf M).map q =
      (Tb : Subgroup _) ⊓ alternatingGroup (Fin 5) := by
    change (((T : Subgroup G).subgroupOf M) ⊓ L.subgroupOf M).map q = _
    rw [map_inf_of_ker_le q _ _ (hk ▸ hq.kernel_le_layer),hL]
    rfl
  have hnq : q dm ∈ normalizer (((Tb : Subgroup _) ⊓ alternatingGroup (Fin 5) : Subgroup _) : Set _) := by
    rw [←hImage]
    apply (((T : Subgroup G) ⊓ L).subgroupOf M).le_normalizer_map q
    apply mem_map_of_mem q
    apply mem_normalizer_iff.mpr
    intro x
    have hdn : d ∈ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := hdT
    exact mem_normalizer_iff.mp hdn (x : G)
  have hBint := Theory.SpecificGroups.SymmetricFive.OuterFourIntersection.outer_four_inf_cubic_conjugate
    Tb B hB hBT hout (q dm) hdq hnq
  have hIntV : Pa ⊓ Pa.map f ≤ V := by
    rintro x ⟨hx,hxc⟩
    obtain ⟨y,hy,hyx⟩ := hxc
    let xm : M := ⟨x,hPM hx⟩
    let ym : M := ⟨y,hPM hy⟩
    have h1 : q xm ∈ B := mem_map_of_mem q hx
    have h2 : q xm ∈ B.map (MulAut.conj (q dm)⁻¹).toMonoidHom := by
      refine ⟨q ym,mem_map_of_mem q hy,?_⟩
      have hc : dm⁻¹ * ym * dm = xm := by
        apply Subtype.ext
        change d⁻¹ * y * d = x
        change d⁻¹ * y * (d⁻¹)⁻¹ = x at hyx
        simpa only [inv_inv] using hyx
      change (q dm)⁻¹ * q ym * ((q dm)⁻¹)⁻¹ = q xm
      rw [inv_inv,←map_inv,←map_mul,←map_mul,hc]
    have hxker : xm ∈ q.ker := by
      change q xm = 1
      exact mem_bot.mp (hBint ▸ (show q xm ∈ B ⊓ B.map (MulAut.conj (q dm)⁻¹).toMonoidHom from ⟨h1,h2⟩))
    change xm ∈ V.subgroupOf M
    rwa [hk] at hxker
  have hZA : ZS (T : Subgroup G) L V₀ ≤ A := by
    intro z hz
    exact ⟨mem_map.mpr ⟨⟨z,hTH (h611.ZS_le_T hz)⟩,hSP hz,rfl⟩,hz.1⟩
  have hAint := (h611.natural_eight_cubic_geometry hnat A inf_le_right hA hZA hdL hdT hd).2
  have hnV : d ∈ normalizer (V : Set G) := by
    obtain ⟨_,_,_,_,_,hm⟩ := hnat
    exact hm.normalizes hdL
  have hfV : V.map f = V := mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hnV)
  have he : A ⊓ A.map f = Pa ⊓ Pa.map f := by
    change (Pa ⊓ V) ⊓ (Pa ⊓ V).map f = _
    rw [map_inf _ _ _ (MulAut.conj d⁻¹).injective,hfV]
    exact le_antisymm (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
      (le_inf (le_inf inf_le_left hIntV) (le_inf inf_le_right hIntV))
  exact he.symm.trans hAint


/-- The marked source intersection is constructed from the existing local data. -/
theorem source_centralizer_extension_of_source_geometry
    {κ : GroupClass} {T : Sylow 2 G} {L M V₀ : Subgroup G} {n : ℕ}
    (h611 : Hypothesis611 κ T L M V₀ n)
    (h6127 : Conclusion6127 (T : Subgroup G) L M V₀ n)
    (H : Subgroup G) (z : G) (hH : H = centralizer ({z} : Set G))
    (hTH : (T : Subgroup G) ≤ H)
    [((layer L V₀).subgroupOf M).Normal]
    (hq : CompatibleSymmetricFiveQuotient ((layer L V₀).subgroupOf M) (L.subgroupOf M))
    (P : Subgroup H) [P.Normal] (hP : CoreData P)
    (ha : NaturalFourOrbit P ((ZS (T : Subgroup G) L V₀).subgroupOf H))
    (hZS : coreCenter P ≤ (ZS (T : Subgroup G) L V₀).subgroupOf H)
    (hSP : (ZS (T : Subgroup G) L V₀).subgroupOf H ≤ P)
    (hPT : P.map H.subtype ≤ (T : Subgroup G))
    (hbranch : (sourceEight ((ZS (T : Subgroup G) L V₀).subgroupOf H)).map H.subtype ⊓
      layer L V₀ = ZS (T : Subgroup G) L V₀)
    (d : G) (hdL : d ∈ L)
    (hdT : d ∈ normalizer ((T : Subgroup G) ⊓ L : Set G)) (hd : orderOf d = 3) :
    let S := (ZS (T : Subgroup G) L V₀).subgroupOf H
    (centralizer (sourceEight S : Set H)).Normal ∧
      IsElementaryAbelian 2 (centralizer (sourceEight S : Set H)) ∧
      Nat.card (centralizer (sourceEight S : Set H)) = 16 ∧
      Nonempty ((H ⧸ centralizer (sourceEight S : Set H)) ≃* Equiv.Perm (Fin 4)) := by
  have hPP := source_core_cubic_intersection h611 h6127.2.1 H hTH P hP hZS hSP hPT
    hq d hdL hdT hd
  exact source_centralizer_extension_of_marked_reduction h611 h6127 H z hH hTH hq P
    hP ha hZS hSP hPT hbranch d hdL hdT hd hPP

end CFSG.Quasithin.Chapter6.M22Recognition.CentralizerExtension
