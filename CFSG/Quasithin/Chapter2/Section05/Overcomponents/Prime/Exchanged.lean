module
public import Theory.GroupTheory.GeneralizedFitting.ComponentSwapNormFixedSeed
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.MarkedOrdinarySource
public import CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource.Kernel

/-!
# The source kernel of an exchanged component pair

Apply the generic norm-component uniqueness and pair stabilizer theorem inside the actual involution centralizer. Transport its normalizer and exact index through the original subgroup inclusion, discharging both local premises of the maximal bad-involution theorem.

Source: Aschbacher–Smith 2.5.19, printed pp.560–563.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
open ComponentRefinement ComponentSelection OvercomponentsSource
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

omit [Finite G] in
private theorem component_double_centralizer
    (K : Subgroup G) (t i : G) (htI : t ∈ centralizer ({i} : Set G))
    (hKi : K ≤ centralizer ({i} : Set G))
    (hKt : IsComponentIn K (centralizer ({t} : Set G))) :
    IsComponentIn (K.subgroupOf (centralizer ({i} : Set G)))
      (centralizer ({(⟨t,htI⟩ : centralizer ({i} : Set G))} : Set (centralizer ({i} : Set G)))) := by
  let Gi := centralizer ({i} : Set G)
  let tI : Gi := ⟨t,htI⟩
  let C := centralizer ({tI} : Set Gi)
  let Ct := centralizer ({t} : Set G)
  let D := K.subgroupOf Gi
  have hDC : D ≤ C := by
    intro k hk
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hKt.1 hk)
  let f : C →* Ct := ((Gi.subtype).comp C.subtype).codRestrict Ct (fun x => by
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))
  let e : (D.subgroupOf C) ≃* K :=
    (subgroupOfEquivOfLe hDC).trans (subgroupOfEquivOfLe hKi)
  refine ⟨hDC, hKt.2.1.comap f, ?_⟩
  let : IsQuasisimple K := hKt.quasisimple
  exact IsQuasisimple.of_mulEquiv e.symm

theorem source_exchanged_kernel
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (t i : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hi : BadInvolution ((S : Subgroup H).map H.subtype) K i)
    (htI : t ∈ centralizer ({i} : Set G))
    (J : Subgroup (centralizer ({i} : Set G)))
    (hJ : IsComponent (centralizer ({i} : Set G)) J)
    (hm : J ≠ J.map (MulAut.conj (⟨t,htI⟩ : centralizer ({i} : Set G))).toMonoidHom)
    (hpair : componentOrbit (K.subgroupOf (centralizer ({i} : Set G)))
        (oddELayer (centralizer ({i} : Set G))) =
      J ⊔ J.map (MulAut.conj (⟨t,htI⟩ : centralizer ({i} : Set G))).toMonoidHom) :
    ((S : Subgroup H).map H.subtype ⊓ centralizer ({i} : Set G) ≤ normalizer (K : Set G)) ∧
    (let Gi := centralizer ({i} : Set G)
     let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
     let R := ((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓ Gi
     ((R ⊓ centralizer (X.map Gi.subtype : Set G)).subgroupOf R).index = 2) := by
  let Y := (S : Subgroup H).map H.subtype
  let Gi := centralizer ({i} : Set G)
  let tI : Gi := ⟨t,htI⟩
  let D := K.subgroupOf Gi
  let X := componentOrbit D (oddELayer Gi)
  let R := (Y ⊓ centralizer (K : Set G)) ⊓ Gi
  let RI := R.subgroupOf Gi
  have hKi : K ≤ Gi := fun k hk => mem_centralizer_singleton_iff.mpr (hi.1.2 k hk)
  have hKt := source_component_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ
  have hD := component_double_centralizer K t i htI hKi hKt
  have hDP : D ≤ J ⊔ J.map (MulAut.conj tI).toMonoidHom :=
    hpair ▸ le_componentOrbit D (oddELayer Gi)
  have ht2 : tI ^ 2 = 1 := by
    apply Subtype.ext
    exact ht ▸ pow_orderOf_eq_one t
  have hrank := (hG.involution_centralizer_sqtk hi.2.1).stronglyQuasithin
  have hnorm := NormPair.centralizer_normalizes_fixed_component hrank hJ hm.symm ht2 hD hDP
  have hRi : R ≤ Gi := inf_le_right
  have hRat : RI ≤ centralizer ({tI} : Set Gi) := by
    intro r hr
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (htZ.2 r hr.1.1)
  have hRK : RI ≤ centralizer (D : Set Gi) := by
    intro r hr k hk
    exact Subtype.ext (hr.1.2 k hk)
  have htR : tI ∈ RI := by
    refine ⟨⟨htZ.1, ?_⟩, htI⟩
    exact fun k hk => mem_centralizer_singleton_iff.mp (hKt.1 hk)
  have hidx := NormPair.fixed_component_pair_kernel_index hrank hJ hm.symm ht2 hD hDP
    RI hRat hRK htR
  refine ⟨?_, ?_⟩
  · intro b hb
    have hbt : (⟨b,hb.2⟩ : Gi) ∈ centralizer ({tI} : Set Gi) := by
      apply mem_centralizer_singleton_iff.mpr
      exact Subtype.ext (htZ.2 b hb.1)
    have hn : b ∈ normalizer (D.map Gi.subtype : Set G) :=
      le_normalizer_map (H := D) Gi.subtype (mem_map_of_mem Gi.subtype (hnorm hbt))
    rwa [map_subgroupOf_eq_of_le hKi] at hn
  · have hXm : X = J ⊔ J.map (MulAut.conj tI).toMonoidHom := hpair
    have hdmap : (RI ⊓ centralizer (X : Set Gi)).map Gi.subtype =
        R ⊓ centralizer (X.map Gi.subtype : Set G) := by
      ext b
      constructor
      · rintro ⟨r, ⟨hr,hc⟩, rfl⟩
        refine ⟨hr, ?_⟩
        rintro x ⟨y, hy, rfl⟩
        exact congrArg Subtype.val (hc y hy)
      · rintro ⟨hr,hc⟩
        refine ⟨⟨b,hRi hr⟩, ⟨hr, ?_⟩, rfl⟩
        intro x hx
        exact Subtype.ext (hc x (mem_map_of_mem Gi.subtype hx))
    have hrmap : RI.map Gi.subtype = R := map_subgroupOf_eq_of_le hRi
    have he := relIndex_map_map_of_injective
      (RI ⊓ centralizer (X : Set Gi)) RI Gi.subtype_injective
    rw [hdmap, hrmap] at he
    exact he.trans (by simpa only [relIndex,hXm] using hidx)

/-- The literal exchanged branch supplies both formerly explicit kernel
premises of the source maximality theorem. -/
theorem source_maximal_exchanged_dichotomy
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (t i : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hi : MaximalBadInvolution ((S : Subgroup H).map H.subtype) K i)
    (htI : t ∈ centralizer ({i} : Set G))
    (J : Subgroup (centralizer ({i} : Set G)))
    (hJ : IsComponent (centralizer ({i} : Set G)) J)
    (hm : J ≠ J.map (MulAut.conj (⟨t,htI⟩ : centralizer ({i} : Set G))).toMonoidHom)
    (hpair : componentOrbit (K.subgroupOf (centralizer ({i} : Set G)))
        (oddELayer (centralizer ({i} : Set G))) =
      J ⊔ J.map (MulAut.conj (⟨t,htI⟩ : centralizer ({i} : Set G))).toMonoidHom) :
    Nat.card ((((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓
      centralizer ({i} : Set G)) : Subgroup G) ≤ 4 ∨
      (¬ (K.subgroupOf H).Normal ∧
        i ∈ centerIn ((S : Subgroup H).map H.subtype ⊓ normalizer (K : Set G))) := by
  obtain ⟨hN,hidx⟩ := source_exchanged_kernel c hG hempty hgen hb hstar t i ht htC htZ
    hi.1 htI J hJ hm hpair
  exact source_maximal_kernel_dichotomy c hG hempty hgen hb hstar i hi hN hidx

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime
