module
public import CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource.Maximality
public import Theory.GroupTheory.CComponent.FixedOrbitClosure
public import Theory.GroupTheory.ComponentLocalOrbitCore

/-!
# The original overcomponent orbit and its centralizer kernel

Apply the actual I.3.2 pumpup at the source central involution. In both
branches its odd-E orbit lies in the odd-E layer and is normal there,
hence subnormal in C_G(i). Every element normalizing the original K
normalizes that orbit. If an involution centralizing the orbit preserved
K as a component, restriction and subnormal ascent would make K a
component of C_G(i), contradicting the original bad-involution choice.

For the literal R₀=C_R(K₊), these results construct its normality and
its bad-involution condition. The maximality theorem then gives |R|≤4
or the nonnormal-component alternative, retaining only the index-two
model conclusion and C_S(i)-normalization of K.

Source: Aschbacher–Smith 2.5.19, printed pp.560–563, especially case (A)
and the non-HS case (B) on p.563. The HS index-four kernel remains separate.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource
open ComponentRefinement ComponentSelection Overcomponents
variable {G : Type*} [Group G] [Finite G]

/-- The literal odd-E orbit in the pumpup is subnormal in C_G(i), and its
normalizer contains every element of C_G(i) normalizing the original K. -/
theorem source_overcomponent_orbit_subnormal
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (t i : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (_hi : orderOf i = 2) (hiS : i ∈ (S : Subgroup H).map H.subtype)
    (hiK : i ∈ centralizer (K : Set G)) :
    let Gi := centralizer ({i} : Set G)
    let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
    X.IsSubnormal ∧ K ≤ X.map Gi.subtype ∧
      Gi ⊓ normalizer (K : Set G) ≤ normalizer (X.map Gi.subtype : Set G) := by
  let Gi := centralizer ({i} : Set G)
  let A := oddELayer Gi
  let B := K.subgroupOf Gi
  let X := componentOrbit B A
  have hKi : K ≤ Gi := fun k hk => mem_centralizer_singleton_iff.mpr (hiK k hk)
  have hKt := source_component_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ
  obtain ⟨hti,_,hcase⟩ := twoComponent_pumpup K t i ht (htZ.2 i hiS).symm hKi hKt
  have hXA : X ≤ A := by
    rcases hcase with ⟨hX,_⟩ | ⟨J,hJ,_,hX,_⟩
    · exact hX.le_twoComponentLayer.trans le_sup_right
    · rw [show X = J ⊔ J.map (MulAut.conj (⟨t,hti⟩ : Gi)).toMonoidHom from hX]
      exact sup_le (hJ.le_twoComponentLayer.trans le_sup_right)
        ((hJ.map_equiv (MulAut.conj ⟨t,hti⟩)).le_twoComponentLayer.trans le_sup_right)
  have hn : (X.subgroupOf A).Normal :=
    (normal_subgroupOf_iff_le_normalizer hXA).mpr (le_normalizer_componentOrbit B A)
  have hsub : X.IsSubnormal := IsSubnormal.trans hXA hn.isSubnormal
    (inferInstance : A.Normal).isSubnormal
  have hKX : K ≤ X.map Gi.subtype := by
    have hm := map_mono (f := Gi.subtype) (le_componentOrbit B A)
    rwa [map_subgroupOf_eq_of_le hKi] at hm
  refine ⟨hsub,hKX,?_⟩
  have he : X.map Gi.subtype = componentOrbit K (A.map Gi.subtype) := by
    rw [map_componentOrbit,map_subgroupOf_eq_of_le hKi]
  rw [he]
  apply le_trans ?_ (normalizer_inf_le_normalizer_componentOrbit K (A.map Gi.subtype))
  refine le_inf inf_le_right ?_
  exact inf_le_left.trans (Gi.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image Gi A))

/-- Every involution centralizing the actual larger orbit remains a bad
involution: componenthood would restrict to the orbit and ascend along its
proved subnormal chain to C_G(i). This discharges the R₀ obstruction in the
maximality argument without a universal noncomponent premise. -/
theorem source_overcomponent_kernel_involutions
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (t i : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hi : orderOf i = 2) (hiS : i ∈ (S : Subgroup H).map H.subtype)
    (hiK : i ∈ centralizer (K : Set G))
    (hbad : ¬ IsComponentIn K (centralizer ({i} : Set G)))
    (j : G)
    (hj : j ∈ centralizer
      ((componentOrbit (K.subgroupOf (centralizer ({i} : Set G)))
        (oddELayer (centralizer ({i} : Set G)))).map
        (centralizer ({i} : Set G)).subtype : Set G)) :
    ¬ IsComponentIn K (centralizer ({j} : Set G)) := by
  intro hcomp
  let Gi := centralizer ({i} : Set G)
  let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
  obtain ⟨hs,hKX,_⟩ := source_overcomponent_orbit_subnormal c hG hempty hgen hb hstar
    t i ht htC htZ hi hiS hiK
  have hXj : X.map Gi.subtype ≤ centralizer ({j} : Set G) :=
    fun x hx => mem_centralizer_singleton_iff.mpr (hj x hx)
  have hXsub : ((X.map Gi.subtype).subgroupOf Gi).IsSubnormal := by
    change ((X.map Gi.subtype).comap Gi.subtype).IsSubnormal
    rw [comap_map_eq_self_of_injective Gi.subtype_injective]
    exact hs
  exact hbad ((hcomp.restrict hKX hXj).of_subnormal (map_subtype_le _) hXsub)

/-- The actual R₀ is normalized by C_S(i), and every one of its elements
keeps K out of componenthood in its centralizer. The source central
involution and the literal odd-E orbit are constructed internally. -/
theorem source_kernel_normalizes_and_bad
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (i : G) (hi : BadInvolution ((S : Subgroup H).map H.subtype) K i)
    (hCiN : (S : Subgroup H).map H.subtype ⊓ centralizer ({i} : Set G) ≤
      normalizer (K : Set G)) :
    let Y := (S : Subgroup H).map H.subtype
    let Gi := centralizer ({i} : Set G)
    let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
    let R := (Y ⊓ centralizer (K : Set G)) ⊓ Gi
    let D := R ⊓ centralizer (X.map Gi.subtype : Set G)
    (Y ⊓ Gi ≤ normalizer (D : Set G)) ∧
      ∀ j ∈ D, ¬ IsComponentIn K (centralizer ({j} : Set G)) := by
  let Y := (S : Subgroup H).map H.subtype
  let Gi := centralizer ({i} : Set G)
  let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
  let C := Y ⊓ Gi
  let R := (Y ⊓ centralizer (K : Set G)) ⊓ Gi
  let D := R ⊓ centralizer (X.map Gi.subtype : Set G)
  obtain ⟨t,ht,htC,htZ⟩ := MathieuSourceSetup.exists_central_core_involution c
  have horbit := source_overcomponent_orbit_subnormal c hG hempty hgen hb hstar
    t i ht htC htZ hi.2.1 hi.1.1 hi.1.2
  have hCX : C ≤ normalizer (X.map Gi.subtype : Set G) :=
    (le_inf inf_le_right hCiN).trans horbit.2.2
  have hCYK : C ≤ normalizer (Y ⊓ centralizer (K : Set G) : Set G) := by
    intro a ha x
    exact and_congr (Y.le_normalizer ha.1 x)
      (normalizer_le_normalizer_centralizer K (hCiN ha) x)
  have hCR : C ≤ normalizer (R : Set G) := by
    intro a ha x
    exact and_congr (hCYK ha x) (Gi.le_normalizer ha.2 x)
  have hCD : C ≤ normalizer (D : Set G) := by
    intro a ha x
    exact and_congr (hCR ha x)
      (normalizer_le_normalizer_centralizer (X.map Gi.subtype) (hCX ha) x)
  refine ⟨hCD,?_⟩
  intro j hj
  exact source_overcomponent_kernel_involutions c hG hempty hgen hb hstar
    t i ht htC htZ hi.2.1 hi.1.1 hi.1.2 hi.2.2 j hj.2

/-- The non-HS maximality branch, retaining only the literal model index
and C_S(i)-normalization of K. All kernel premises are discharged above. -/
theorem source_maximal_kernel_dichotomy
    {H K M : Subgroup G} {S : Sylow 2 H} {z : G}
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (i : G) (hi : MaximalBadInvolution ((S : Subgroup H).map H.subtype) K i)
    (hCiN : (S : Subgroup H).map H.subtype ⊓ centralizer ({i} : Set G) ≤
      normalizer (K : Set G))
    (hindex :
      let Gi := centralizer ({i} : Set G)
      let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
      let R := ((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓ Gi
      ((R ⊓ centralizer (X.map Gi.subtype : Set G)).subgroupOf R).index = 2) :
    Nat.card ((((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓
      centralizer ({i} : Set G)) : Subgroup G) ≤ 4 ∨
      (¬ (K.subgroupOf H).Normal ∧
        i ∈ centerIn ((S : Subgroup H).map H.subtype ⊓ normalizer (K : Set G))) := by
  let Gi := centralizer ({i} : Set G)
  let X := componentOrbit (K.subgroupOf Gi) (oddELayer Gi)
  let R := ((S : Subgroup H).map H.subtype ⊓ centralizer (K : Set G)) ⊓ Gi
  let D := R ⊓ centralizer (X.map Gi.subtype : Set G)
  obtain ⟨hDn,hbad⟩ := source_kernel_normalizes_and_bad c hG hempty hgen hb hstar i hi.1 hCiN
  exact source_maximal_bad_involution_dichotomy c hG hempty hgen hb hstar i hi hCiN
    D (show D ≤ R from inf_le_left) hDn hindex (fun j hj _ => hbad j hj)

end CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource
