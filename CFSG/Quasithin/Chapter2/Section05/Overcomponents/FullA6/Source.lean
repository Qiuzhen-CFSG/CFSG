module

public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6.A8Source
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6.A8Kernel
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6.QuotientSource
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6.HS
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.NonfullA6.Exchanged

/-!
# Original full-A₆ overcomponents after the crossing identity

The actual marked pumpup supplies the invariant larger component and the
complete quotient census. Fusion contradicts the crossing mark in the
PSL₅(2), Sp₄(4), and HS rows; the HS argument lifts the fusion through its
possible central cover. Thus every bad involution has an A₈ overcomponent.

The maximal bad involution argument now gives a four-group centralizer for
every bad involution. The compatible A₈ marking supplies the original
transposition and identifies K with the literal fixed solvable residual.
All hypotheses are original source data and the previously proved crossing
identity. No overcomponent or centralizer-four premise remains.

Source: Aschbacher–Smith 2.5.19(2)(3)(4), printed pp.560–563, applied with
2.5.25 in 2.5.26, printed pp.568–569, combined manuscript of 1 March 2004.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6
open ComponentRefinement ComponentSelection NonfullA6 OvercomponentsSource
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The surviving source row on the literal odd-E orbit. -/
theorem source_bad_involution_a8_row
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* alternatingGroup (Fin 6))
    (t zK : G) (ht : orderOf t = 2) (hzK : orderOf zK = 2)
    (htC : t ∈ twoCore H) (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hzKK : zK ∈ K) (hz : z = t * zK)
    (i : G) (hi : BadInvolution ((S : Subgroup H).map H.subtype) K i) :
    let Gi := centralizer ({i} : Set G)
    let D := K.subgroupOf Gi
    let X := componentOrbit D (oddELayer Gi)
    IsComponent Gi X ∧ ∃ a : MulAut X,
      (∀ y : X, ((a y : Gi) : G) = t * ((y : Gi) : G) * t⁻¹) ∧
      Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨_,hX,a,ha,hact,hB,⟨eKB⟩⟩ := source_a6_marked_pumpup_invariant
    c hG hempty hgen hb hstar eK t i ht htC htZ hi.2.1 hi.1.1 hi.1.2 hi.2.2
  let Gi := centralizer ({i} : Set G)
  let D := K.subgroupOf Gi
  let X := componentOrbit D (oddELayer Gi)
  let B := (D.subgroupOf X).subgroupOf a.fixedSubgroup
  have hKi : K ≤ Gi := fun k hk => mem_centralizer_singleton_iff.mpr (hi.1.2 k hk)
  have hKX : K ≤ X.map Gi.subtype := by
    intro k hk
    exact ⟨⟨k,hKi hk⟩,le_componentOrbit D (oddELayer Gi) hk,rfl⟩
  have hm := source_a8_or_hs_quotient c hG hempty hgen hb t zK ht hzK htC htZ hzKK hz
    i hi.2.1 X hX a ha hact B hB.2 eKB eK hKX
  refine ⟨hX,a,hact,?_⟩
  rcases hm with hA8 | ⟨e,hmark⟩
  · exact hA8
  · let x : X := ⟨⟨zK,hKi hzKK⟩,le_componentOrbit D (oddELayer Gi) hzKK⟩
    let k : B := ⟨⟨x,hB.1 hzKK⟩,hzKK⟩
    have hk : orderOf k = 2 := by
      have hh : orderOf ((((k : a.fixedSubgroup) : X) : Gi) : G) = 2 := hzK
      simpa only [Subgroup.orderOf_coe] using hh
    have hcross : z = t * ((((k : a.fixedSubgroup) : X) : Gi) : G) := hz
    exact (HS.source_hs_crossing_false c hgen t i ht htC htZ X hX e a hact hmark
      B hB.2 (eKB.symm.trans eK) k hk hcross).elim

/-- Every bad involution has its literal larger orbit isomorphic to A₈. -/
theorem source_bad_involution_a8_orbit
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* alternatingGroup (Fin 6))
    (t zK : G) (ht : orderOf t = 2) (hzK : orderOf zK = 2)
    (htC : t ∈ twoCore H) (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hzKK : zK ∈ K) (hz : z = t * zK)
    (i : G) (hi : BadInvolution ((S : Subgroup H).map H.subtype) K i) :
    Nonempty (((componentOrbit (K.subgroupOf (centralizer ({i} : Set G)))
      (oddELayer (centralizer ({i} : Set G)))).map
      (centralizer ({i} : Set G)).subtype) ≃* alternatingGroup (Fin 8)) := by
  obtain ⟨hX,a,hact,⟨eQ⟩⟩ := source_bad_involution_a8_row
    c hG hempty hgen hb hstar eK t zK ht hzK htC htZ hzKK hz i hi
  let Gi := centralizer ({i} : Set G)
  let D := K.subgroupOf Gi
  let X := componentOrbit D (oddELayer Gi)
  have hKi : K ≤ Gi := fun k hk => mem_centralizer_singleton_iff.mpr (hi.1.2 k hk)
  let : IsQuasisimple X := hX.2
  obtain ⟨eX⟩ := a8_model_of_quotient D X (le_componentOrbit D (oddELayer Gi))
    ((subgroupOfEquivOfLe hKi).trans eK) eQ
  exact ⟨(X.equivMapOfInjective Gi.subtype Gi.subtype_injective).symm.trans eX⟩

/-- Original full-A₆ alternatives, with all containing-model premises removed.
The centralizer equality comes from the maximal bad involution; all other
rows are excluded by fusion with the original crossing mark. -/
theorem source_full_a6_overcomponent
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* alternatingGroup (Fin 6))
    (t zK : G) (ht : orderOf t = 2) (hzK : orderOf zK = 2)
    (htC : t ∈ twoCore H) (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hzKK : zK ∈ K) (hz : z = t * zK)
    (i : G) (hi : BadInvolution ((S : Subgroup H).map H.subtype) K i) :
    (twoCore H ⊓ centralizer ({i} : Set G) = zpowers i ⊔ zpowers t) ∧
      ∃ E : Subgroup G, IsComponentIn E (centralizer ({i} : Set G)) ∧
        ∃ e : E ≃* alternatingGroup (Fin 8),
          (∀ k : E, (e.symm (MulAut.conjNormal (Equiv.swap (0 : Fin 8) 1) (e k)) : G) =
            t * k * t⁻¹) ∧
          K = (solvableResidual (E ⊓ centralizer ({t} : Set G) : Subgroup G)).map
            (E ⊓ centralizer ({t} : Set G)).subtype := by
  have hc := source_a8_orbits_centralizer_four c hG hempty hgen hb hstar eK
    (source_bad_involution_a8_orbit c hG hempty hgen hb hstar eK t zK ht hzK htC htZ hzKK hz)
    t ht htC htZ i hi
  let : (K.subgroupOf H).Normal := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) (K.subgroupOf H)
    ((subgroupOfEquivOfLe c.component_le).trans eK) c.component
  have hcore := MathieuSourceSetup.core_eq_sylow_centralizer c hgen
  refine ⟨by simpa only [← hcore] using hc.1,?_⟩
  obtain ⟨hX,a,hact,⟨eQ⟩⟩ := source_bad_involution_a8_row
    c hG hempty hgen hb hstar eK t zK ht hzK htC htZ hzKK hz i hi
  let Gi := centralizer ({i} : Set G)
  let D := K.subgroupOf Gi
  let X := componentOrbit D (oddELayer Gi)
  have hKi : K ≤ Gi := fun k hk => mem_centralizer_singleton_iff.mpr (hi.1.2 k hk)
  have hKX : K ≤ X.map Gi.subtype := by
    intro k hk
    exact ⟨⟨k,hKi hk⟩,le_componentOrbit D (oddELayer Gi) hk,rfl⟩
  exact source_a8_marked_overcomponent K t i ht
    (source_component_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ)
    eK X hX a hact hKX eQ

end CFSG.Quasithin.Chapter2.Section05.Overcomponents.FullA6
