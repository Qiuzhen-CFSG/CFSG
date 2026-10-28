module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentEnvelope
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentFixedIndex
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentQuotient
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentNormality.A8
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.CentralizerSource

/-!
# Component normality in the paired cubic involution centralizers

Balance lifts the original normal A₆ into a normal component of C_G(r).
If that component is larger, the original Thompson geometry bounds the
Sylow fixed index by four. The genuine fixed-A₆ quotient census then
forces A₈, where compatible source markings produce a commuting A₄ and
the forbidden local cubic rank three. Thus the containing component is
exactly the original K.

The correlated-geometry endpoint supplies the literal normalizer inclusion
needed in the remainder of source36. Its transposition mark discharges the
preceding opposite-module noncentrality. The final theorem applies this
normality directly to the proved cyclic-centralizer consumer.

Source: Aschbacher–Smith 2.4.36, printed p.549, using I.3.2 and A.3.18.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem SourceCentralizerGeometry.component_centralizer_normalizes
    {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}
    (g : SourceCentralizerGeometry c)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K : Subgroup (involutionCentralizer g.z₂)) [K.Normal]
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (hLK : d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype)
    (eK : K ≃* alternatingGroup (Fin 6))
    (hVK : ¬ c.U₂.subgroupOf (involutionCentralizer g.z₂) ≤
      centralizer (K : Set (involutionCentralizer g.z₂)))
    (r : involutionCentralizer g.z₂)
    (hrR : r ∈ (sourceR d).subgroupOf (involutionCentralizer g.z₂))
    (hrK : r ∈ centralizer (K : Set (involutionCentralizer g.z₂)))
    (hr2 : orderOf r = 2) :
    centralizer ({(r : G)} : Set G) ≤
      normalizer (K.map (involutionCentralizer g.z₂).subtype : Set G) := by
  let H := involutionCentralizer g.z₂
  let C := centralizer ({(r : G)} : Set G)
  let L := K.map H.subtype
  have hr2G : orderOf (r : G) = 2 := (Subgroup.orderOf_coe r).trans hr2
  have hrL : (r : G) ∈ centralizer (L : Set G) := by
    rintro _ ⟨k,hk,rfl⟩
    exact congrArg Subtype.val (hrK k hk)
  have hLC : L ≤ C := by
    intro k hk
    exact mem_centralizer_singleton_iff.mpr (hrL k hk)
  have hzC : g.z₂ ∈ C :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp r.property).symm
  let z : C := ⟨g.z₂,hzC⟩
  have hz : orderOf z = 2 := (Subgroup.orderOf_coe z).symm.trans g.order_second
  obtain ⟨J,hJ,hnJ,hLJ⟩ := normal_component_envelope hG g.z₂
    (g.order_second ▸ pow_orderOf_eq_one g.z₂) K eK r hrK hr2
  let : J.Normal := hnJ
  let : IsQuasisimple J := hJ.2
  let E := J.map C.subtype
  have hCE : C ≤ normalizer (E : Set G) := by
    have hh := J.le_normalizer_map C.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  let A := L.subgroupOf C
  have hAJ : A ≤ J := by
    intro a ha
    obtain ⟨j,hj,he⟩ := hLJ ha
    exact C.subtype_injective he ▸ hj
  by_cases he : A = J
  · have hLE : L = E := by
      have hh := congrArg (Subgroup.map C.subtype) he
      simpa only [A,map_subgroupOf_eq_of_le hLC] using hh
    change C ≤ normalizer (L : Set G)
    rw [hLE]
    exact hCE
  have hlt : A < J := lt_of_le_of_ne hAJ he
  have hnot : C ∉ Chapter1.He G := fun hc =>
    not_isComponent_of_twoCore (Chapter1.mem_He_iff.mp hc) J hJ
  have hRindex := g.component_centralizer_index_le_two K hLK (r : G) hrR hr2G hrL
  obtain ⟨P,_,hi⟩ := g.exists_sylow_fixed_index_le_four hG (r : G) hr2G hRindex hnot
  have hi' : (centralizer ({z} : Set C)).relIndex (P : Subgroup C) ≤ 4 := by
    have hc : centralizer ({z} : Set C) = (centralizer ({g.z₂} : Set G)).comap C.subtype := by
      ext x
      rw [mem_centralizer_singleton_iff]
      change x * z = z * x ↔ (x : G) ∈ centralizer ({g.z₂} : Set G)
      rw [mem_centralizer_singleton_iff]
      exact Subtype.ext_iff
    rw [hc,relIndex_comap]
    exact hi
  let fL : K ≃* L := K.equivMapOfInjective H.subtype H.subtype_injective
  let eA : A ≃* alternatingGroup (Fin 6) :=
    (subgroupOfEquivOfLe hLC).trans (fL.symm.trans eK)
  have hAz : A ≤ centralizer ({z} : Set C) := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp ((map_subtype_le K) ha)
  have hHN : H ≤ normalizer (L : Set G) := by
    have hh := K.le_normalizer_map H.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hnorm : centralizer ({z} : Set C) ≤ normalizer (A : Set C) := by
    intro y hy
    have hyH : (y : G) ∈ H := mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy))
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (hHN hyH) (a : G)
  let : IsQuasisimple K := hK.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv fL
  let : IsQuasisimple A := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLC).symm
  have hAc : IsComponentIn A (centralizer ({z} : Set C)) := by
    refine ⟨hAz,?_,?_⟩
    · exact (normal_subgroupOf_of_le_normalizer hnorm).isSubnormal
    · exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hAz).symm
  obtain ⟨eQ⟩ := proper_fixed_component_quotient_alternating_eight J A
    ((hG.involution_centralizer_sqtk hr2G).subgroup J) z hz hAc hlt eA P hi'
  let f : J ≃* E := J.equivMapOfInjective C.subtype C.subtype_injective
  let : IsQuasisimple E := IsQuasisimple.of_mulEquiv f
  have hcenter : (center J).map f.toMonoidHom = center E := by
    apply le_antisymm
    · rintro _ ⟨j,hj,rfl⟩
      exact (centerCongr f ⟨j,hj⟩).property
    · intro e he
      exact ⟨f.symm e,(centerCongr f).symm ⟨e,he⟩ |>.property,f.apply_symm_apply e⟩
  let eQE : (E ⧸ center E) ≃* alternatingGroup (Fin 8) :=
    (QuotientGroup.congr _ _ f hcenter).symm.trans eQ
  have hLH : IsComponentIn L H := by
    refine ⟨map_subtype_le _,?_⟩
    change IsComponent H ((K.map H.subtype).comap H.subtype)
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  exact (ComponentNormality.A8.contradiction_of_original hG g K hK hLK eK hVK E
    (hLH.restrict (le_inf hLJ hLH.1) inf_le_right) (hCE hzC) eQE).elim

/-- The source36 premise on the same correlated source geometry used by
its downstream cyclic-centralizer and factor consumer. -/
theorem SourceCentralizerGeometry.component_centralizer_normality_of_geometry
    {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}
    (g : SourceCentralizerGeometry c)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (b : SourceComponentGeometry d) (hbz : b.z = g.z₂)
    (hu : (b.u : G) ∈ c.U₂)
    (hLK : d.block.map d.H.subtype ≤ b.K.map (involutionCentralizer b.z).subtype) :
    ∀ r : involutionCentralizer b.z,
      r ∈ (sourceR d).subgroupOf (involutionCentralizer b.z) →
      r ∈ centralizer (b.K : Set (involutionCentralizer b.z)) → orderOf r = 2 →
      centralizer ({(r : G)} : Set G) ≤
        normalizer (b.K.map (involutionCentralizer b.z).subtype : Set G) := by
  have aux (z : G) (hz : z = g.z₂)
      (K : Subgroup (involutionCentralizer z)) (hn : K.Normal)
      (hK : IsComponent (involutionCentralizer z) K)
      (hL : d.block.map d.H.subtype ≤ K.map (involutionCentralizer z).subtype)
      (eK : K ≃* alternatingGroup (Fin 6))
      (hV : ¬ c.U₂.subgroupOf (involutionCentralizer z) ≤
        centralizer (K : Set (involutionCentralizer z))) :
      ∀ r : involutionCentralizer z,
        r ∈ (sourceR d).subgroupOf (involutionCentralizer z) →
        r ∈ centralizer (K : Set (involutionCentralizer z)) → orderOf r = 2 →
        centralizer ({(r : G)} : Set G) ≤
          normalizer (K.map (involutionCentralizer z).subtype : Set G) := by
    subst z
    let : K.Normal := hn
    exact g.component_centralizer_normalizes hG K hK hL eK hV
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (alternatingGroup (Fin 6)) := {
    simple := ((QuotientGroup.quotientMulEquivOfEq (alternatingGroup.center_eq_bot (by simp))).trans
      QuotientGroup.quotientBot).isSimpleGroup }
  have hK : IsComponent (involutionCentralizer b.z) b.K :=
    ⟨b.normal.isSubnormal,IsQuasisimple.of_mulEquiv b.componentEquiv.symm⟩
  have hV : ¬ c.U₂.subgroupOf (involutionCentralizer b.z) ≤
      centralizer (b.K : Set (involutionCentralizer b.z)) := by
    intro h
    have hc := h hu
    have hk : b.u ∈ (AlternatingSix.ShadowLocal.conjugationAction b.K b.componentEquiv).ker := by
      rwa [AlternatingSix.ShadowLocal.conjugationAction_ker]
    have he := MonoidHom.mem_ker.mp hk
    rw [b.transposition] at he
    have hs : b.σ = 1 := AlternatingSix.ShadowLocal.permutationAction_injective
      (he.trans (map_one _).symm)
    have hh := b.swap.sign_eq
    rw [hs] at hh
    norm_num at hh
  exact aux b.z hbz b.K b.normal hK hLK b.componentEquiv hV

/-- Original source36, before the source37 fusion argument. The actual
component-centralizer normality premise is fully discharged. -/
theorem SourceCentralizerGeometry.component_centralizer_cyclic_four_from_source
    {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}
    (g : SourceCentralizerGeometry c)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (b : SourceComponentGeometry d) (hz : b.z = g.z₂)
    (hs : b.s = c.s⁻¹) (hu : (b.u : G) ∈ c.U₂)
    (hLK : d.block.map d.H.subtype ≤ b.K.map (involutionCentralizer b.z).subtype) :
    Nat.card c.D = 1 ∧ Nat.card (sourceR d) = 64 ∧
      Nonempty (((sourceR d).subgroupOf (involutionCentralizer b.z) ⊓
        centralizer (b.K : Set (involutionCentralizer b.z)) : Subgroup (involutionCentralizer b.z)) ≃*
          Multiplicative (ZMod 4)) :=
  g.component_centralizer_cyclic_four b hz hs hu hLK hG.quasithin
    (g.component_centralizer_normality_of_geometry hG b hz hu hLK)

end CFSG.Quasithin.Chapter2.DoubleA3
