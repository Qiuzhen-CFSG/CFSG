module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterSplit
public import Theory.GroupTheory.ComponentInverterCyclicCentralizer
/-!
# The centralizer of the selected PSL₃(3) involution

The source central-core theorem places H inside C_G(t) and supplies its
original Sylow subgroup. Persistence makes K a normal component of C_G(t).
The original z belongs to K and inverts the odd core, forcing that core to
be trivial. The component centralizer has cyclic Sylow ⟨t⟩ and is therefore
contained in the supplied Sylow. The outer two-group theorem then gives
C_G(t)=KS=H on the actual ambient carrier.
Source: Aschbacher--Smith 2.5.15, printed p.559.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem linear_three_source_centralizer_eq
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H=K⊔(S:Subgroup H).map H.subtype)
    (e : K≃*Matrix.PSL3Three.PSL) (hzK : z∈K)
    (t : G) (ht : orderOf t=2) (htC : t∈twoCore H)
    (htZ : t∈centerIn ((S:Subgroup H).map H.subtype))
    (hcore : twoCore H=zpowers t) : centralizer ({t}:Set G)=H := by
  let Y := (S:Subgroup H).map H.subtype
  let J := centralizer ({t}:Set G)
  obtain ⟨hHJ,hgamma,⟨P,hP⟩,_,_⟩ := MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ
  obtain ⟨hKJ,hn,_⟩ := MathieuSourceSetup.small_component_centralizer_residual c hG hempty hgen
    (Or.inl ⟨e⟩) t ht htC htZ
  let K0 := K.subgroupOf J
  let : K0.Normal := hn
  have h115 := ComponentSelection.NonEnlargement.hypotheses115_of_same_sylow hG c.T c.maximal c.sylow_le c.unique
    (MathieuSourceSetup.sourceTuple c) hgamma P hP
  let zJ : J := ⟨z,hKJ.1 hzK⟩
  have hzJ : orderOf zJ=2 := by simpa only [zJ,Subgroup.orderOf_mk] using c.involution
  have hodd : pPrimeCore 2 J=⊥ := oddCore_eq_bot_of_component_involution_inverts K0 hKJ.2 zJ hzK hzJ
    (fun u hu => Subtype.ext (h115.inverts_oddCore u hu))
  have hk0e : K0≃*Matrix.PSL3Three.PSL := (subgroupOfEquivOfLe hKJ.1).trans e
  have hout : IsPGroup 2 (MulAut.Outer K0) :=
    Matrix.PSL3Three.outer_isTwoGroup.of_equiv (MulAut.outerCongr hk0e).symm
  let D := centralizer (K0:Set J)
  have hCeq : Y⊓centralizer (K:Set G)=twoCore H := by
    have hKN : Y≤normalizer (K:Set G) := (map_subtype_le _).trans
      ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
    have horbit : componentOrbit K Y=K := le_antisymm
      (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hKN) (le_componentOrbit _ _)
    have hh := generated_orbit_core ⟨c.component_le,c.component⟩ S hgen
    rwa [horbit] at hh
  let V := (P:Subgroup J).subgroupOf D
  let f : V→*twoCore H := ((J.subtype.comp D.subtype).comp V.subtype).codRestrict _ (by
    intro v
    rw [←hCeq]
    refine ⟨?_,?_⟩
    · change ((v.val.val : J) : G)∈Y
      have hh := mem_map_of_mem J.subtype v.property
      change ((v.val.val : J) : G)∈(P:Subgroup J).map J.subtype at hh
      rw [hP] at hh
      exact hh
    · intro k hk
      exact congrArg Subtype.val (v.val.property (⟨k,hKJ.1 hk⟩:J) hk))
  let : IsCyclic (twoCore H) := hcore.symm ▸ inferInstance
  have hcyc : IsCyclic V := isCyclic_of_injective f (by
    intro a b hab
    have he := congrArg (fun q:twoCore H=>(q:G)) hab
    exact Subtype.ext (Subtype.ext (Subtype.ext he)))
  let tJ : J := ⟨t,mem_centralizer_singleton_iff.mpr rfl⟩
  have htD : tJ∈D := by
    intro k hk
    apply Subtype.ext
    have htK : t∈centralizer (K:Set G) := by
      rw [←hCeq] at htC
      exact htC.2
    exact htK k hk
  have heven : 2∣Nat.card D := by
    have ho : orderOf tJ=2 := by simpa only [tJ,Subgroup.orderOf_mk] using ht
    exact ho ▸ D.orderOf_dvd_natCard htD
  have htop := normal_sylow_sup_eq_top_of_cyclic_centralizer_restriction K0 P hout hcyc heven hodd
  have hm := congrArg (Subgroup.map J.subtype) htop
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hKJ.1,hP,
    ←MonoidHom.range_eq_map,J.range_subtype,←hgen] at hm
  exact hm.symm
end CFSG.Quasithin.Chapter2.Section05
