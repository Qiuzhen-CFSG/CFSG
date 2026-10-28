module
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.NormalCenterSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.TwoComponentCenterSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.FourMarksSource
/-! # Complete original center marks in source 2.5.8 and 2.5.11
The normal and two-component branches give the same literal orbit-center
split. The disjoint-conjugate core argument then constructs the unique core
involution and the original marked projection, with both central four-group
bases, Z(T)=⟨z⟩, and the exact ambient involution centralizer and Sylow.
All center decomposition and cardinality inputs are discharged internally.
Source: Aschbacher--Smith, printed pp.557--558.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open Subgroup Theory.GroupTheory ComponentRefinement
variable {G:Type*} [Group G] [Finite G] {H L M:Subgroup G} {S:Sylow 2 H} {z:G}

theorem MathieuSourceSetup.component_orbit_center_split
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel L) :
    let Y:=(S:Subgroup H).map H.subtype
    let D:=componentOrbit L Y
    let Z:=centerIn Y
    Z=(Z⊓D)⊔(Z⊓twoCore H) ∧ Disjoint (Z⊓D) (Z⊓twoCore H) ∧
      Nat.card (Z⊓D:Subgroup G)=2 ∧
      ∃d:G,orderOf d=2 ∧ Z⊓D=zpowers d ∧ d⁻¹*z∈Z⊓twoCore H := by
  let Y:=(S:Subgroup H).map H.subtype
  by_cases hn:(L.subgroupOf H).Normal
  · let :=hn
    have hYL:Y≤normalizer (L:Set G):=(map_subtype_le _).trans
      ((normal_subgroupOf_iff_le_normalizer c.component_le).mp hn)
    have ho:componentOrbit L Y=L:=le_antisymm
      (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hYL) (le_componentOrbit _ _)
    obtain ⟨hs,hd,hc,_⟩:=MathieuSourceSetup.normal_component_center_split c hG hempty hgen hb
    obtain ⟨t,d,hHt,hz,hd2,hdZ,ht,htC⟩:=MathieuSourceSetup.normal_component_central_projection c hG hempty hgen
    have hline:centerIn Y⊓L=zpowers d:=by
      have hle:zpowers d≤centerIn Y⊓L:=zpowers_le.mpr ⟨hdZ.2,hdZ.1⟩
      apply (eq_of_le_of_card_ge hle ?_).symm
      rw [hc,Nat.card_zpowers,hd2]
    have htz:t∈centerIn Y:=by
      rw [ht]
      have hh:=c.localSetup hG structural115Input localC129Input_knownSimple
      exact (centerIn Y).mul_mem ((centerIn Y).inv_mem hdZ.2) ⟨hh.mem_sylow,hh.central⟩
    dsimp only
    change centerIn Y=(centerIn Y⊓componentOrbit L Y)⊔(centerIn Y⊓twoCore H) ∧ _
    rw [ho]
    exact ⟨hs,hd,hc,d,hd2,hline,ht ▸ ⟨htz,htC⟩⟩
  · obtain ⟨hs,hd,hc,_,hdm⟩:=MathieuSourceSetup.nonnormal_component_center_split c hG hempty hgen hb hn
    exact ⟨hs,hd,hc,hdm⟩

theorem MathieuSourceSetup.source_central_marks
    (c:MathieuSourceSetup H L M S z)
    (hG:IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty:gammaEvenZero (Chapter1.He G) M=∅)
    (hgen:H=L⊔(S:Subgroup H).map H.subtype)
    (hb:¬ClassificationModels.IsBenderModel L) :
    let Y:=(S:Subgroup H).map H.subtype
    let D:=componentOrbit L Y
    ∃t zK:G,orderOf t=2 ∧ orderOf zK=2 ∧ t∈twoCore H ∧
      centerIn Y⊓twoCore H=zpowers t ∧ centerIn Y⊓D=zpowers zK ∧
      centerIn Y=zpowers t⊔zpowers z ∧ centerIn Y=zpowers t⊔zpowers zK ∧
      IsKleinFour (centerIn Y) ∧ centerIn (c.T:Subgroup G)=zpowers z ∧
      H≤centralizer ({t}:Set G) ∧
      centralizer ({t}:Set G)∈gammaZero (Chapter1.He G) M ∧
      (∃P:Sylow 2 (centralizer ({t}:Set G)),
        (P:Subgroup (centralizer ({t}:Set G))).map (centralizer ({t}:Set G)).subtype=Y) ∧
      (H∈gammaStar (Chapter1.He G) M→centralizer ({t}:Set G)∈gammaStar (Chapter1.He G) M) ∧
      ¬IsConj t z := by
  let Y:=(S:Subgroup H).map H.subtype
  let D:=componentOrbit L Y
  obtain ⟨hs,hd,hc,d,hd2,hline,hres⟩:=MathieuSourceSetup.component_orbit_center_split c hG hempty hgen hb
  obtain ⟨hfour,hCtwo⟩:=MathieuSourceSetup.center_four_of_center_split c hgen (centerIn Y⊓D) hs hd hc
  obtain ⟨t,ht,htC,hcore,hspan,hE,hZT⟩:=MathieuSourceSetup.marked_center_pair_of_four c hG hempty hgen hfour hCtwo
  have htZ:t∈centerIn Y:=(zpowers_le.mp (hcore ▸ (show centerIn Y⊓twoCore H≤centerIn Y from inf_le_left)))
  have hspanD:centerIn Y=zpowers t⊔zpowers d:=by
    rw [hs,hline,hcore,sup_comm]
  exact ⟨t,d,ht,hd2,htC,hcore,hline,hspan,hspanD,hE,hZT,
    MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ⟩
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
