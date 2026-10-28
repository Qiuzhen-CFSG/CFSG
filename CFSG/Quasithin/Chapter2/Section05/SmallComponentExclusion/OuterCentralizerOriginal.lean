module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterCentralizer
/-!
# The original source centralizer equality with all marks selected

The source center theorem chooses t and the component projection k. The
proved splitting family identifies k=z and O₂(H)=⟨t⟩. Applying the local
centralizer theorem then gives the literal equality C_G(t)=H, retaining the
same chosen t and the original nonfusion of t and z.
Source: Aschbacher--Smith 2.5.15, printed p.559.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M U L : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem linear_three_source_centralizer_mark
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (e : K ≃* Matrix.PSL3Three.PSL) :
    z∈K ∧ ∃ t:G,orderOf t=2 ∧ t∈twoCore H ∧
      t∈centerIn ((S:Subgroup H).map H.subtype) ∧ twoCore H=zpowers t ∧
      centralizer ({t}:Set G)=H ∧ ¬IsConj t z := by
  let Y := (S : Subgroup H).map H.subtype
  obtain ⟨t,k,ht,hk,htC,hcore,hline,_,hspanK,hZ,_⟩ :=
    ComponentSelection.MathieuSourceSetup.source_central_marks c hG hempty hgen hb
  have htZ : t ∈ centerIn Y := by
    have hh : t ∈ centerIn Y ⊓ twoCore H := hcore ▸ mem_zpowers t
    exact hh.1
  have hKY : Y ≤ normalizer (K : Set G) := (map_subtype_le _).trans
    ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance)
  have horbit : componentOrbit K Y = K := le_antisymm
    (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hKY) (le_componentOrbit _ _)
  have hkZK : k ∈ centerIn Y ⊓ K := by
    rw [horbit] at hline
    exact hline ▸ mem_zpowers k
  let zK : K := ⟨k,hkZK.2⟩
  have hzK : orderOf zK = 2 := by simpa only [zK,Subgroup.orderOf_mk] using hk
  have hN := linear_three_source_core_eq_central_involution c hG hempty hgen hb hp hUS e
    t ht htC htZ hZ zK hzK hkZK.1 hspanK
  have hez := (linear_three_source_marked_split c hG hempty hgen hb hp hUS e
    t ht htC htZ hZ zK hzK hkZK.1 hspanK).1
  have hzK' : z∈K := hez ▸ zK.property
  exact ⟨hzK',t,ht,htC,htZ,hN,
    linear_three_source_centralizer_eq c hG hempty hgen e hzK' t ht htC htZ hN,
    (MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ).2.2.2.2⟩
end CFSG.Quasithin.Chapter2.Section05
