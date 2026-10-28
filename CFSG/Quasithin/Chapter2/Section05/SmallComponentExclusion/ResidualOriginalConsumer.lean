module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.InnerResidualSource
/-!
# Original Mathieu source exclusion after the earlier residual identity

The source center theorem chooses both involutions and both central bases.
The original component orbit is K by normality. Thus the complete marked
inner contradiction applies, leaving only the genuine earlier 2.5.6/A.3.18
statement that this K is O^{3′}(C_G(t)); every other marking and local fact
is constructed from the original tuple and its largest pair.
Source: Aschbacher--Smith 2.5.15, printed pp.558--559.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection
open ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M U L : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem mathieu_component_false_of_source_residual
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (e : K ≃* Sporadic.Mathieu.M11)
    (hres : ∀ t : G, orderOf t = 2 → t ∈ twoCore H →
      t ∈ centerIn ((S : Subgroup H).map H.subtype) →
      K = (primeToResidual 3 (centralizer ({t} : Set G))).map
        (centralizer ({t} : Set G)).subtype) : False := by
  let Y := (S : Subgroup H).map H.subtype
  obtain ⟨t,k,ht,hk,htC,hcore,hline,hspan,hspanK,hZ,_,_⟩ :=
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
  exact mathieu_component_residual_false c hG hempty hgen hb hp hUS e t ht htC htZ hZ
    zK hzK hkZK.1 hspanK (hres t ht htC htZ)
end CFSG.Quasithin.Chapter2.Section05
