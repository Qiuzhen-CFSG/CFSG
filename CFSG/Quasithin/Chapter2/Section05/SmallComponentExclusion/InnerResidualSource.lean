module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.InnerMarkedSource
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.ResidualCharacteristic

/-!
# Inner-action exclusion from the preceding ambient residual theorem

The prior 2.5.6/A.3.18 output identifies the actual normal component K as
O^{3′}(C_G(t)). The original center basis then makes O²(C_K(zK)) characteristic
in C_G(Z(S)), hence invariant under every Sylow-normalizing crossing. A finite
two-group supplies such a crossing, and the marked inner contradiction applies.
The sole additional mathematical input is that precise earlier residual identity;
its producer belongs to the preceding small-component persistence theorem.
Source: Aschbacher--Smith 2.5.15(i), printed pp.558--559.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection
open ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M U L : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem small_component_inner_residual_false
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (hK : Nonempty (K ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (K ≃* Sporadic.Mathieu.M11))
    (hinner : (S : Subgroup H).map H.subtype ≤ K ⊔ centralizer (K : Set G))
    (t : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hZ : IsKleinFour (centerIn ((S : Subgroup H).map H.subtype)))
    (zK : K) (hzK : orderOf zK = 2)
    (hzS : (zK : G) ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hspan : centerIn ((S : Subgroup H).map H.subtype) = zpowers t ⊔ zpowers (zK : G))
    (hres : K = (primeToResidual 3 (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype) : False := by
  obtain ⟨x,hxT,hxS,hxN,_⟩ := exists_outside_normalizer_square_mem
    ((S : Subgroup H).map H.subtype) c.T c.T.isPGroup' c.sylow_lt
  exact small_component_inner_marked_false c hG hempty hgen hb hp hUS hK hinner
    t ht htC htZ hZ zK hzK hzS hxT hxS hxN
    (local_residual_normalized_by_sylow_normalizer K _ hK zK hzK t hspan hres hxN)

/-- In the Mathieu case innerness is automatic on the literal component. -/
theorem mathieu_component_residual_false
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype) (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H) (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (e : K ≃* Sporadic.Mathieu.M11)
    (t : G) (ht : orderOf t = 2) (htC : t ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hZ : IsKleinFour (centerIn ((S : Subgroup H).map H.subtype)))
    (zK : K) (hzK : orderOf zK = 2)
    (hzS : (zK : G) ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hspan : centerIn ((S : Subgroup H).map H.subtype) = zpowers t ⊔ zpowers (zK : G))
    (hres : K = (primeToResidual 3 (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype) : False :=
  small_component_inner_residual_false c hG hempty hgen hb hp hUS (Or.inr ⟨e⟩)
    (mathieu_source_sylow_inner_cover c e) t ht htC htZ hZ zK hzK hzS hspan hres

end CFSG.Quasithin.Chapter2.Section05
