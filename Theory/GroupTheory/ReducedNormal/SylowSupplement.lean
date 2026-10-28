module
public import Theory.GroupTheory.ReducedNormal.Detection
public import Theory.GroupTheory.ReducedNormal.Basic
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.ReducedNormal.RelativeDetection

/-!
# A Sylow supplement detects the two-core through R₂

A normal elementary detecting module gives C_K(R₂(G)) = O₂(K) by
A.1.19. If a Sylow two-subgroup supplements K, the ambient centralizer
of R₂(G) is a two-group and hence equals O₂(G). The ambient adapter
keeps the literal subgroup inclusion and its centralizer quotient.

Source: Aschbacher--Smith A.1.19 and 13.7.4(1), printed pp.24,937.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A normal elementary detecting module for a Sylow supplement makes R₂(G)
detect the whole two-core. -/
theorem centralizer_reducedTwo_eq_core_of_sylow_supplement
    (K U : Subgroup G) [K.Normal] [U.Normal] [IsElementaryAbelian 2 U]
    (S : Sylow 2 G) (hgen : K ⊔ (S : Subgroup G) = ⊤)
    (hc : K ⊓ centralizer (U : Set G) = K.pCoreIn 2) :
    centralizer (reducedTwoSubgroup G : Set G) = pCore 2 G := by
  obtain ⟨W, hWU, hr, hw⟩ := exists_isPReduced_le_centralizer_eq_core K U hc
  have hCK : K ⊓ centralizer (reducedTwoSubgroup G : Set G) ≤ K.pCoreIn 2 :=
    (inf_le_inf_left K (centralizer_le hr.le_reducedPSubgroup)).trans_eq hw
  let C := centralizer (reducedTwoSubgroup G : Set G)
  let f : C →* G ⧸ K := (QuotientGroup.mk' K).comp C.subtype
  have hk : IsPGroup 2 f.ker := by
    apply (isPGroup_pCoreIn 2 K).comap_subtype.to_le
    intro x hx
    have hxK : (x : G) ∈ K := (QuotientGroup.eq_one_iff (x : G)).mp hx
    exact hCK ⟨hxK,x.property⟩
  have hQ : IsPGroup 2 (G ⧸ K) := isPGroup_quotient_of_sup_eq_top K S S.isPGroup' hgen
  have hC : IsPGroup 2 C := by
    have hp := (hQ.to_subgroup (⊤ : Subgroup (G ⧸ K))).comap_of_ker_isPGroup f hk
    have ht : (⊤ : Subgroup (G ⧸ K)).comap f = ⊤ := comap_top f
    exact hp.of_equiv ((MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv)
  exact le_antisymm (le_sSup ⟨inferInstance,hC⟩)
    (le_centralizer_iff.mp (reducedPSubgroup_le_centralizer_pCore 2 G))


/-- The ambient form of the detector, after restricting to a subgroup X.
A Sylow subgroup of X generating with K transfers the identity back to G. -/
theorem centralizer_reducedTwo_eq_pCoreIn_of_sylow_supplement
    (K X R : Subgroup G) (hKX : K ≤ X) (hRX : R ≤ X)
    (hXK : X ≤ normalizer (K : Set G))
    (hXR : X ≤ normalizer (R : Set G))
    (hcentral : K ⊓ centralizer (R : Set G) = K.pCoreIn 2)
    [hR : IsElementaryAbelian 2 R]
    (S : Sylow 2 X) (hgen : K.subgroupOf X ⊔ (S : Subgroup X) = ⊤) :
    X ⊓ centralizer ((reducedTwoSubgroup X).map X.subtype : Set G) = X.pCoreIn 2 := by
  let KX := K.subgroupOf X
  let RX := R.subgroupOf X
  let : KX.Normal := normal_subgroupOf_of_le_normalizer hXK
  let : RX.Normal := normal_subgroupOf_of_le_normalizer
    (by simpa only [subgroupOf_normalizer_eq] using hXR)
  let : IsElementaryAbelian 2 RX := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hRX).toMonoidHom (subgroupOfEquivOfLe hRX).injective
  have hcore : KX ⊓ centralizer (RX : Set X) = KX.pCoreIn 2 := by
    apply map_injective X.subtype_injective
    rw [map_inf _ _ _ X.subtype_injective, map_centralizer_subtype,
      map_pCoreIn_of_injective 2 KX X.subtype X.subtype_injective,
      map_subgroupOf_eq_of_le hKX, map_subgroupOf_eq_of_le hRX,
      ← inf_assoc, inf_eq_left.mpr hKX, hcentral]
  have he := centralizer_reducedTwo_eq_core_of_sylow_supplement
    KX RX S hgen hcore
  have hem := congrArg (Subgroup.map X.subtype) he
  rw [map_centralizer_subtype] at hem
  change X ⊓ centralizer ((reducedTwoSubgroup X).map X.subtype : Set G) =
    (pCore 2 X).map X.subtype
  exact hem

end Theory.GroupTheory
