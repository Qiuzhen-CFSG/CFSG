module
public import Theory.GroupTheory.PCoreNormalizerAction
public import Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.PCoreRestriction

/-!
# Elementary actors meet the normal A₅ square

For a normal subgroup K of H, a two-group kernel of the action on
K/O₂(K) is exactly O₂(H). When this quotient is the actual A₅ square,
an elementary image of order greater than four contains a nontrivial
inner automorphism. Lifting it gives an element in K O₂(H) outside O₂(H).
An order-sixteen image contained in the square is a Sylow subgroup there.

The tensor point-core argument uses this with its original upper-layer
irreducibility to place the entire offender in the square. All maps use
the original subgroup and the full ambient core.
Source: Aschbacher--Smith 8.3.12, printed p.726, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A two-group full section-action kernel is the entire ambient two-core. -/
theorem pCoreNormalizerAction_restrict_ker_eq_twoCore (H K : Subgroup G)
    (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G))
    (hker : IsPGroup 2 ((pCoreNormalizerAction 2 K).comp (inclusion hHK)).ker) :
    ((pCoreNormalizerAction 2 K).comp (inclusion hHK)).ker = pCore 2 H := by
  refine le_antisymm ?_ ?_
  · exact le_sSup ⟨inferInstance,hker⟩
  intro a ha
  apply (pCoreNormalizerAction_eq_one_iff 2 K (inclusion hHK a)).mpr
  intro k
  have hQN : H ≤ normalizer (H.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn,normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (pCore 2 H).le_normalizer_map H.subtype
  have hQ : (a : G) ∈ H.pCoreIn 2 := mem_map_of_mem H.subtype ha
  have hcommK : ⁅(a : G),(k : G)⁆ ∈ K :=
    (le_normalizer_iff_commutator_le_right.mp hHK)
      (commutator_mem_commutator a.property k.property)
  have hcommQ : ⁅(a : G),(k : G)⁆ ∈ H.pCoreIn 2 :=
    (le_normalizer_iff_commutator_le_left.mp (hKH.trans hQN))
      (commutator_mem_commutator hQ k.property)
  have hh := inf_pCoreIn_le_of_le 2 hKH ⟨hcommK,hcommQ⟩
  obtain ⟨u,hu,he⟩ := hh
  have he' : u = K.normalizerMonoidHom (inclusion hHK a) k / k := by
    apply Subtype.ext
    change (u : G) = (a : G) * (k : G) * (a : G)⁻¹ / (k : G)
    change (u : G) = ⁅(a : G),(k : G)⁆ at he
    simpa only [div_eq_mul_inv,commutatorElement_def] using he
  exact he' ▸ hu
end Subgroup


namespace Theory.SpecificGroups.Alternating.FiveSquareCoreImage
open FiveSquareAutomorphisms
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A large elementary actor has a nontrivial image in the original normal square. -/
theorem exists_nontrivial_component_image
    (H K V : Subgroup G) [IsElementaryAbelian 2 V]
    (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G)) (hVH : V ≤ H)
    (e : (K ⧸ pCore 2 K) ≃* Pair)
    (hker : IsPGroup 2 ((pCoreNormalizerAction 2 K).comp (inclusion hHK)).ker)
    (hcard : 4 < Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))) :
    ∃ v ∈ V, v ∈ K ⊔ H.pCoreIn 2 ∧ v ∉ H.pCoreIn 2 := by
  let f₀ := (pCoreNormalizerAction 2 K).comp (inclusion hHK)
  let f := (MulAut.congr e).toMonoidHom.comp f₀
  have hk₀ : f₀.ker = pCore 2 H := pCoreNormalizerAction_restrict_ker_eq_twoCore H K hKH hHK hker
  have hk : f.ker = pCore 2 H := by
    rw [←hk₀]
    ext a
    change (MulAut.congr e) (f₀ a) = 1 ↔ f₀ a = 1
    rw [←(MulAut.congr e).map_one]
    exact (MulAut.congr e).injective.eq_iff
  have hc : 4 < Nat.card ((V.subgroupOf H).map f) := by
    rw [←relIndex_ker,hk]
    simpa only [←relIndex_ker,QuotientGroup.ker_mk'] using hcard
  let : IsElementaryAbelian 2 (V.subgroupOf H) := IsElementaryAbelian.subgroupOf hVH
  have hE : IsElementaryAbelian 2 ((V.subgroupOf H).map f) := IsElementaryAbelian.map f
  obtain ⟨r,hr,_,v,hv,he⟩ := exists_nontrivial_inner _ hE hc
  obtain ⟨k,hkq⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (e.symm r)
  let kH : H := ⟨k,hKH k.property⟩
  have hfK : f kH = MulAut.conj r := by
    change (MulAut.congr e) (pCoreNormalizerAction 2 K (inclusion hHK kH)) = _
    rw [show inclusion hHK kH = ⟨k,K.le_normalizer k.property⟩ from rfl,
      pCoreNormalizerAction_on_component,MulAut.congr_conj,hkq,e.apply_symm_apply]
  have hQ : v / kH ∈ pCore 2 H := by
    rw [←hk]
    change f (v / kH) = 1
    rw [map_div,he,hfK]
    simp only [div_eq_mul_inv,mul_inv_cancel]
  have hvin : (v : G) ∈ K ⊔ H.pCoreIn 2 := by
    have hd : (v : G) / (k : G) ∈ H.pCoreIn 2 := mem_map_of_mem H.subtype hQ
    have hh := (K ⊔ H.pCoreIn 2).mul_mem (mem_sup_right hd) (mem_sup_left k.property)
    simpa only [div_mul_cancel] using hh
  refine ⟨v,hv,hvin,?_⟩
  intro hvQ
  have hvQ' : v ∈ pCore 2 H := by
    obtain ⟨u,hu,huv⟩ := hvQ
    exact (show u = v from Subtype.ext huv) ▸ hu
  have hfV : f v = 1 := by
    exact (show v ∈ f.ker from hk.symm ▸ hvQ')
  have hz : center Pair = ⊥ := by
    rw [Subgroup.center_prod,alternatingGroup.center_eq_bot (by simp),bot_prod_bot]
  exact hr (conj_injective_of_center_eq_bot hz
    (he.symm.trans (hfV.trans (map_one MulAut.conj).symm)))

/-- Inside the actual image of the normal square, order sixteen is the full two-part. -/
theorem exists_sylow_core_image
    (H K V : Subgroup G) (hKH : K ≤ H) (hHK : H ≤ normalizer (K : Set G))
    (e : (K ⧸ pCore 2 K) ≃* Pair)
    (hVK : V ≤ K ⊔ H.pCoreIn 2)
    (hcard : Nat.card ((V.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) = 16) :
    let π := QuotientGroup.mk' (pCore 2 H)
    let A := (V.subgroupOf H).map π
    let N := (K.subgroupOf H).map π
    ∃ S : Sylow 2 N, (S : Subgroup N).map N.subtype = A := by
  dsimp only
  let π := QuotientGroup.mk' (pCore 2 H)
  let A := (V.subgroupOf H).map π
  let N := (K.subgroupOf H).map π
  have hQ : (H.pCoreIn 2).subgroupOf H = pCore 2 H :=
    comap_map_eq_self_of_injective H.subtype_injective _
  have hAN : A ≤ N := by
    have hh := map_mono (f := π) (subgroupOf_mono H hVK)
    rw [subgroupOf_sup hKH (pCoreIn_le 2 H),hQ,Subgroup.map_sup,
      QuotientGroup.map_mk'_self,sup_bot_eq] at hh
    exact hh
  let : (K.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer hHK
  let c := subgroupOfEquivOfLe hKH
  let d := (coreQuotientEquivImage 2 (K.subgroupOf H)).symm.trans
    ((QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans e)
  have hcN : Nat.card N = 3600 := by
    rw [Nat.card_congr d.toEquiv,Nat.card_prod]
    change Nat.card (alternatingGroup (Fin 5)) * Nat.card (alternatingGroup (Fin 5)) = 3600
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hAcard : Nat.card (A.subgroupOf N) = 2 ^ (Nat.card N).factorization 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv,hcard,hcN]
    decide +kernel
  exact ⟨Sylow.ofCard (A.subgroupOf N) hAcard,map_subgroupOf_eq_of_le hAN⟩
end Theory.SpecificGroups.Alternating.FiveSquareCoreImage
