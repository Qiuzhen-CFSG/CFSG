module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.OuterAction
public import Theory.GroupTheory.CyclicFixerDisjointConjugate
/-!
# The source two-core embeds in the residual's cyclic-four fixer

The adjusted crossing normalizes C_S(R) and moves O₂(H) disjointly from
itself. The component action restricts to C_S(R), has kernel O₂(H), and
has cyclic image of order dividing four. The conjugate-kernel embedding
therefore makes the original O₂(H) cyclic of order dividing four.
Source: Aschbacher--Smith 2.5.15, printed p.559.
-/
public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z x : G}

theorem linear_three_source_core_cyclic_dvd_four
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (e : K ≃* Matrix.PSL3Three.PSL) (zK : K) (hzK : orderOf zK = 2)
    (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (hxN : x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G))
    (hx2 : x^2 ∈ (S : Subgroup H).map H.subtype)
    (hxR : x ∈ centralizer ((GLTwoThreeLocal.residual zK).map K.subtype : Set G)) :
    IsCyclic (twoCore H) ∧ Nat.card (twoCore H) ∣ 4 := by
  let Y := (S : Subgroup H).map H.subtype
  let B := (GLTwoThreeLocal.residual zK).map K.subtype
  let C := Y ⊓ centralizer (B : Set G)
  have hCH : C ≤ H := inf_le_left.trans (map_subtype_le _)
  let α := MathieuSourceSetup.componentAction c
  let f := α.comp (inclusion hCH)
  have hk : f.ker = (twoCore H).subgroupOf C := by
    ext q
    change α (inclusion hCH q) = 1 ↔ _
    rw [← MonoidHom.mem_ker,normal_component_source_action_ker c hG hempty hgen]
    rfl
  obtain ⟨a,_,ha,_,hfix⟩ := linear_three_local_residual_fixer K e zK hzK
  change fixingSubgroup (MulAut K) (GLTwoThreeLocal.residual zK : Set K) = zpowers a at hfix
  have hf : ∀ q : C, f q ∈ zpowers a := by
    intro q
    rw [← hfix]
    apply (mem_fixingSubgroup_iff _).mpr
    intro r hr
    apply Subtype.ext
    change (q : G) * (r : G) * (q : G)⁻¹ = (r : G)
    exact mul_inv_eq_iff_eq_mul.mpr (q.property.2 r (mem_map_of_mem K.subtype hr)).symm
  have hNC : twoCore H ≤ C := by
    intro n hn
    have hnh : n ∈ H := pCoreIn_le 2 H hn
    have hker : (⟨n,hnh⟩ : H) ∈ α.ker := by
      rw [normal_component_source_action_ker c hG hempty hgen]
      exact hn
    have hCK : n ∈ centralizer (K : Set G) := by
      change (⟨n,hnh⟩ : H) ∈
        (K.normalizerMonoidHom.comp (inclusion
          ((normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance))).ker at hker
      rw [normalizer_action_ker_comap] at hker
      exact hker
    exact ⟨pCoreIn_le_sylow H S hn,centralizer_le (map_subtype_le _) hCK⟩
  have hxC : x ∈ normalizer (C : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨hxN,(centralizer (B : Set G)).le_normalizer hxR⟩
  have hd := (generated_twoCore_disjoint S (MathieuSourceSetup.sourceTuple c)
    ⟨c.component_le,c.component⟩ hgen hxT hxS hxN hx2).1
  obtain ⟨hcyc,hcard⟩ := cyclic_of_disjoint_conjugate_in_cyclic_preimage
    C f (zpowers a) (twoCore H) hk hf hNC x⁻¹ ((normalizer (C : Set G)).inv_mem hxC) hd
  rw [Nat.card_zpowers,ha] at hcard
  exact ⟨hcyc,hcard⟩
end CFSG.Quasithin.Chapter2.Section05
