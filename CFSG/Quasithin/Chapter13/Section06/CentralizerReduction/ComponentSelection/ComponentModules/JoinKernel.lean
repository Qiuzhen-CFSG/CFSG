module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules.OrbitKernel
public import Theory.GroupTheory.CComponent.SimplePairKernel

/-!
# The two-group kernel on the original component-Sylow join

Restrict the literal plus map to K T_v. The source orbit is the pair K,Kᵗ,
whose intrinsic two-core quotients are simple. Its normal action kernel
misses K because K⁺ is nontrivial, and misses Kᵗ by normality. The general
pair kernel theorem therefore proves that this restricted kernel is a
two-group. No containment of L_v in the component orbit is needed.

Source: Aschbacher--Smith, the paired case in 13.6.14, printed p.929.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Restriction of the original quotient map to K T_v, retaining its values. -/
@[expose] def joinPlusMap (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G)) :
    ↥(K ⊔ Tv T v) →* Gplus K L T z v hL hz :=
  (plusMk K L T z v hL hz).comp
    (inclusion (sup_le (K_le_plusActor K L T v) le_sup_right))

/-- The source moving component has a two-group action kernel on its
whole Sylow join, before proving L_v lies in the orbit. -/
theorem joinPlusMap_ker_isTwoGroup_source
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK KnownSimple.IsKnownSimple (Gv v))
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v) (hn : ¬ Tv T v ≤ normalizer (K : Set G)) :
    IsPGroup 2 (joinPlusMap K L T z v hL hz).ker := by
  obtain ⟨_, _, t, ht, htN, hp⟩ := noninvariant_component_pair_source K L T z v hlocal hK hn
  let H := K ⊔ Tv T v
  have hKH : K ≤ H := le_sup_left
  have hTH : Tv T v ≤ H := le_sup_right
  let tH : H := ⟨t, hTH ht⟩
  let B := K.subgroupOf H
  let C := B.conjBy tH
  let S := (Tv T v).subgroupOf H
  let N := (joinPlusMap K L T z v hL hz).ker
  have hB : B.IsCComponent := hK.1.2.1
  have hC : C.IsCComponent := hB.map_equiv (MulAut.conj tH)
  have hBmap : B.map H.subtype = K := map_subgroupOf_eq_of_le hKH
  have hCmap : C.map H.subtype = K.conjBy t := by
    change (B.map (MulAut.conj tH).toMonoidHom).map H.subtype = _
    rw [map_map]
    have he : H.subtype.comp (MulAut.conj tH).toMonoidHom =
        (MulAut.conj t).toMonoidHom.comp H.subtype := rfl
    rw [he, ← map_map, hBmap]
    rfl
  have hne : B ≠ C := by
    intro he
    apply htN
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hCmap.symm.trans (he ▸ hBmap)
  let : IsSimpleGroup (K ⧸ pCore 2 K) :=
    noninvariant_component_core_simple_source K L T z v hlocal hK hn
  let eB := subgroupOfEquivOfLe hKH
  let qB := QuotientGroup.congr (pCore 2 B) (pCore 2 K) eB (pCore_map_iso 2 eB)
  let : IsSimpleGroup (B ⧸ pCore 2 B) := qB.isSimpleGroup
  let eC : B ≃* C := (MulAut.conj tH).subgroupMap B
  let qC := QuotientGroup.congr (pCore 2 B) (pCore 2 C) eC (pCore_map_iso 2 eC)
  let : IsSimpleGroup (C ⧸ pCore 2 C) := qC.symm.isSimpleGroup
  have hKmH : Kminus K T v ≤ H :=
    conjugateSpanBy_le hKH (hTH.trans H.le_normalizer)
  have hpair : B ⊔ C = (Kminus K T v).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, hBmap, hCmap, map_subgroupOf_eq_of_le hKmH, hp]
  have hHN : H ≤ normalizer (Kminus K T v : Set G) :=
    sup_le ((le_conjugateSpanBy K (Tv T v)).trans (Kminus K T v).le_normalizer)
      (le_normalizer_conjugateSpanBy K (Tv T v))
  let : (B ⊔ C).Normal := by
    rw [hpair]
    exact normal_subgroupOf_of_le_normalizer hHN
  have hS : IsPGroup 2 S :=
    (Chapter1.isSylowIn_iff.mp hK.1.2.2.1).1.comap_subtype
  have hBS : B ⊔ S = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup, hBmap, map_subgroupOf_eq_of_le hTH,
      ← MonoidHom.range_eq_map, range_subtype]
  have hgen : (B ⊔ C) ⊔ S = ⊤ := top_unique
    (hBS.symm.le.trans (sup_le_sup_right le_sup_left S))
  have hBN : ¬ B ≤ N := by
    intro hb
    apply plusImage_ne_bot_of_mem_Yz K L T z v hL hz hK
    apply bot_unique
    rintro x ⟨a, ha, rfl⟩
    have h := hb (show (⟨a, hKH ha⟩ : H) ∈ B from ha)
    exact h
  have hCN : ¬ C ≤ N := by
    intro hc
    apply hBN
    intro b hb
    have hconj : MulAut.conj tH b ∈ N := hc (mem_map_of_mem _ hb)
    have hback := (inferInstance : N.Normal).conj_mem (MulAut.conj tH b) hconj tH⁻¹
    simpa [MulAut.conj_apply, mul_assoc] using hback
  exact isTwoGroup_of_normal_avoiding_simpleCore_pair B C S N hB hC hne hS hgen hBN hCN

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
