module

public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Conjugation on the central quotient after the two-core

Transport the actual action of a normalizing group H on K/O₂,Z(K) to a
specified model. Elements of K induce the model's inner automorphisms.
Normalization of a model subgroup's inner image lifts to its literal
preimage in K when the model is centerless. If H = KT with K normal in H
and T a two-group, the action kernel is solvable: its intersection with K
lies in O₂,Z(K), and its image in H/K is a two-group.

These elementary action and extension arguments support the cover geometry
in Aschbacher–Smith 13.8.21(2), printed p.956.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupAction.PCoreCentralModelAction
variable {G D : Type*} [Group G] [Group D]

noncomputable def centralModelAction (H K : Subgroup G)
    (hn : H ≤ normalizer (K : Set G))
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* D) : H →* MulAut D :=
  (MulAut.congr e).toMonoidHom.comp
    ((quotientAut (centralPreimage (pCore 2 K))).comp
      (K.normalizerMonoidHom.comp (inclusion hn)))

theorem centralModelAction_apply (H K : Subgroup G)
    (hn : H ≤ normalizer (K : Set G))
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* D) (t : H) (k : K) :
    centralModelAction H K hn e t (e (QuotientGroup.mk' _ k)) =
      e (QuotientGroup.mk' _ (K.normalizerMonoidHom (inclusion hn t) k)) := by
  change e (quotientAut _ _ (e.symm (e _))) = _
  rw [e.symm_apply_apply, quotientAut_apply_mk]
  rfl

theorem centralModelAction_inner (H K : Subgroup G)
    (hn : H ≤ normalizer (K : Set G)) (hKH : K ≤ H)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* D) (k : K) :
    centralModelAction H K hn e (inclusion hKH k) =
      MulAut.conj (e (QuotientGroup.mk' _ k)) := by
  ext x
  obtain ⟨q, rfl⟩ := e.surjective x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (centralPreimage (pCore 2 K)) q
  rw [centralModelAction_apply]
  change e (QuotientGroup.mk' _ (k * x * k⁻¹)) = _
  simp only [map_mul, map_inv, MulAut.conj_apply]

private theorem preserves_of_normalizes_inner (U : Subgroup D)
    (hc : center D = ⊥) (a : MulAut D)
    (ha : a ∈ normalizer (U.map MulAut.conj : Set (MulAut D))) (x : D) :
    x ∈ U ↔ a x ∈ U := by
  have he : MulAut.conj (a x) = a * MulAut.conj x * a⁻¹ := by
    ext y
    simp
  have hi := Theory.GroupTheory.conj_injective_of_center_eq_bot hc
  simpa only [← he, mem_map_iff_mem hi] using
    ((mem_normalizer_iff.mp ha) (MulAut.conj x))

theorem centralModelAction_normalizes_lift (H K : Subgroup G)
    (hn : H ≤ normalizer (K : Set G))
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* D)
    (hc : center D = ⊥) (U : Subgroup D) (t : H)
    (ht : centralModelAction H K hn e t ∈
      normalizer (U.map MulAut.conj : Set (MulAut D))) :
    (t : G) ∈ normalizer ((U.comap
      (e.toMonoidHom.comp (QuotientGroup.mk' (centralPreimage (pCore 2 K))))).map
        K.subtype : Set G) := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (centralPreimage (pCore 2 K)))
  let a := K.normalizerMonoidHom (inclusion hn t)
  have hmem (x : K) : x ∈ U.comap f ↔ a x ∈ U.comap f := by
    have hh := preserves_of_normalizes_inner U hc _ ht (f x)
    change e (QuotientGroup.mk' _ x) ∈ U ↔
      centralModelAction H K hn e t (e (QuotientGroup.mk' _ x)) ∈ U at hh
    rw [centralModelAction_apply] at hh
    exact hh
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨a k, (hmem k).mp hk, rfl⟩
  · rintro ⟨k, hk, he⟩
    refine ⟨a.symm k, (hmem (a.symm k)).mpr ?_, ?_⟩
    · rw [a.apply_symm_apply]
      exact hk
    · have hh := congrArg (fun z : K => (z : G)) (a.apply_symm_apply k)
      change (t : G) * (a.symm k : G) * (t : G)⁻¹ = (k : G) at hh
      change (k : G) = (t : G) * x * (t : G)⁻¹ at he
      rw [he] at hh
      exact (conj_injective hh)

theorem centralModelAction_inner_le_range (H K : Subgroup G)
    (hn : H ≤ normalizer (K : Set G)) (hKH : K ≤ H)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* D) :
    (MulAut.conj : D →* MulAut D).range ≤ (centralModelAction H K hn e).range := by
  rintro _ ⟨d, rfl⟩
  obtain ⟨q, rfl⟩ := e.surjective d
  obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective (centralPreimage (pCore 2 K)) q
  exact ⟨inclusion hKH k, centralModelAction_inner H K hn hKH e k⟩

theorem centralModelAction_centralPreimage (H K : Subgroup G)
    (hn : H ≤ normalizer (K : Set G)) (hKH : K ≤ H)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* D)
    (k : centralPreimage (pCore 2 K)) :
    centralModelAction H K hn e (inclusion hKH k.val) = 1 := by
  rw [centralModelAction_inner]
  have hk : QuotientGroup.mk' (centralPreimage (pCore 2 K)) k.val = 1 :=
    (QuotientGroup.eq_one_iff k.val).mpr k.property
  rw [hk, map_one, map_one]

theorem centralModelAction_ker_solvable [Finite G] (H K T : Subgroup G)
    (hKH : K ≤ H) [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ T) (hT : IsPGroup 2 T)
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* D) (hc : center D = ⊥) :
    Group.IsSolvable
      (centralModelAction H K (le_normalizer_of_normal_subgroupOf hKH) e).ker := by
  let hn := le_normalizer_of_normal_subgroupOf hKH
  let a := centralModelAction H K hn e
  let N := a.ker
  let C := centralPreimage (pCore 2 K)
  let J := K.subgroupOf H
  let q := QuotientGroup.mk' J
  have hTH : T ≤ H := hgen ▸ le_sup_right
  have hj : J ⊔ T.subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup hKH hTH, ← hgen, subgroupOf_self]
  have hp : IsPGroup 2 (H ⧸ J) :=
    isPGroup_quotient_of_sup_eq_top J (T.subgroupOf H) hT.comap_subtype hj
  let : Group.IsNilpotent (H ⧸ J) := hp.isNilpotent
  let : Group.IsSolvable (H ⧸ J) := inferInstance
  let : Group.IsNilpotent (pCore 2 K) := pCore_isNilpotent
  let : Group.IsSolvable (QuotientGroup.mk' (pCore 2 K)).ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  let : Group.IsSolvable C := isSolvable_comap_of_solvable_ker
    (QuotientGroup.mk' (pCore 2 K)) (center _)
  let i : C →* N := ((inclusion hKH).comp C.subtype).codRestrict N
    (fun k => centralModelAction_centralPreimage H K hn hKH e k)
  let f : N →* (H ⧸ J) := q.comp N.subtype
  apply Group.isSolvable_of_ker_le_range i f
  intro x hx
  have hxJ : x.val ∈ J := (QuotientGroup.eq_one_iff x.val).mp hx
  let k : K := ⟨x.val.val, hxJ⟩
  have hak : a (inclusion hKH k) = 1 := x.property
  rw [centralModelAction_inner] at hak
  have hk : k ∈ C := by
    apply (QuotientGroup.eq_one_iff k).mp
    change QuotientGroup.mk' (centralPreimage (pCore 2 K)) k = 1
    apply e.injective
    rw [map_one]
    apply Theory.GroupTheory.conj_injective_of_center_eq_bot hc
    simpa only [map_one] using hak
  exact ⟨⟨k, hk⟩, Subtype.ext (Subtype.ext rfl)⟩


end Theory.GroupAction.PCoreCentralModelAction
