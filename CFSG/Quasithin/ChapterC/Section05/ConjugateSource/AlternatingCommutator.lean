module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingFrattini
public import Theory.GroupTheory.Commutator.CentralizingFactor

/-!
# The commutator plane in the alternating-five conjugate branch

The actual diagonal actor in the marked pair-swap image has fixed index four.
Transporting it to the literal module and comparing the resulting index with
the displacement subgroup identifies `[U,Uˣ]` with `C_U(Uˣ)=U∩Uˣ`.
The centralizing-factor calculation then identifies this with the source
commutator `[U,S]` and proves its invariance under the selected conjugator.

Source: Aschbacher–Smith, C.5.6(2),(3), printed pp.156–157.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
private theorem centralizer_index_le_commutator_card (U V : Subgroup G) [IsMulCommutative U]
    (hVU : V ≤ normalizer (U : Set G)) (v : G) (hv : v ∈ V) :
    (centralizer ({v} : Set G)).relIndex U ≤ Nat.card (⁅U, V⁆ : Subgroup G) := by
  let e := U.normalizerMonoidHom ⟨v, hVU hv⟩
  let f : U →* U := {
    toFun := fun u => e u * u⁻¹
    map_one' := by simp
    map_mul' := by
      intro a b
      simp only [map_mul, mul_inv_rev]
      ac_rfl }
  have hker : f.ker = (centralizer ({v} : Set G)).subgroupOf U := by
    ext u
    change e u * u⁻¹ = 1 ↔ _
    rw [mul_inv_eq_one]
    change e u = u ↔ (u : G) ∈ centralizer ({v} : Set G)
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro he
      have hh := congrArg Subtype.val he
      change v * (u : G) * v⁻¹ = u at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hu
      apply Subtype.ext
      change v * (u : G) * v⁻¹ = u
      rw [← hu, mul_inv_cancel_right]
  have hle : f.range.map U.subtype ≤ ⁅U, V⁆ := by
    rintro a ⟨b, ⟨u, rfl⟩, rfl⟩
    change v * (u : G) * v⁻¹ * (u : G)⁻¹ ∈ ⁅U, V⁆
    rw [commutator_comm]
    exact commutator_mem_commutator hv u.property
  have hc := card_le_of_le hle
  rw [card_map_of_injective U.subtype_injective, ← index_ker f, hker] at hc
  exact hc

namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open BinaryPermutation Representation.BinaryOffender
private theorem diagonal_fixed :
    fixedSpace (coreRepresentation (Fin 5)) (zpowers pairDiagonal) =
      fixedSpace (coreRepresentation (Fin 5)) (ChapterB.Offenders.D 5) := by
  apply fixedSpace_eq_of_exchange_normalized
  · apply zpowers_le.mpr
    exact mul_mem (ChapterB.Offenders.pairSwap_mem (n := 5) (m := 2) 0 (by decide))
      (ChapterB.Offenders.pairSwap_mem (n := 5) (m := 2) 1 (by decide))
  · intro he
    have hm := mem_zpowers pairDiagonal
    rw [he, mem_bot] at hm
    have hd : pairDiagonal ≠ 1 := by decide +kernel
    exact hd hm
  · apply mem_normalizer_iff_map_conj_eq.mpr
    rw [MonoidHom.map_zpowers]
    have hd : MulAut.conj pairExchange pairDiagonal = pairDiagonal := by decide +kernel
    exact congrArg zpowers hd
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open BinaryPermutation Representation.BinaryOffender
variable {R K L : Subgroup G}
omit [Finite G] in
private theorem range_restrict (N B : Subgroup G) (hBN : B ≤ N) (a : N →* FivePerm) :
    (a.comp (inclusion hBN)).range = (B.subgroupOf N).map a := by
  ext p
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨inclusion hBN b, b.property, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b, hb⟩, rfl⟩

omit [Finite G] in
private theorem centralizer_zpowers (v : G) :
    centralizer (zpowers v : Set G) = centralizer ({v} : Set G) := by
  apply le_antisymm (centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers v)))
  intro g hg
  have hz : zpowers v ≤ centralizer ({g} : Set G) :=
    zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hg).symm)
  intro a ha
  exact mem_centralizer_singleton_iff.mp (hz ha)

theorem AlternatingPairSetup.exists_diagonal_actor
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    ∃ v ∈ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom,
      (centralizer ({v} : Set G)).relIndex (sourceModule K) = 4 := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  let N := K ⊔ S
  have hd : pairDiagonal ∈ ChapterB.Offenders.D 5 :=
    mul_mem (ChapterB.Offenders.pairSwap_mem (n := 5) (m := 2) 0 (by decide))
      (ChapterB.Offenders.pairSwap_mem (n := 5) (m := 2) 1 (by decide))
  have hd' : pairDiagonal ∈ (V.subgroupOf N).map h.action :=
    (h.conjugate_action_image x hx hnc).symm ▸ hd
  obtain ⟨v, hv, hav⟩ := hd'
  let A : Subgroup G := zpowers (v : G)
  have hAN : A ≤ N := zpowers_le.mpr v.property
  have hA : A.subgroupOf N = zpowers v := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le hAN, MonoidHom.map_zpowers]
    rfl
  let a := h.action.comp (inclusion hAN)
  have ha : a.range = zpowers pairDiagonal := by
    rw [range_restrict N A hAN h.action, hA, MonoidHom.map_zpowers, hav]
  have hc : Nat.card (U ⊓ centralizer (A : Set G) : Subgroup G) = 4 := by
    rw [marked_centralizer_card A U a h.coordinates (fun s u => h.equivariant (inclusion hAN s) u),
      ha, diagonal_fixed]
    exact pair_actor_fixed_card
  refine ⟨v, hv, ?_⟩
  change (centralizer ({(v : G)} : Set G)).relIndex U = 4
  have hm := relIndex_mul_relIndex (⊥ : Subgroup G)
    (U ⊓ centralizer (A : Set G)) U bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left, hc, h.module_card] at hm
  rw [show A = zpowers (v : G) from rfl, centralizer_zpowers] at hm
  omega

theorem AlternatingPairSetup.commutator_eq_fixed
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let U := sourceModule K
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    ⁅U, V⁆ = U ⊓ centralizer (V : Set G) ∧ ⁅U, V⁆ = U ⊓ V := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  have hU : IsElementaryAbelian 2 U := by
    let := h.block.2.1.elementary
    exact IsElementaryAbelian.map K.subtype
  let := hU
  have hV : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  let := hV
  have hS : S.map (MulAut.conj x⁻¹).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp
      (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx))
  have hVS : V ≤ S := (map_mono h.module_le).trans_eq hS
  have hn := h.transvection_normalizes x hx
  have hSU := (baumann_le_transvectionRadical R).trans hn.1
  have hSV := (baumann_le_transvectionRadical R).trans hn.2.1
  have hle : ⁅U, V⁆ ≤ U ⊓ V := le_inf
    (le_normalizer_iff_commutator_le_left.mp (hVS.trans hSU))
    (le_normalizer_iff_commutator_le_right.mp (h.module_le.trans hSV))
  have hfixed : U ⊓ V ≤ U ⊓ centralizer (V : Set G) :=
    inf_le_inf_left U (le_centralizer V)
  obtain ⟨v, hv, hi⟩ := h.exists_diagonal_actor x hx hnc
  have hc := centralizer_index_le_commutator_card U V (hVS.trans hSU) v hv
  rw [hi] at hc
  have he : ⁅U, V⁆ = U ⊓ centralizer (V : Set G) :=
    eq_of_le_of_card_ge (hle.trans hfixed) (by rw [h.conjugate_fixed_card x hx hnc]; exact hc)
  exact ⟨he, le_antisymm hle (hfixed.trans he.ge)⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
open scoped Pointwise
variable {R K L : Subgroup G}
theorem AlternatingPairSetup.commutator_structure
    (h : AlternatingPairSetup R K L) (x : G) (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let U := sourceModule K
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let E := ⁅U, ChapterB.baumann R⁆
    E = ⁅U, V⁆ ∧ E = U ⊓ centralizer (V : Set G) ∧ E = U ⊓ V ∧
      E.map (MulAut.conj x⁻¹).toMonoidHom = E := by
  let S := ChapterB.baumann R
  let U := sourceModule K
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  let Q := (K ⊔ S).pCoreIn 2
  let C := S ⊓ centralizer (V : Set G)
  have hcore : Q = S ⊓ centralizer (U : Set G) := h.core
  have hSmap : S.map (MulAut.conj x⁻¹).toMonoidHom = S :=
    mem_normalizer_iff_map_conj_eq.mp
      (Stellmacher.normalizer_le_normalizer_baumann R ((normalizer (R : Set G)).inv_mem hx))
  have hn := h.transvection_normalizes x hx
  have hSU := (baumann_le_transvectionRadical R).trans hn.1
  have hSV := (baumann_le_transvectionRadical R).trans hn.2.1
  have hg1 : (S : Set G) = (V : Set G) * (Q : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left V Q ((hcore.le.trans inf_le_left).trans hSV)]
    exact congrArg SetLike.coe (h.first_factorization x hx hnc)
  have hg2 : (S : Set G) = (U : Set G) * (C : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left U C (inf_le_left.trans hSU)]
    exact congrArg SetLike.coe (h.second_factorization x hx hnc)
  have hcomm : ⁅U, S⁆ = ⁅U, V⁆ := commutator_eq_of_product_centralizing_factor hg1
    (le_centralizer_iff.mp (hcore.le.trans inf_le_right))
  have hcomm' : ⁅V, S⁆ = ⁅V, U⁆ := commutator_eq_of_product_centralizing_factor hg2
    (le_centralizer_iff.mp (show C ≤ centralizer (V : Set G) from inf_le_right))
  have he := h.commutator_eq_fixed x hx hnc
  refine ⟨hcomm, hcomm.trans he.1, hcomm.trans he.2, ?_⟩
  change (⁅U, S⁆ : Subgroup G).map (MulAut.conj x⁻¹).toMonoidHom = ⁅U, S⁆
  rw [map_commutator, hSmap]
  exact hcomm'.trans ((commutator_comm V U).trans hcomm.symm)
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
