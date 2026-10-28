module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.Action
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.Actors
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.PermutationOvergroups
public import Theory.GroupTheory.PRegularLift
public import Theory.GroupTheory.PrimeOrderLift
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Equality with the actual seven-point partition stabilizer

The intrinsic solvable-Sylow calculation is transported along the faithful
seven-point action. To upgrade containment to equality, lift the partition
stabilizer through H → H/O₂(H). Its kernel is a two-group, so the lift is
solvable and 13.8.13 puts it in M. Every element of order three lifts with
order three and belongs to L₁ = θ(H∩M). The stabilizer's proved generation
by these elements and T* then gives equality. The same coordinate choice
retains all three Sylow orbits. A factor of nine in L₁ survives the two-core
quotient and rules out the actual pair stabilizer, whose order is 48.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.7.3(9), 13.8.13 and 13.8.24, printed pp.936, 950–951, 958–959
(combined manuscript, 1 March 2004).
-/

public section
open Subgroup Equiv
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry

private theorem generation_comap {J B : Type*} [Group J] [Group B]
    (e : J ≃* B) (D : Subgroup B) (S : Subgroup J)
    (hD : D = closure {b : B | b ∈ D ∧ orderOf b = 3} ⊔ S.map e.toMonoidHom) :
    D.comap e.toMonoidHom =
      closure {g : J | g ∈ D.comap e.toMonoidHom ∧ orderOf g = 3} ⊔ S := by
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_comap_eq_self_of_surjective e.surjective, Subgroup.map_sup, MonoidHom.map_closure]
  have he : e.toMonoidHom '' {g : J | g ∈ D.comap e.toMonoidHom ∧ orderOf g = 3} =
      {g : B | g ∈ D ∧ orderOf g = 3} := by
    ext g
    constructor
    · rintro ⟨x, ⟨hx, ho⟩, rfl⟩
      exact ⟨hx, (e.orderOf_eq x).trans ho⟩
    · rintro ⟨hg, ho⟩
      refine ⟨e.symm g, ⟨?_, (e.symm.orderOf_eq g).trans ho⟩, e.apply_symm_apply g⟩
      change e (e.symm g) ∈ D
      simpa only [e.apply_symm_apply] using hg
  rw [he]
  exact hD

/-- Transfer the intrinsic permutation calculation along a faithful action.
The single coordinate change is retained in the stabilizer and all three orbits. -/
theorem faithful_solvable_sylow_placement {J : Type*} [Group J]
    (φ : J →* S7) (hφ : Function.Injective φ)
    (hAlt : alternatingGroup (Fin 7) ≤ φ.range)
    (S : Sylow 2 J) (P : Subgroup J) [Group.IsSolvable P]
    (hSP : (S : Subgroup J) ≤ P) :
    ∃ (σ : S7) (R : Subgroup S7),
      (R = fourThreeStabilizer ∨ R = pairStabilizer) ∧
      let ψ := (MulAut.conj σ).toMonoidHom.comp φ
      let D := R.comap ψ
      P ≤ D ∧ Group.IsSolvable D ∧
      D = closure {g : J | g ∈ D ∧ orderOf g = 3} ⊔ (S : Subgroup J) ∧
      {y : Fin 7 | ∃ s ∈ (S : Subgroup J), ψ s 0 = y} = {0, 1, 2, 3} ∧
      {y : Fin 7 | ∃ s ∈ (S : Subgroup J), ψ s 4 = y} = {4, 5} ∧
      {y : Fin 7 | ∃ s ∈ (S : Subgroup J), ψ s 6 = y} = {6} := by
  let : Finite J := Finite.of_injective φ hφ
  let e := MonoidHom.ofInjective hφ
  let S' := S.mapSurjective e.surjective
  let P' := P.map e.toMonoidHom
  let : Group.IsSolvable P' := Group.isSolvable_of_surjective
    (e.toMonoidHom.subgroupMap_surjective P)
  obtain ⟨σ, R, hR, _, hPD, hs, hg, _, h0, h4, h6⟩ :=
    PermutationOvergroups.solvable_sylow_overgroup_compatible_placement
      φ.range hAlt S' P' (map_mono hSP)
  let ψ := (MulAut.conj σ).toMonoidHom.comp φ.range.subtype
  let D := R.comap ψ
  have hsol : Group.IsSolvable (D.comap e.toMonoidHom) := by
    let := hs
    exact Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom.subgroupComap D)
      (fun a b h => Subtype.ext (e.injective (congrArg Subtype.val h)))
  have horb (i : Fin 7) :
      {y : Fin 7 | ∃ s ∈ (S : Subgroup J), (ψ.comp e.toMonoidHom) s i = y} =
      {y : Fin 7 | ∃ s : S', ψ s.val i = y} := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨e s, mem_map_of_mem _ hs⟩, rfl⟩
    · rintro ⟨s, he⟩
      obtain ⟨x, hx, hxv⟩ := s.property
      change e x = s.val at hxv
      exact ⟨x, hx, by change ψ (e x) i = y; rw [hxv]; exact he⟩
  have hPD' : P ≤ D.comap e.toMonoidHom := map_le_iff_le_comap.mp hPD
  refine ⟨σ, R, hR, hPD', hsol,
    generation_comap e D S hg, ?_, ?_, ?_⟩
  · exact (horb 0).trans h0
  · exact (horb 4).trans h4
  · exact (horb 6).trans h6

variable {G : Type*} [Group G] [Finite G]

/-- The full inverse image of a solvable star subgroup is solvable and
falls in M by the universal earlier conclusion 13.8.13. -/
theorem solvable_star_lift_le_M (H L₁ T G₁ M : Subgroup G)
    (hbase : L₁ ⊔ T ≤ H) (hHG : H ≤ G₁)
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (D : Subgroup (Source.Hstar H)) [Group.IsSolvable D]
    (hD : Source.starImage H (L₁ ⊔ T) ≤ D) :
    (D.comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype ≤ M := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let J := (D.comap q).map H.subtype
  have hk : Group.IsSolvable q.ker := by
    dsimp [q]
    rw [QuotientGroup.ker_mk']
    let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
    infer_instance
  let := hk
  let : Group.IsSolvable (D.comap q) := isSolvable_comap_of_solvable_ker q D
  have hs : Group.IsSolvable J := Group.isSolvable_of_surjective
    (H.subtype.subgroupMap_surjective (D.comap q))
  apply h13 J ?_ ((map_subtype_le _).trans hHG) hs
  intro x hx
  exact ⟨⟨x, hbase hx⟩, hD (mem_map_of_mem q hx), rfl⟩

/-- An order-three star element has an order-three lift through O₂(H). -/
theorem order_three_star_lift (H : Subgroup G)
    (a : Source.Hstar H) (ho : orderOf a = 3) :
    ∃ x : H, QuotientGroup.mk' (pCore 2 H) x = a ∧ orderOf x = 3 := by
  let q := QuotientGroup.mk' (pCore 2 H)
  obtain ⟨x, hx, he⟩ := q.exists_pRegular_lift (QuotientGroup.mk'_surjective _)
    2 Nat.prime_two a (by rw [ho]; decide)
  have hk : IsPGroup 2 q.ker := by
    rw [show q.ker = pCore 2 H from QuotientGroup.ker_mk' _]
    exact pCore_isPGroup
  exact ⟨x, he, (q.orderOf_map_eq_of_coprime_of_isPGroup_ker hk x
    (Nat.prime_two.coprime_iff_not_dvd.mpr hx)).symm.trans (he ▸ ho)⟩

/-- Theta and 13.8.13 upgrade solvable partition containment to equality.
No maximality or equality with H∩M is assumed. -/
theorem star_overgroup_eq_of_three_generation (H L₁ T G₁ M : Subgroup G)
    (hbase : L₁ ⊔ T ≤ H) (hHG : H ≤ G₁)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (D : Subgroup (Source.Hstar H)) [Group.IsSolvable D]
    (hPD : Source.starImage H (L₁ ⊔ T) ≤ D)
    (hgen : D = closure {g : Source.Hstar H | g ∈ D ∧ orderOf g = 3} ⊔
      Source.starImage H T) : D = Source.starImage H (L₁ ⊔ T) := by
  have hM := solvable_star_lift_le_M H L₁ T G₁ M hbase hHG h13 D hPD
  apply le_antisymm _ hPD
  rw [hgen]
  refine sup_le ((closure_le _).mpr ?_) (starImage_mono H le_sup_right)
  rintro a ⟨ha, ho⟩
  obtain ⟨x, hx, hxo⟩ := order_three_star_lift H a ho
  have hxM : (x : G) ∈ M := hM ⟨x, by change _ ∈ D; rwa [hx], rfl⟩
  have hxL : (x : G) ∈ L₁ := by
    rw [htheta]
    exact subset_closure ⟨⟨x.property, hxM⟩, (orderOf_coe x).trans hxo⟩
  exact ⟨x, (show L₁ ≤ L₁ ⊔ T from le_sup_left) hxL, hx⟩

/-- The two actual partition stabilizers, with equality forced by the earlier
solvable exclusion and theta identity. -/
theorem source_partition_dichotomy (H L₁ T G₁ M : Subgroup G)
    (hbase : L₁ ⊔ T ≤ H) (hHG : H ≤ G₁)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (φ : Source.Hstar H →* S7) (hφ : Function.Injective φ)
    (hAlt : alternatingGroup (Fin 7) ≤ φ.range)
    (S : Sylow 2 H) (hS : (S : Subgroup H) = T.subgroupOf H)
    [Group.IsSolvable (L₁ ⊔ T : Subgroup G)] :
    ∃ σ : S7, let ψ := (MulAut.conj σ).toMonoidHom.comp φ
      (Source.starImage H (L₁ ⊔ T) = fourThreeStabilizer.comap ψ ∨
        Source.starImage H (L₁ ⊔ T) = pairStabilizer.comap ψ) ∧
      {y : Fin 7 | ∃ s ∈ Source.starImage H T, ψ s 0 = y} = {0, 1, 2, 3} ∧
      {y : Fin 7 | ∃ s ∈ Source.starImage H T, ψ s 4 = y} = {4, 5} ∧
      {y : Fin 7 | ∃ s ∈ Source.starImage H T, ψ s 6 = y} = {6} := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let S' := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hS' : (S' : Subgroup (Source.Hstar H)) = Source.starImage H T := by
    change (S : Subgroup H).map q = _
    rw [hS]
    rfl
  let : Group.IsSolvable ((L₁ ⊔ T).subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hbase).toMonoidHom)
      (subgroupOfEquivOfLe hbase).injective
  let : Group.IsSolvable (Source.starImage H (L₁ ⊔ T)) :=
    Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
  obtain ⟨σ, R, hR, hPD, hsol, hgen, h0, h4, h6⟩ :=
    faithful_solvable_sylow_placement φ hφ hAlt S' (Source.starImage H (L₁ ⊔ T))
      (by rw [hS']; exact starImage_mono H le_sup_right)
  rw [hS'] at hgen h0 h4 h6
  let := hsol
  have he := star_overgroup_eq_of_three_generation H L₁ T G₁ M hbase hHG htheta h13
    (R.comap ((MulAut.conj σ).toMonoidHom.comp φ)) hPD hgen
  exact ⟨σ, hR.elim (fun h => Or.inl (he.symm.trans (congrArg _ h)))
    (fun h => Or.inr (he.symm.trans (congrArg _ h))), h0, h4, h6⟩

/-- A two-group kernel cannot absorb a factor of nine. -/
theorem nine_dvd_image_of_two_kernel {J B : Type*} [Group J] [Finite J] [Group B]
    (f : J →* B) (hk : IsPGroup 2 f.ker) (h9 : 9 ∣ Nat.card J) :
    9 ∣ Nat.card f.range := by
  have he := f.ker.card_mul_index
  rw [index_ker] at he
  have hc : Nat.Coprime 9 (Nat.card f.ker) := by
    obtain ⟨n, hn⟩ := hk.exists_card_dvd_pow
    exact ((by decide : Nat.Coprime 9 2).pow_right n).coprime_dvd_right hn
  exact hc.dvd_of_dvd_mul_left (he.symm ▸ h9)

/-- In particular a factor of nine in L₁ survives in its actual star image. -/
theorem nine_dvd_starImage (H L₁ : Subgroup G) (hLH : L₁ ≤ H)
    (h9 : 9 ∣ Nat.card L₁) : 9 ∣ Nat.card (Source.starImage H L₁) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let f := q.comp (L₁.subgroupOf H).subtype
  have hk : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.ker.comap (L₁.subgroupOf H).subtype)
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup (p := 2) (G := H)).comap_of_injective
      (L₁.subgroupOf H).subtype (L₁.subgroupOf H).subtype_injective
  have hn : 9 ∣ Nat.card (L₁.subgroupOf H) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hLH).toEquiv]
    exact h9
  simpa only [Source.starImage, f, MonoidHom.range_comp, range_subtype] using
    nine_dvd_image_of_two_kernel f hk hn

/-- Nine in L₁ excludes the genuine three-pair stabilizer. -/
theorem not_pair_partition_of_nine (H L₁ T : Subgroup G) (hLH : L₁ ≤ H)
    (φ : Source.Hstar H →* S7) (hφ : Function.Injective φ)
    (h9 : 9 ∣ Nat.card L₁) :
    Source.starImage H (L₁ ⊔ T) ≠ pairStabilizer.comap φ := by
  intro he
  have hm : (Source.starImage H L₁).map φ ≤ pairStabilizer := by
    apply map_le_iff_le_comap.mpr
    rw [← he]
    exact starImage_mono H le_sup_left
  have hc := card_dvd_of_le hm
  rw [card_map_of_injective hφ] at hc
  have hd := (nine_dvd_starImage H L₁ hLH h9).trans hc
  exact PermutationOvergroups.nine_not_dvd_pairStabilizer_card hd

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry
