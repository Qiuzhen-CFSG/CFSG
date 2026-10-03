module

public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Sylow enlargement controlled by a characteristic centralizer

A prime subgroup which is maximal in the intersection of two overgroups is
maximal in the first overgroup if its normalizer lies in the second. The
normalizer condition in a finite prime group proves this assertion.

The centralizer lemmas put the familiar fully centralized criterion in a
form usable with explicit finite computations: a Sylow centralizer of maximal
order among fused elements is a Sylow subgroup of the full centralizer.
These are the enlargement steps in Janko--Thompson, Math. Z. 113 (1970), p.396.
-/

namespace Subgroup

/-- Normalizer control promotes maximality from an intersection to an overgroup. -/
public theorem prime_overgroup_eq_of_normalizer_control
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (C H N : Subgroup G)
    (hN : normalizer (C : Set G) ≤ N)
    (hmax : ∀ U : Subgroup G, IsPGroup p U → C ≤ U → U ≤ H → U ≤ N → U = C)
    (U : Subgroup G) (hU : IsPGroup p U) (hCU : C ≤ U) (hUH : U ≤ H) : U = C := by
  by_contra hne
  have hproper : C.subgroupOf U < ⊤ := by
    rw [lt_top_iff_ne_top, Ne, subgroupOf_eq_top]
    exact fun hUC => hne (le_antisymm hUC hCU)
  let : Group.IsNilpotent U := hU.isNilpotent
  obtain ⟨u, huN, huC⟩ := SetLike.exists_of_lt
    (Group.normalizerCondition_of_isNilpotent (C.subgroupOf U) hproper)
  have huN' : (u : G) ∈ normalizer (C : Set G) := by
    rw [← subgroupOf_normalizer_eq hCU] at huN
    exact huN
  let D := U ⊓ normalizer (C : Set G)
  have hD : IsPGroup p D := hU.of_injective (inclusion inf_le_left)
    (inclusion_injective inf_le_left)
  have heq := hmax D hD (le_inf hCU le_normalizer)
    (inf_le_left.trans hUH) (inf_le_right.trans hN)
  exact huC (heq ▸ (show (u : G) ∈ D from ⟨u.property, huN'⟩))

/-- Conjugate elements have centralizers of the same finite order. -/
public theorem card_centralizer_eq_of_isConj
    {G : Type*} [Group G] (x y : G) (hxy : IsConj x y) :
    Nat.card (centralizer ({x} : Set G)) = Nat.card (centralizer ({y} : Set G)) := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  let f : G ≃* G := MulAut.conj g
  have hf : f x = y := hg
  apply Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)
  intro a
  change a ∈ centralizer ({x} : Set G) ↔ f a ∈ centralizer ({y} : Set G)
  simp only [mem_centralizer_singleton_iff]
  constructor
  · intro ha
    simpa only [map_mul, hf] using congrArg f ha
  · intro ha
    apply f.injective
    simpa only [map_mul, hf] using ha

/-- A characteristic subgroup transported through an injective embedding is
preserved by every ambient normalizer of the embedded group. -/
public theorem normalizer_le_normalizer_characteristic_map
    {P G : Type*} [Group P] [Group G] (f : P →* G)
    (hf : Function.Injective f) (C : Subgroup P) (K : Subgroup C)
    [K.Characteristic] :
    normalizer (C.map f : Set G) ≤
      normalizer ((K.map C.subtype).map f : Set G) := by
  let e : C ≃* C.map f := C.equivMapOfInjective f hf
  apply le_normalizer_iff.mpr
  intro g hg a ha
  obtain ⟨c, ⟨k, hk, rfl⟩, rfl⟩ := ha
  let b := (C.map f).normalizerMonoidHom ⟨g, hg⟩
  let a := (e.trans b).trans e.symm
  have hak : a k ∈ K := characteristic_iff_le_comap.mp inferInstance a hk
  refine mem_map.mpr ⟨(a k : C), mem_map_of_mem C.subtype hak, ?_⟩
  have hh := congrArg Subtype.val (e.apply_symm_apply (b (e k)))
  exact hh

end Subgroup

namespace Sylow

open Subgroup

/-- Bound a prime centralizer overgroup by transporting it inside a specified
overgroup of the Sylow subgroup. The bound only concerns conjugators there. -/
public theorem centralizer_prime_overgroup_eq_of_local_card_bound
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (N : Subgroup G) (hSN : (S : Subgroup G) ≤ N) (x : S)
    (hbound : ∀ g : N, ∀ y : S, (MulAut.conj (g : G)) (x : G) = (y : G) →
      Nat.card (centralizer ({y} : Set S)) ≤ Nat.card (centralizer ({x} : Set S)))
    (U : Subgroup G) (hU : IsPGroup p U)
    (hCU : (centralizer ({x} : Set S)).map (S : Subgroup G).subtype ≤ U)
    (hUH : U ≤ centralizer ({(x : G)} : Set G)) (hUN : U ≤ N) :
    U = (centralizer ({x} : Set S)).map (S : Subgroup G).subtype := by
  let C := (centralizer ({x} : Set S)).map (S : Subgroup G).subtype
  have hUp : IsPGroup p (U.subgroupOf N) := hU.comap_subtype
  obtain ⟨P, hUP⟩ := hUp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N P (S.subtype hSN)
  have hUS : U.map (MulAut.conj (g : G)).toMonoidHom ≤ (S : Subgroup G) := by
    rintro _ ⟨u, hu, rfl⟩
    have hh : (MulAut.conj g) ⟨u, hUN hu⟩ ∈ (S.subtype hSN : Subgroup N) := by
      rw [← hg]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hUP hu)
    exact hh
  have hxC : (x : G) ∈ C := mem_map_of_mem (S : Subgroup G).subtype
    (mem_centralizer_singleton_iff.mpr rfl)
  let y : S := ⟨(MulAut.conj (g : G)) (x : G), hUS
    (mem_map_of_mem (MulAut.conj (g : G)).toMonoidHom (hCU hxC))⟩
  have hUC : U.map (MulAut.conj (g : G)).toMonoidHom ≤
      (centralizer ({y} : Set S)).map (S : Subgroup G).subtype := by
    rintro _ ⟨u, hu, rfl⟩
    refine mem_map.mpr ⟨⟨(MulAut.conj (g : G)) u,
      hUS (mem_map_of_mem (MulAut.conj (g : G)).toMonoidHom hu)⟩, ?_, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    change (MulAut.conj (g : G)) u * (MulAut.conj (g : G)) (x : G) =
      (MulAut.conj (g : G)) (x : G) * (MulAut.conj (g : G)) u
    simpa only [map_mul] using congrArg (MulAut.conj (g : G))
      (mem_centralizer_singleton_iff.mp (hUH hu))
  apply (eq_of_le_of_card_ge hCU ?_).symm
  have hh := card_le_of_le hUC
  rw [card_map_of_injective (MulAut.conj (g : G)).injective,
    card_map_of_injective (S : Subgroup G).subtype_injective] at hh
  rw [card_map_of_injective (S : Subgroup G).subtype_injective]
  exact hh.trans (hbound g y rfl)

/-- Maximal order among fused centralizers makes the centralizer a Sylow subgroup. -/
public theorem exists_centralizer_sylow_of_card_bound
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (x : S)
    (hbound : ∀ y : S, IsConj (x : G) (y : G) →
      Nat.card (centralizer ({y} : Set S)) ≤ Nat.card (centralizer ({x} : Set S))) :
    ∃ T : Sylow p (centralizer ({(x : G)} : Set G)),
      (T : Subgroup (centralizer ({(x : G)} : Set G))).map
        (centralizer ({(x : G)} : Set G)).subtype =
          (centralizer ({x} : Set S)).map (S : Subgroup G).subtype := by
  let C := (centralizer ({x} : Set S)).map (S : Subgroup G).subtype
  let H := centralizer ({(x : G)} : Set G)
  have hCH : C ≤ H := by
    rintro _ ⟨c, hc, rfl⟩
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc))
  have hCp : IsPGroup p C := (S.isPGroup'.to_subgroup _).map _
  have hCpH : IsPGroup p (C.subgroupOf H) := hCp.comap_subtype
  obtain ⟨T, hCT⟩ := hCpH.exists_le_sylow
  let U := (T : Subgroup H).map H.subtype
  have hCU : C ≤ U := by
    rw [← map_subgroupOf_eq_of_le hCH]
    exact map_mono hCT
  obtain ⟨P, hUP⟩ := (T.isPGroup'.map H.subtype).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P S
  have hUS : U.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) := by
    rw [← hg]
    exact map_mono hUP
  have hxC : (x : G) ∈ C := mem_map_of_mem (S : Subgroup G).subtype
    (mem_centralizer_singleton_iff.mpr rfl)
  let y : S := ⟨(MulAut.conj g) (x : G), hUS
    (mem_map_of_mem (MulAut.conj g).toMonoidHom (hCU hxC))⟩
  have hy : IsConj (x : G) (y : G) := isConj_iff.mpr ⟨g, rfl⟩
  have hUC : U.map (MulAut.conj g).toMonoidHom ≤
      (centralizer ({y} : Set S)).map (S : Subgroup G).subtype := by
    rintro _ ⟨u, hu, rfl⟩
    have huH : u ∈ H := map_subtype_le _ hu
    refine mem_map.mpr ⟨⟨(MulAut.conj g) u,
      hUS (mem_map_of_mem (MulAut.conj g).toMonoidHom hu)⟩, ?_, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    change (MulAut.conj g) u * (MulAut.conj g) (x : G) =
      (MulAut.conj g) (x : G) * (MulAut.conj g) u
    simpa only [map_mul] using
      congrArg (MulAut.conj g) (mem_centralizer_singleton_iff.mp huH)
  have hcard : Nat.card U ≤ Nat.card C := by
    have hh := card_le_of_le hUC
    rw [card_map_of_injective (MulAut.conj g).injective,
      card_map_of_injective (S : Subgroup G).subtype_injective] at hh
    exact hh.trans ((hbound y hy).trans_eq
      (card_map_of_injective (S : Subgroup G).subtype_injective).symm)
  exact ⟨T, (eq_of_le_of_card_ge hCU hcard).symm⟩

end Sylow
