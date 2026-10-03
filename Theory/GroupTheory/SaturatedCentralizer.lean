module

public import Theory.GroupTheory.SylowCentralizerConjugacy

/-!
# Saturated conjugate centralizers

An element in a Sylow subgroup has a conjugate whose Sylow centralizer is
maximal among ambient p-subgroups centralizing it. Choose a Sylow subgroup
of its centralizer and conjugate an ambient Sylow overgroup into the given
Sylow subgroup.

Applying this inside the centralizer of a central Sylow element preserves
that element and gives saturation in the simultaneous centralizer. In
particular a distinct conjugate stays distinct. This is the Sylow-selection
step in Janko–Thompson (1970), §4, Case 2, printed p.393.
-/

open Subgroup
open scoped Pointwise

namespace Sylow

/-- Choose a conjugate whose centralizer in the given Sylow is a maximal
p-subgroup of its ambient centralizer. -/
public theorem exists_conjugate_with_saturated_centralizer {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (x : S) :
    ∃ t : S, IsConj (x : G) (t : G) ∧
      ∀ V : Subgroup G, IsPGroup p V →
        (centralizer ({t} : Set S)).map (S : Subgroup G).subtype ≤ V →
        V ≤ centralizer ({(t : G)} : Set G) →
        V = (centralizer ({t} : Set S)).map (S : Subgroup G).subtype := by
  let C := centralizer ({(x : G)} : Set G)
  let U := (centralizer ({x} : Set S)).map (S : Subgroup G).subtype
  have hUC : U ≤ C := by
    change (centralizer ({x} : Set S)).map (S : Subgroup G).subtype ≤ C
    rw [map_subtype_centralizer_singleton]
    exact inf_le_right
  have hUp : IsPGroup p U := (S.isPGroup'.to_subgroup _).map _
  obtain ⟨Q, hQ⟩ := (hUp.comap_subtype (K := C)).exists_le_sylow
  let K := (Q : Subgroup C).map C.subtype
  have hKC : K ≤ C := map_subtype_le _
  have hKp : IsPGroup p K := Q.isPGroup'.map _
  have hUK : U ≤ K := by
    rw [← map_subgroupOf_eq_of_le hUC]
    exact map_mono hQ
  have hmax (V : Subgroup G) (hpV : IsPGroup p V) (hKV : K ≤ V) (hVC : V ≤ C) : V = K := by
    have he := Q.is_maximal' (hpV.comap_subtype (K := C)) (by
      intro q hq
      exact hKV (mem_map_of_mem C.subtype hq))
    have := congrArg (fun L : Subgroup C => L.map C.subtype) he
    change (V.subgroupOf C).map C.subtype = K at this
    rwa [map_subgroupOf_eq_of_le hVC] at this
  obtain ⟨T, hKT⟩ := hKp.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G T S
  let f : G ≃* G := MulAut.conj a
  let L := K.map f.toMonoidHom
  have hLS : L ≤ (S : Subgroup G) := by
    rw [← ha]
    exact map_mono hKT
  have hxK : (x : G) ∈ K := hUK (mem_map_of_mem (S : Subgroup G).subtype
    (mem_centralizer_singleton_iff.mpr rfl))
  let t : S := ⟨f x, hLS (mem_map_of_mem f.toMonoidHom hxK)⟩
  have hLC : L ≤ centralizer ({(t : G)} : Set G) := by
    rintro y ⟨k, hk, rfl⟩
    exact mem_centralizer_singleton_iff.mpr (by
      change f k * f x = f x * f k
      simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp (hKC hk)))
  have hmaxL (V : Subgroup G) (hpV : IsPGroup p V) (hLV : L ≤ V)
      (hVC : V ≤ centralizer ({(t : G)} : Set G)) : V = L := by
    have hpre : V.map f.symm.toMonoidHom = K := hmax _ (hpV.map _) (by
      intro k hk
      exact ⟨f k, hLV (mem_map_of_mem f.toMonoidHom hk), f.symm_apply_apply k⟩) (by
      rintro y ⟨v, hv, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      apply f.injective
      change f (f.symm v * (x : G)) = f ((x : G) * f.symm v)
      simpa only [map_mul, f.apply_symm_apply] using mem_centralizer_singleton_iff.mp (hVC hv))
    have he := congrArg (fun L : Subgroup G => L.map f.toMonoidHom) hpre
    have hid : f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id G := by
      ext v
      exact f.apply_symm_apply v
    simpa only [map_map, hid, map_id] using he
  let E := (centralizer ({t} : Set S)).map (S : Subgroup G).subtype
  have hLE : L ≤ E := by
    dsimp only [E]
    rw [map_subtype_centralizer_singleton]
    exact le_inf hLS hLC
  have hE : E = L := hmaxL E ((S.isPGroup'.to_subgroup _).map _) hLE (by
    dsimp only [E]
    rw [map_subtype_centralizer_singleton]
    exact inf_le_right)
  refine ⟨t, isConj_iff.mpr ⟨a, rfl⟩, ?_⟩
  intro V hpV hEV hVC
  exact (hmaxL V hpV (hE ▸ hEV) hVC).trans hE.symm

end Sylow

namespace Sylow

/-- A distinct conjugate of a central Sylow element can be chosen with its
Sylow centralizer maximal in the simultaneous ambient centralizer. -/
public theorem exists_distinct_conjugate_with_saturated_common_centralizer {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (z : S) (hzC : z ∈ center S)
    (x : S) (hx : x ≠ z) (hxz : IsConj (z : G) (x : G)) :
    ∃ t : S, t ≠ z ∧ IsConj (z : G) (t : G) ∧
      ∀ V : Subgroup G, IsPGroup p V →
        (centralizer ({t} : Set S)).map (S : Subgroup G).subtype ≤ V →
        V ≤ centralizer ({(z : G), (t : G)} : Set G) →
        V = (centralizer ({t} : Set S)).map (S : Subgroup G).subtype := by
  let N := centralizer ({(z : G)} : Set G)
  have hSN : (S : Subgroup G) ≤ N := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp hzC ⟨s, hs⟩))
  let T := S.subtype hSN
  let e : T ≃* S := subgroupOfEquivOfLe hSN
  obtain ⟨u, hxu, hmax⟩ := T.exists_conjugate_with_saturated_centralizer (e.symm x)
  let t := e u
  have hconj : IsConj (x : G) (t : G) := by
    obtain ⟨a, ha⟩ := isConj_iff.mp hxu
    exact isConj_iff.mpr ⟨(a : G), congrArg Subtype.val ha⟩
  have hne : t ≠ z := by
    intro heq
    apply hx
    obtain ⟨a, ha⟩ := isConj_iff.mp hxu
    have hh := congrArg Subtype.val ha
    change (a : G) * (x : G) * (a : G)⁻¹ = (t : G) at hh
    have hfix : (a : G) * (z : G) * (a : G)⁻¹ = z :=
      mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp a.property)
    rw [heq] at hh
    exact Subtype.ext ((MulAut.conj (a : G)).injective (hh.trans hfix.symm))
  let U := (centralizer ({u} : Set T)).map (T : Subgroup N).subtype
  let E := (centralizer ({t} : Set S)).map (S : Subgroup G).subtype
  have hUE : U.map N.subtype = E := by
    apply le_antisymm
    · rintro y ⟨n, ⟨v, hv, rfl⟩, rfl⟩
      refine ⟨e v, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hv)
    · rintro y ⟨v, hv, rfl⟩
      refine ⟨((e.symm v : T) : N), ⟨e.symm v, ?_, rfl⟩, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hv
  refine ⟨t, hne, hxz.trans hconj, ?_⟩
  intro V hpV hEV hVC
  have hVN : V ≤ N := by
    intro v hv
    exact mem_centralizer_singleton_iff.mpr (hVC hv z (by simp)).symm
  have hVU : V.subgroupOf N = U := hmax _ hpV.comap_subtype (by
    intro n hn
    have hnE : (n : G) ∈ E := by
      rw [← hUE]
      exact mem_map_of_mem N.subtype hn
    exact hEV hnE) (by
    intro n hn
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext ((hVC hn t (by simp)).symm))
  have he := congrArg (fun L : Subgroup N => L.map N.subtype) hVU
  rwa [map_subgroupOf_eq_of_le hVN, hUE] at he

end Sylow
