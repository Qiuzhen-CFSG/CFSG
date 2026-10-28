module

public import Theory.GroupTheory.SaturatedCentralizer

/-!
# Selecting a fully centralized element in a fusion-invariant set

Choose a Sylow subgroup of an element centralizer and conjugate an ambient
Sylow overgroup into the prescribed Sylow subgroup. A predicate invariant
under conjugacy survives this choice. The local version works inside any
subgroup containing the prescribed Sylow subgroup and states maximality as
a prime-free relative index in the ambient image of the local centralizer.

Source: Sylow conjugacy; the selection used by Janko–Thompson,
Math. Z. 113 (1970), §4, printed pp.392–393.
-/

open Subgroup

namespace Sylow

/-- A conjugate can be chosen whose Sylow centralizer has prime-free index
in the full centralizer. -/
public theorem exists_conjugate_with_centralizer_not_dvd_relIndex
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (x : S) :
    ∃ y : S, IsConj (x : G) (y : G) ∧
      ¬ p ∣ ((centralizer ({y} : Set S)).map (S : Subgroup G).subtype).relIndex
        (centralizer ({(y : G)} : Set G)) := by
  obtain ⟨y, hxy, hmax⟩ := S.exists_conjugate_with_saturated_centralizer x
  let C := centralizer ({(y : G)} : Set G)
  let E := (centralizer ({y} : Set S)).map (S : Subgroup G).subtype
  have hEC : E ≤ C := by
    dsimp only [E]
    rw [map_subtype_centralizer_singleton]
    exact inf_le_right
  have hpE : IsPGroup p E := (S.isPGroup'.to_subgroup _).map _
  obtain ⟨T, hET⟩ := (hpE.comap_subtype (K := C)).exists_le_sylow
  have hmap : (T : Subgroup C).map C.subtype = E :=
    hmax _ (T.isPGroup'.map _) (by
      change E ≤ _
      rw [← map_subgroupOf_eq_of_le hEC]
      exact map_mono hET) (map_subtype_le _)
  have heq : E.subgroupOf C = (T : Subgroup C) := by
    apply map_injective C.subtype_injective
    rw [map_subgroupOf_eq_of_le hEC, hmap]
  refine ⟨y, hxy, ?_⟩
  change ¬ p ∣ (E.subgroupOf C).index
  rw [heq]
  exact T.not_dvd_index

/-- Local Sylow conjugacy preserves any fusion-invariant predicate on the
given Sylow subgroup. The local subgroup need not normalize that Sylow. -/
public theorem exists_fusion_invariant_with_local_centralizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (L : Subgroup G) (hSL : (S : Subgroup G) ≤ L)
    (P : S → Prop)
    (hP : ∀ x y : S, P x →
      IsConj (⟨(x : G), hSL x.property⟩ : L) ⟨(y : G), hSL y.property⟩ → P y)
    (x : S) (hx : P x) :
    ∃ y : S, P y ∧ orderOf y = orderOf x ∧
      ¬ p ∣ ((centralizer ({y} : Set S)).map (S : Subgroup G).subtype).relIndex
        (L ⊓ centralizer ({(y : G)} : Set G)) := by
  let T := S.subtype hSL
  let e : T ≃* S := subgroupOfEquivOfLe hSL
  obtain ⟨u, hxu, hu⟩ := T.exists_conjugate_with_centralizer_not_dvd_relIndex (e.symm x)
  let y := e u
  have hxy : IsConj (⟨(x : G), hSL x.property⟩ : L) ⟨(y : G), hSL y.property⟩ := by
    exact hxu
  have horder : orderOf y = orderOf x := by
    obtain ⟨a, ha⟩ := isConj_iff.mp hxy
    have hh := (MulAut.conj a).orderOf_eq (⟨(x : G), hSL x.property⟩ : L)
    change orderOf (a * _ * a⁻¹) = _ at hh
    rw [ha] at hh
    have hh' : orderOf (y : G) = orderOf (x : G) := by
      simpa only [← Subgroup.orderOf_coe] using hh
    exact (Subgroup.orderOf_coe y).symm.trans (hh'.trans (Subgroup.orderOf_coe x))
  let U := (centralizer ({u} : Set T)).map (T : Subgroup L).subtype
  have hUE : U.map L.subtype =
      (centralizer ({y} : Set S)).map (S : Subgroup G).subtype := by
    apply le_antisymm
    · rintro v ⟨n, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨e w, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      simpa only [map_mul] using congrArg e (mem_centralizer_singleton_iff.mp hw)
    · rintro v ⟨w, hw, rfl⟩
      refine ⟨((e.symm w : T) : L), ⟨e.symm w, ?_, rfl⟩, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using mem_centralizer_singleton_iff.mp hw
  refine ⟨y, hP x y hx hxy, horder, ?_⟩
  rw [← hUE]
  change ¬ p ∣ (U.map L.subtype).relIndex (L ⊓ centralizer ({((u : L) : G)} : Set G))
  rw [← map_subtype_centralizer_singleton L (u : L),
    relIndex_map_map_of_injective _ _ L.subtype_injective]
  exact hu

end Sylow
