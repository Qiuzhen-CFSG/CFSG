module

public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable

/-!
# Normalizers in solvable extensions

For a normal subgroup L of G with solvable quotient, solvability of N_L(A)
implies solvability of N_G(A). Restrict the quotient map to the ambient
normalizer: its kernel embeds in the intrinsic normalizer. A characteristic
subgroup of a Sylow intersection with L is normalized by the original ambient
Sylow. Intrinsic movement of an element survives the inclusion into G.

These elementary extension arguments supply the two-extension step in
Aschbacher--Smith E.1.14(7), printed p.214, without an automorphism-classification
or a simplicity hypothesis.
-/

public section

open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- Intrinsic normalizer solvability extends across a solvable ambient quotient. -/
theorem normalizer_map_subtype_isSolvable (L : Subgroup G) [L.Normal]
    [Group.IsSolvable (G ⧸ L)] (A : Subgroup L)
    [Group.IsSolvable (normalizer (A : Set L))] :
    Group.IsSolvable (normalizer (A.map L.subtype : Set G)) := by
  let N := normalizer (A.map L.subtype : Set G)
  let f : N →* G ⧸ L := (QuotientGroup.mk' L).comp N.subtype
  have hk (x : f.ker) : (x.val : G) ∈ L :=
    (QuotientGroup.eq_one_iff (x.val : G)).mp x.property
  have hnorm : N.comap L.subtype = normalizer (A : Set L) := by
    rw [comap_normalizer_eq_of_le_range (map_le_range L.subtype A),
      comap_map_eq_self_of_injective L.subtype_injective]
  let i : f.ker →* normalizer (A : Set L) :=
    { toFun := fun x => ⟨⟨x.val, hk x⟩, by
        rw [← hnorm]
        exact x.val.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hi : Function.Injective i := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun a : normalizer (A : Set L) =>
      (a.val : G)) h))
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hi
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f (by rw [range_subtype])

/-- The ambient Sylow normalizes each characteristic subgroup of its normal-subgroup intersection. -/
theorem sylow_le_normalizer_characteristic_intersection
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = (T : Subgroup G) ⊓ L)
    (A : Subgroup S) [A.Characteristic] :
    (T : Subgroup G) ≤ normalizer ((A.map (S : Subgroup L).subtype).map L.subtype : Set G) := by
  let R := (T : Subgroup G) ⊓ L
  let e : S ≃* R := ((S : Subgroup L).equivMapOfInjective L.subtype
    L.subtype_injective).trans (MulEquiv.subgroupCongr hS)
  let B := A.map e.toMonoidHom
  have hB : B.Characteristic := by
    apply characteristic_iff_le_comap.mpr
    intro a x hx
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨(MulAut.congr e.symm a) y,
      characteristic_iff_le_comap.mp inferInstance (MulAut.congr e.symm a) hy, ?_⟩
    exact e.apply_symm_apply (a (e y))
  let := hB
  have hTN : (T : Subgroup G) ≤ normalizer (R : Set G) := by
    apply le_normalizer_iff.mpr
    intro t ht r hr
    exact ⟨(T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ht hr.1)
      ((T : Subgroup G).inv_mem ht), (inferInstance : L.Normal).conj_mem _ hr.2 _⟩
  have hh := hTN.trans (normalizer_le_normalizer_characteristic_image R B)
  convert hh using 1
  rw [map_map, map_map]
  rfl

/-- An intrinsic normalizer that moves an element still moves it in the ambient group. -/
theorem normalizer_image_not_le_centralizer (L : Subgroup G) (A : Subgroup L)
    (z : L) (h : ¬ normalizer (A : Set L) ≤ centralizer ({z} : Set L)) :
    ¬ normalizer (A.map L.subtype : Set G) ≤ centralizer ({(z : G)} : Set G) := by
  intro hn
  apply h
  intro x hx
  have hxN : (x : G) ∈ normalizer (A.map L.subtype : Set G) :=
    le_normalizer_map L.subtype ⟨x, hx, rfl⟩
  exact mem_centralizer_singleton_iff.mpr (Subtype.ext
    (mem_centralizer_singleton_iff.mp (hn hxN)))
end Subgroup
