module

public import Theory.GroupTheory.PCoreProduct
public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# Prime cores of central products with prime-group intersection

For commuting factors whose intersection is a p-group, multiplication maps
 their direct product onto their join with p-group kernel. Prime-core lifting
 therefore identifies the actual embedded core with the join of the two
 embedded cores. The conclusion preserves both factor inclusions.

This supplies the quaternion core in Aschbacher, *Sporadic Groups* (1994),
Lemma 45.2, printed p.242.
-/

public section
namespace Subgroup

theorem pCoreIn_sup_of_commuting_of_intersection_isPGroup {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (A B : Subgroup G) (hc : ∀ a : A, ∀ b : B, Commute (a : G) (b : G))
    (hp : IsPGroup p (A ⊓ B : Subgroup G)) :
    (A ⊔ B).pCoreIn p = A.pCoreIn p ⊔ B.pCoreIn p := by
  let f := A.subtype.noncommCoprod B.subtype hc
  have hr : f.range = A ⊔ B := by
    exact (MonoidHom.noncommCoprod_range A.subtype B.subtype hc).trans
      (by rw [A.range_subtype, B.range_subtype])
  let q : A × B →* (A ⊔ B : Subgroup G) := f.codRestrict _ (fun x => hr ▸ ⟨x, rfl⟩)
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨y, hy⟩ := (show (x : G) ∈ f.range by rw [hr]; exact x.property)
    exact ⟨y, Subtype.ext hy⟩
  let k : q.ker →* (A ⊓ B : Subgroup G) :=
    { toFun x := ⟨x.val.1, x.val.1.property, by
        have hh : (x.val.1 : G) * (x.val.2 : G) = 1 := congrArg Subtype.val x.property
        rw [eq_inv_of_mul_eq_one_left hh]
        exact B.inv_mem x.val.2.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hk : Function.Injective k := by
    intro x y he
    have he0 := congrArg Subtype.val he
    change (x.val.1 : G) = (y.val.1 : G) at he0
    have hl : x.val.1 = y.val.1 := Subtype.ext he0
    have hx : (x.val.1 : G) * (x.val.2 : G) = 1 := congrArg Subtype.val x.property
    have hy : (y.val.1 : G) * (y.val.2 : G) = 1 := congrArg Subtype.val y.property
    apply Subtype.ext
    apply Prod.ext hl
    apply Subtype.ext
    apply mul_left_cancel (a := (x.val.1 : G))
    rw [hx, hl, hy]
  have he : (pCore p (A × B)).map q = pCore p (A ⊔ B : Subgroup G) := by
    rw [← q.comap_pCore_of_ker_isPGroup hq (hp.of_injective k hk), map_comap_eq_self]
    rw [MonoidHom.range_eq_top.mpr hq]
    exact le_top
  change (pCore p (A ⊔ B : Subgroup G)).map (A ⊔ B).subtype = _
  rw [← he, pCore_prod, map_map]
  apply le_antisymm
  · rintro x ⟨⟨a,b⟩, hab, rfl⟩
    exact mul_mem_sup (mem_map_of_mem A.subtype hab.1) (mem_map_of_mem B.subtype hab.2)
  · apply sup_le
    · rintro x ⟨a,ha,rfl⟩
      refine ⟨(a,1), ⟨ha,one_mem _⟩, ?_⟩
      exact mul_one _
    · rintro x ⟨b,hb,rfl⟩
      refine ⟨(1,b), ⟨one_mem _,hb⟩, ?_⟩
      exact one_mul _

end Subgroup
