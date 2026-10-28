module

public import Theory.GroupAction.LargeOrbitSylow
public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupTheory.TINormalizerControl

/-!
# Rechoosing a point inside its component orbit

Let L normalize V and let T normalize both. If V is TI in N_G(L),
the centralizer of a nonidentity point of V lies in N_G(L) ∩ N_G(V).
The latter group acts by its literal ambient conjugation on V. An L-orbit
larger than half of V is also an orbit of this whole acting group.
Sylow rechoice in that orbit therefore uses an element of L and computes
its T-centralizer index from the original L-orbit length.

Source: the local Sylow choice in Aschbacher--Smith 12.5.9(1), printed p.821.
No weak-closure or ambient point-centralizer Sylow hypothesis is needed.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The TI property controls the entire point centralizer in N_G(L), while
a large L-orbit lets Sylow rechoice use a conjugator in L itself. -/
theorem exists_point_centralizer_sylow_in_component (T : Sylow 2 G) (L V : Subgroup G)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hLV : L ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ normalizer (L : Set G),
      V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V.map (MulAut.conj g).toMonoidHom = V)
    (x : V) (hne : (x : G) ≠ 1)
    (hlarge : Nat.card V < 2 * (centralizer ({(x : G)} : Set G)).relIndex L) :
    ∃ l : L,
      ((T : Subgroup G) ⊓ centralizer ({MulAut.conj (l : G) x} : Set G)).relIndex
          (T : Subgroup G) =
        2 ^ ((centralizer ({(x : G)} : Set G)).relIndex L).factorization 2 ∧
      ¬ 2 ∣ ((T : Subgroup G) ⊓ centralizer ({MulAut.conj (l : G) x} : Set G)).relIndex
        (normalizer (L : Set G) ⊓
          centralizer ({MulAut.conj (l : G) x} : Set G)) := by
  let B := normalizer (L : Set G) ⊓ normalizer (V : Set G)
  have hTB : (T : Subgroup G) ≤ B := le_inf hTL hTV
  have hLB : L ≤ B := le_inf L.le_normalizer hLV
  let := conjMulDistribMulActionOfLeNormalizer B V inf_le_right
  let L' := L.subgroupOf B
  let : L'.Normal := normal_subgroupOf_of_le_normalizer inf_le_left
  have hi : (MulAction.stabilizer L' x).index =
      (centralizer ({(x : G)} : Set G)).relIndex L := by
    rw [← relIndex_subgroupOf (H := centralizer ({(x : G)} : Set G)) hLB]
    congr 1
    ext l
    change ((l : B) • x = x) ↔ _
    constructor
    · intro he
      exact mem_centralizer_singleton_iff.mpr
        (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he))
    · intro he
      apply Subtype.ext
      exact mul_inv_eq_of_eq_mul (mem_centralizer_singleton_iff.mp he)
  obtain ⟨l, hiT, hiC⟩ := exists_sylow_point_in_large_normal_orbit (T.subtype hTB) L' x
    (by rwa [hi])
  let lG : L := ⟨((l : B) : G), l.property⟩
  let y : V := l • x
  have hy : (y : G) ≠ 1 := by
    intro he
    exact hne ((MulAut.conj (lG : G)).injective (he.trans (map_one _).symm))
  have hC := inf_elementCentralizer_le_normalizer_of_trivial_intersections
    hTI y.property hy
  have hstab : (MulAction.stabilizer B y).map B.subtype =
      normalizer (L : Set G) ⊓ centralizer ({(y : G)} : Set G) := by
    ext g
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨g.property.1, mem_centralizer_singleton_iff.mpr ?_⟩
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hg)
    · intro hg
      refine ⟨⟨g, hg.1, hC hg⟩, ?_, rfl⟩
      apply Subtype.ext
      exact mul_inv_eq_of_eq_mul (mem_centralizer_singleton_iff.mp hg.2)
  have hTmap : ((T.subtype hTB : Sylow 2 B) : Subgroup B).map B.subtype =
      (T : Subgroup G) := map_subgroupOf_eq_of_le hTB
  have hQmap : (((T.subtype hTB : Sylow 2 B) : Subgroup B) ⊓
      MulAction.stabilizer B y).map B.subtype =
      (T : Subgroup G) ⊓ centralizer ({(y : G)} : Set G) := by
    rw [map_inf _ _ _ B.subtype_injective, hTmap, hstab]
    rw [← inf_assoc, inf_eq_left.mpr hTL]
  refine ⟨lG, ?_, ?_⟩
  · have he := relIndex_map_map_of_injective
      (((T.subtype hTB : Sylow 2 B) : Subgroup B) ⊓ MulAction.stabilizer B y)
      ((T.subtype hTB : Sylow 2 B) : Subgroup B) B.subtype_injective
    rw [hQmap, hTmap] at he
    exact he.trans (hiT.trans (congrArg (fun n : ℕ => 2 ^ n.factorization 2) hi))
  · have he := relIndex_map_map_of_injective
      (((T.subtype hTB : Sylow 2 B) : Subgroup B) ⊓ MulAction.stabilizer B y)
      (MulAction.stabilizer B y) B.subtype_injective
    rw [hQmap, hstab] at he
    exact he ▸ hiC
end Theory.GroupTheory
