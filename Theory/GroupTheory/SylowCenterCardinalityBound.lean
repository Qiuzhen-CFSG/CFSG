module

public import Theory.GroupTheory.PGroup.NormalSubgroups
public import Mathlib.GroupTheory.Sylow

/-!
# A Sylow-center cardinality bound

If a two-subgroup R normalizes C and C avoids the center of R, then R meets
C trivially: a nontrivial normal intersection would meet the center of R.
Multiplication therefore injects R × C into any common overgroup.

Suppose C is normal in a Sylow two-subgroup T, and T normalizes V = Z(R),
with C disjoint from V. Sylow conjugacy inside N(V) places R in a conjugate
of T. The corresponding conjugate of C is still disjoint from V, so the
first bound gives |R||C| ≤ |T|. All normality is relative to the indicated
subgroups; no normality in the ambient group is required.

Source: the group-theoretic argument in Aschbacher–Smith, combined manuscript
of 1 March 2004, proof of 16.3.4, printed p.1178 / PDF p.1195.
-/

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A normalized two-subgroup disjoint from the center of R has product
cardinality bounded by every common overgroup. -/
public theorem card_mul_le_of_disjoint_center (R C S : Subgroup G)
    (hR : IsPGroup 2 R) (hRS : R ≤ S) (hCS : C ≤ S)
    (hn : R ≤ normalizer (C : Set G))
    (hd : Disjoint C ((center R).map R.subtype)) :
    Nat.card R * Nat.card C ≤ Nat.card S := by
  have hbot : C.subgroupOf R = ⊥ := by
    by_contra hne
    let : (C.subgroupOf R).Normal := normal_subgroupOf_of_le_normalizer hn
    let : Nontrivial (C.subgroupOf R) := (nontrivial_iff_ne_bot _).mpr hne
    let : Fact (IsPGroup 2 R) := ⟨hR⟩
    obtain ⟨x, hx, hxZ⟩ := exists_nontrivial_center_mem_normal (C.subgroupOf R) (p := 2)
    have he : ((x : R) : G) = 1 := disjoint_def.mp hd x.property ⟨x, hxZ, rfl⟩
    exact hx (Subtype.ext (Subtype.ext he))
  have hdis : Disjoint R C := by
    apply disjoint_def.mpr
    intro x hxR hxC
    have hx : (⟨x, hxR⟩ : R) ∈ C.subgroupOf R := hxC
    rw [hbot, mem_bot] at hx
    exact congrArg Subtype.val hx
  let f : R × C → S := fun x => ⟨x.1 * x.2, S.mul_mem (hRS x.1.property) (hCS x.2.property)⟩
  have hinj : Function.Injective f := fun _ _ h =>
    mul_injective_of_disjoint hdis (congrArg Subtype.val h)
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective f hinj

/-- Transport a normal subgroup of a Sylow two-subgroup into the normalizer
of a prescribed Sylow center. The center-intersection theorem bounds the
product of the two orders. -/
public theorem sylow_center_card_bound (T : Sylow 2 G) (C V R : Subgroup G)
    (hC : C ≤ (T : Subgroup G)) (hCn : (T : Subgroup G) ≤ normalizer (C : Set G))
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hCV : Disjoint C V) (hR : IsPGroup 2 R)
    (hZ : (center R).map R.subtype = V) :
    Nat.card R * Nat.card C ≤ Nat.card T := by
  let N := normalizer (V : Set G)
  have hRN : R ≤ N := by
    apply le_trans _ (centralizer_le_normalizer (V : Set G))
    intro r hr v hv
    rw [← hZ] at hv
    obtain ⟨v, hv, rfl⟩ := hv
    exact (congrArg Subtype.val (mem_center_iff.mp hv ⟨r, hr⟩)).symm
  obtain ⟨S, hRS⟩ := (hR.comap_of_injective N.subtype N.subtype_injective).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq N (T.subtype hTV) S
  let f := (MulAut.conj (g : G)).toMonoidHom
  let U := (T : Subgroup G).map f
  let D := C.map f
  have hU : (S : Subgroup N).map N.subtype = U := by
    rw [← hg]
    change (((T : Subgroup G).subgroupOf N).map
      (MulAut.conj g).toMonoidHom).map N.subtype = U
    rw [map_map]
    have hcomp : N.subtype.comp (MulAut.conj g).toMonoidHom = f.comp N.subtype := by
      ext x
      rfl
    rw [hcomp, ← map_map, map_subgroupOf_eq_of_le hTV]
  have hRU : R ≤ U := by
    intro r hr
    rw [← hU]
    exact ⟨⟨r, hRN hr⟩, hRS hr, rfl⟩
  have hDU : D ≤ U := map_mono hC
  have hUD : U ≤ normalizer (D : Set G) :=
    (map_mono hCn).trans (le_normalizer_map f)
  have hDV : Disjoint D V := by
    have hgV : V.map f = V := mem_normalizer_iff_map_conj_eq.mp g.property
    rw [← hgV]
    exact Subgroup.disjoint_map (MulAut.conj (g : G)).injective hCV
  have hb := card_mul_le_of_disjoint_center R D U hR hRU hDU
    (hRU.trans hUD) (hZ.symm ▸ hDV)
  simpa only [U, D, f, card_map_of_injective (f := (MulAut.conj (g : G)).toMonoidHom) (MulAut.conj (g : G)).injective] using hb

end Subgroup
