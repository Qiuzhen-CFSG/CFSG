module
public import Theory.GroupTheory.SylowCentralizerConjugacy

/-!
# Cardinal bounds from saturated centralizers

A maximal p-subgroup of an element centralizer is a Sylow subgroup there.
Conjugacy identifies the two ambient centralizers, so its order bounds every
p-subgroup centralizing the conjugate element. This formulation requires no
p-group assumption on either full centralizer.

Source: the Sylow comparison in Janko–Thompson, Math. Z. 113 (1970), §4,
printed p.391.
-/

open Subgroup
namespace Subgroup

/-- A saturated p-subgroup of one centralizer bounds every p-subgroup of a
conjugate centralizer. -/
public theorem card_le_of_isConj_of_saturated_centralizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (x y : G) (hxy : IsConj x y) (E : Subgroup G) (hEp : IsPGroup p E)
    (hEC : E ≤ centralizer ({x} : Set G))
    (hmax : ∀ V : Subgroup G, IsPGroup p V → E ≤ V →
      V ≤ centralizer ({x} : Set G) → V = E)
    (U : Subgroup G) (hUp : IsPGroup p U)
    (hUC : U ≤ centralizer ({y} : Set G)) : Nat.card U ≤ Nat.card E := by
  let C := centralizer ({x} : Set G)
  obtain ⟨T, hET⟩ := (hEp.comap_subtype (K := C)).exists_le_sylow
  have hTE : (T : Subgroup C).map C.subtype = E :=
    hmax _ (T.isPGroup'.map _) (by
      rw [← map_subgroupOf_eq_of_le hEC]
      exact map_mono hET) (map_subtype_le _)
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  let f := (MulAut.conj g).symm
  have hfy : f y = x := f.symm.injective (by
    rw [f.symm_apply_apply]
    exact hg.symm)
  let V := U.map f.toMonoidHom
  have hVC : V ≤ C := by
    rintro _ ⟨u, hu, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    change f u * x = x * f u
    have hh := congrArg f (mem_centralizer_singleton_iff.mp (hUC hu))
    simpa only [map_mul, hfy] using hh
  obtain ⟨R, hVR⟩ := ((hUp.map f.toMonoidHom).comap_subtype (K := C)).exists_le_sylow
  calc
    Nat.card U = Nat.card V := (card_map_of_injective f.injective).symm
    _ = Nat.card (V.subgroupOf C) :=
      (Nat.card_congr (subgroupOfEquivOfLe hVC).toEquiv).symm
    _ ≤ Nat.card R := card_le_of_le hVR
    _ = Nat.card T := Nat.card_congr (R.equiv T).toEquiv
    _ = Nat.card ((T : Subgroup C).map C.subtype) :=
      (card_map_of_injective C.subtype_injective).symm
    _ = Nat.card E := by rw [hTE]
end Subgroup
