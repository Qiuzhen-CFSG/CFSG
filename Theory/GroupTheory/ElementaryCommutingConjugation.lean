module

public import Theory.GroupTheory.ElementaryCommutingTwoGroup

/-!
# Stabilizers of elementary commuting components

The elements whose conjugation keeps an elementary subgroup in its commuting
component form a subgroup. This subgroup contains the full normalizer of
every vertex in the component. Rank-three binary vertices in a common
two-subgroup give the same stabilizer.

The proof uses transport of paths under conjugation and concatenation of
paths. These are the component-stabilizer facts of GLS2, Section 22,
especially Lemma 22.2 (`refs/KGroup/GLS2/ChapterF.tex`).
-/

namespace Subgroup

private theorem map_conj_one_eq
    {G : Type*} [Group G] (A : Subgroup G) :
    A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
  have h : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [h, map_id]

private theorem map_conj_mul_eq
    {G : Type*} [Group G] (A : Subgroup G) (x y : G) :
    (A.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom =
      A.map (MulAut.conj (x * y)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext a
  simp [MulAut.conj_apply, mul_assoc]

/-- The stabilizer of the actual commuting component containing a valid vertex. -/
@[expose] public def elementaryCommutingStabilizer
    {G : Type*} [Group G] (p : ℕ) (A : Subgroup G)
    [IsElementaryAbelian p A] (hA : p ^ 2 ≤ Nat.card A) : Subgroup G where
  carrier := {g | ElementaryCommutingConnected p A (A.map (MulAut.conj g).toMonoidHom)}
  one_mem' := by
    change ElementaryCommutingConnected p A (A.map (MulAut.conj (1 : G)).toMonoidHom)
    rw [map_conj_one_eq]
    exact ElementaryCommutingConnected.refl inferInstance hA
  mul_mem' := by
    intro x y hx hy
    exact hx.trans (by simpa only [map_conj_mul_eq] using hy.map (MulAut.conj x))
  inv_mem' := by
    intro x hx
    have h := hx.map (MulAut.conj x⁻¹)
    rw [map_conj_mul_eq, inv_mul_cancel, map_conj_one_eq] at h
    exact h.symm

/-- The normalizer of any vertex preserves its whole commuting component. -/
public theorem normalizer_le_elementaryCommutingStabilizer
    {G : Type*} [Group G] {p : ℕ} (A B : Subgroup G)
    [IsElementaryAbelian p A] (hA : p ^ 2 ≤ Nat.card A)
    (hAB : ElementaryCommutingConnected p A B) :
    normalizer (B : Set G) ≤ elementaryCommutingStabilizer p A hA := by
  intro g hg
  have hB : B.map (MulAut.conj g).toMonoidHom = B :=
    mem_normalizer_iff_map_conj_eq.mp hg
  exact hAB.trans (by simpa only [hB] using hAB.symm.map (MulAut.conj g))

/-- Connected vertices have equal component stabilizers. -/
public theorem elementaryCommutingStabilizer_eq_of_connected
    {G : Type*} [Group G] {p : ℕ} (A B : Subgroup G)
    [IsElementaryAbelian p A] [IsElementaryAbelian p B]
    (hA : p ^ 2 ≤ Nat.card A) (hB : p ^ 2 ≤ Nat.card B)
    (hAB : ElementaryCommutingConnected p A B) :
    elementaryCommutingStabilizer p A hA = elementaryCommutingStabilizer p B hB := by
  apply le_antisymm
  · intro g hg
    exact hAB.symm.trans (hg.trans (hAB.map (MulAut.conj g)))
  · intro g hg
    exact hAB.trans (hg.trans (hAB.symm.map (MulAut.conj g)))

/-- The full normalizer of a two-subgroup containing a rank-three binary
vertex preserves that vertex's commuting component. -/
public theorem normalizer_le_elementaryCommutingStabilizer_of_le_twoGroup
    {G : Type*} [Group G] [Finite G]
    (P A : Subgroup G) (hP : IsPGroup 2 P)
    [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A) (hAP : A ≤ P) :
    normalizer (P : Set G) ≤ elementaryCommutingStabilizer 2 A (by omega) := by
  intro g hg
  let e := MulAut.conj g
  let : IsElementaryAbelian 2 (A.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hconj : A.map e.toMonoidHom ≤ P := by
    rintro x ⟨a, ha, rfl⟩
    exact (mem_normalizer_iff.mp hg a).mp (hAP ha)
  exact elementaryCommutingConnected_of_le_twoGroup P A (A.map e.toMonoidHom) hP
    hA (by simpa only [card_map_of_injective (f := e.toMonoidHom) e.injective] using hA)
    hAP hconj

/-- A two-subgroup containing a rank-three binary vertex preserves its component. -/
public theorem twoGroup_le_elementaryCommutingStabilizer
    {G : Type*} [Group G] [Finite G]
    (P A : Subgroup G) (hP : IsPGroup 2 P)
    [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A) (hAP : A ≤ P) :
    P ≤ elementaryCommutingStabilizer 2 A (by omega) :=
  P.le_normalizer.trans
    (normalizer_le_elementaryCommutingStabilizer_of_le_twoGroup P A hP hA hAP)

end Subgroup
