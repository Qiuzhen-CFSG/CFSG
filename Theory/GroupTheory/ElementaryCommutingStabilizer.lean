module
public import Theory.GroupTheory.ElementaryCommutingConnectivity

/-!
# Stabilizers of elementary commuting components

Conjugation acts on the actual elementary commuting graph. The elements carrying
a valid vertex into its own component form a subgroup. A normalizer of any
vertex in the component is contained in this subgroup. This is the component
stabilizer criterion of GLS2, Section 22, Lemma 22.2
(`refs/KGroup/GLS2/ChapterF.tex`).
-/

namespace Subgroup

private theorem map_conj_mul {G : Type*} [Group G] (A : Subgroup G) (g h : G) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g * h)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_one {G : Type*} [Group G] (A : Subgroup G) :
    A.map (MulAut.conj (1 : G)).toMonoidHom = A := by
  have h : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [h, map_id]

/-- The stabilizer of the commuting component containing a valid vertex. -/
@[expose] public def elementaryCommutingComponentStabilizer
    (p : ℕ) {G : Type*} [Group G] (A : Subgroup G)
    (hA : IsElementaryAbelian p A) (hcard : p ^ 2 ≤ Nat.card A) : Subgroup G where
  carrier := {g | ElementaryCommutingConnected p A (A.map (MulAut.conj g).toMonoidHom)}
  one_mem' := by
    change ElementaryCommutingConnected p A (A.map (MulAut.conj (1 : G)).toMonoidHom)
    rw [map_conj_one]
    exact ElementaryCommutingConnected.refl hA hcard
  mul_mem' := by
    intro g h hg hh
    change ElementaryCommutingConnected p A (A.map (MulAut.conj (g * h)).toMonoidHom)
    simpa only [map_conj_mul] using hg.trans (hh.map (MulAut.conj g))
  inv_mem' := by
    intro g hg
    have hh := hg.symm.map (MulAut.conj g⁻¹)
    change ElementaryCommutingConnected p A (A.map (MulAut.conj g⁻¹).toMonoidHom)
    simpa only [map_conj_mul, inv_mul_cancel, map_conj_one] using hh

@[simp] public theorem mem_elementaryCommutingComponentStabilizer
    {p : ℕ} {G : Type*} [Group G] (A : Subgroup G)
    (hA : IsElementaryAbelian p A) (hcard : p ^ 2 ≤ Nat.card A) (g : G) :
    g ∈ elementaryCommutingComponentStabilizer p A hA hcard ↔
      ElementaryCommutingConnected p A (A.map (MulAut.conj g).toMonoidHom) := Iff.rfl

/-- One connected vertex fixed by conjugation suffices to stabilize the component. -/
public theorem normalizer_le_elementaryCommutingComponentStabilizer
    {p : ℕ} {G : Type*} [Group G] (A B : Subgroup G)
    (hA : IsElementaryAbelian p A) (hcard : p ^ 2 ≤ Nat.card A)
    (hAB : ElementaryCommutingConnected p A B) :
    normalizer (B : Set G) ≤ elementaryCommutingComponentStabilizer p A hA hcard := by
  intro g hg
  have hmap := hAB.symm.map (MulAut.conj g)
  have hBg : B.map (MulAut.conj g).toMonoidHom = B := mem_normalizer_iff_map_conj_eq.mp hg
  rw [hBg] at hmap
  exact hAB.trans hmap

end Subgroup
