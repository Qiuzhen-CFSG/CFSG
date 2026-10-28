module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.LocalGeneration
public import Theory.GroupTheory.NormalizedSupCard
/-!
# Prime and dimension markings of the cyclic endpoints

The original cyclic-three and cyclic-five endpoint data give the literal
odd kernel, its inversion by the marked involution, a dihedral carrier,
and the three source possibilities (p,m)=(3,1),(3,2),(5,2).

Source: Aschbacher--Smith D.2.17(1)--(2) and 15.1.2(1),(3).
-/
public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.CyclicSource
universe u
variable {G V : Type u} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
private theorem dimension_of_card {n : ℕ} (hc : Nat.card (Multiplicative V) = 2 ^ n) :
    Module.finrank (ZMod 2) V = n := by
  apply Nat.pow_right_injective (by decide : 2 ≤ 2)
  change 2 ^ Module.finrank (ZMod 2) V = 2 ^ n
  have hh : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact hh.symm.trans ((Nat.card_congr (Multiplicative.toAdd (α := V))).symm.trans hc)

def PrimeDimensionOptions (p m : ℕ) : Prop :=
  (p = 3 ∧ (m = 1 ∨ m = 2)) ∨ (p = 5 ∧ m = 2)

theorem primeDimensionOptions_iff (p m : ℕ) :
    PrimeDimensionOptions p m ↔ (p = 3 ∧ (m = 1 ∨ m = 2)) ∨ (p = 5 ∧ m = 2) :=
  Iff.rfl

structure DihedralMarking (l : LocalGeneration ρ) (p m : ℕ) : Prop where
  card_kernel : Nat.card l.kernel = p
  dimension : Module.finrank (ZMod 2) V = 2 * m
  dihedral : Nonempty (G ≃* DihedralGroup p)
  inverts : ∀ x : l.kernel, l.involution * (x : G) * l.involution⁻¹ = (x : G)⁻¹

omit [Finite G] in
theorem LocalGeneration.marking_of_endpoints (l : LocalGeneration ρ) :
    letI := BinaryGroupAction.action ρ
    letI : Finite V := Module.finite_of_finite (ZMod 2)
    letI : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
    letI := l.normal
    (Section02.CyclicThreeEndpoint (V := Multiplicative V) l.kernel l.involution ∨
      Section02.CyclicFiveEndpoint (V := Multiplicative V) l.kernel l.involution) →
    ∃ p m, PrimeDimensionOptions p m ∧ DihedralMarking l p m := by
  let := BinaryGroupAction.action ρ
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let := l.normal
  intro he
  rcases he with h3 | h5
  · have hc : Nat.card l.kernel = 3 := by
      obtain ⟨e⟩ := h3.kernel_equiv
      exact (Nat.card_congr e.toEquiv).trans (by simp)
    obtain ⟨e⟩ := h3.ambient_equiv
    let j : G ≃* DihedralGroup 3 := e.trans nonempty_dihedralThreeEquivPerm.some.symm
    rcases h3.dimensions with hd | hd
    · exact ⟨3,1,Or.inl ⟨rfl,Or.inl rfl⟩,⟨hc,by simpa using dimension_of_card (n := 2) hd.1,⟨j⟩,h3.inverts⟩⟩
    · exact ⟨3,2,Or.inl ⟨rfl,Or.inr rfl⟩,⟨hc,by simpa using dimension_of_card (n := 4) hd.1,⟨j⟩,h3.inverts⟩⟩
  · have hc : Nat.card l.kernel = 5 := by
      obtain ⟨e⟩ := h5.kernel_equiv
      exact (Nat.card_congr e.toEquiv).trans (by simp)
    exact ⟨5,2,Or.inr ⟨rfl,rfl⟩,⟨hc,by simpa using dimension_of_card (n := 4) h5.card_module,h5.ambient_equiv,h5.inverts⟩⟩
end CFSG.Quasithin.ChapterD.CyclicSource
