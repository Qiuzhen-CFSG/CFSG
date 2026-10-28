module
public import Theory.Alternating.IndexEightSubgroups
public import Theory.SpecificGroups.AlternatingSix.SmallIndex
public import Theory.LinearAlgebra.BinaryFourAlternatingEight
/-!
# Controlling the normalizer of an order-120 exceptional actor

Under GL₄(2) ≃ A₈, a faithful A₇ image is a point stabilizer. An order-120
subgroup of that image fixes only that point: fixing a second would embed it
with index three in the simple A₆. Its normalizer therefore preserves the same
point and belongs to the same A₇. All embeddings and linear coordinates are
retained. The native heptad application controls changes of coordinates on
its original sixteen-core in Aschbacher--Smith 5.2.20(5), pp.656--657.
The GL₄(2) ≃ A₈ comparison retains its ATLAS attribution in the imported module.
-/

public noncomputable section
open Subgroup MulAction
namespace Theory.GroupTheory.QuasithinM23

private theorem order120_fixed_unique
    (S : Subgroup (alternatingGroup (Fin 8))) (hS : Nat.card S = 120)
    (i j : Fin 8) (hi : ∀ s : S, s.val.val i = i)
    (hj : ∀ s : S, s.val.val j = j) : i = j := by
  classical
  by_contra hij
  let t : Finset (Fin 8) := {i,j}
  let K := fixingSubgroup (alternatingGroup (Fin 8)) (t : Set (Fin 8))
  have hc : Fintype.card (↑tᶜ) = 6 := by
    rw [Fintype.card_coe,Finset.card_compl]
    change 8 - ({i,j} : Finset (Fin 8)).card = 6
    rw [Finset.card_pair hij]
  let e : K ≃* alternatingGroup (Fin 6) :=
    (Atlas.Families.Alternating.stabilizerComplementEquiv t).trans
      (Atlas.Families.Alternating.relabel (Fintype.equivFinOfCardEq hc))
  have hSK : S ≤ K := by
    intro s hs x
    have hx : x.val = i ∨ x.val = j := by simpa [t] using x.property
    rcases hx with hx | hx
    · change s.val x.val = x.val
      rw [hx]; exact hi ⟨s,hs⟩
    · change s.val x.val = x.val
      rw [hx]; exact hj ⟨s,hs⟩
  let R := S.subgroupOf K
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup K := e.isSimpleGroup
  have hK : Nat.card K = 360 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hR : Nat.card R = 120 := (Nat.card_congr (subgroupOfEquivOfLe hSK).toEquiv).trans hS
  have hiR : R.index = 3 := by
    have hh := R.card_mul_index
    rw [hR,hK] at hh
    omega
  have ht : R = ⊤ := Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt R (by
    rw [hiR,hK]; decide)
  rw [ht,card_top,hK] at hR
  contradiction

/-- The normalizer of an order-120 subgroup of an index-eight A₇ stays in
that same A₇: the subgroup has exactly one fixed letter in the eight-letter action. -/
theorem order120_normalizer_le_indexEight
    (S N : Subgroup (alternatingGroup (Fin 8))) (hSN : S ≤ N)
    (hS : Nat.card S = 120) (hN : N.index = 8) :
    normalizer (S : Set (alternatingGroup (Fin 8))) ≤ N := by
  obtain ⟨i,hi⟩ := GroupTheory.AlternatingIndexEight.index_eight_fixed N hN
  have hfix (s : S) : s.val.val i = i := (hi s.val).mp (hSN s.property)
  intro g hg
  apply (hi g).mpr
  symm
  apply order120_fixed_unique S hS i (g.val i) hfix
  intro s
  have hs := (mem_normalizer_iff''.mp hg s.val).mp s.property
  have hh := hfix ⟨g⁻¹*s.val*g,hs⟩
  change g.val.symm (s.val.val (g.val i)) = i at hh
  exact (g.val.symm_apply_eq.mp hh)

/-- An order-120 subgroup of a faithful binary four-dimensional A₇ image
has all its linear normalizers inside that same A₇ image. -/
theorem order120_linear_normalizer_le_exceptional
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : alternatingGroup (Fin 7) →* (V ≃ₗ[ZMod 2] V)) (hρ : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V = 4)
    (S : Subgroup (V ≃ₗ[ZMod 2] V)) (hSρ : S ≤ ρ.range) (hS : Nat.card S = 120) :
    normalizer (S : Set (V ≃ₗ[ZMod 2] V)) ≤ ρ.range := by
  let E := BinaryFourAlternatingEight.linearEquivAlternatingEight hd
  have hcard : Nat.card (ρ.range.map E.toMonoidHom) = 2520 := by
    rw [card_map_of_injective E.injective,
      ←Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hindex : (ρ.range.map E.toMonoidHom).index = 8 := by
    have hh := (ρ.range.map E.toMonoidHom).card_mul_index
    rw [hcard,nat_card_alternatingGroup] at hh
    norm_num only [Nat.card_fin, Nat.factorial] at hh
    omega
  have hle := order120_normalizer_le_indexEight (S.map E.toMonoidHom)
    (ρ.range.map E.toMonoidHom) (map_mono hSρ)
    ((card_map_of_injective E.injective).trans hS) hindex
  rw [←map_equiv_normalizer_eq] at hle
  exact (map_le_map_iff_of_injective E.injective).mp hle
end Theory.GroupTheory.QuasithinM23
