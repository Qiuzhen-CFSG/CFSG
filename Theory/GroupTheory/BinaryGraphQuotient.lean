module

public import Theory.GroupTheory.PGroup.GeneratorSeries
public import Theory.GroupTheory.TwoCosetExtension

/-!
# Quotient maps from binary graph collection

Attach proposed quotient coordinates to a normalizing binary generating
sequence. If their graph generators satisfy the same square and conjugation
containments, repeated two-coset extensions bound the graph subgroup by 2^n.
When the original n generators generate a group of order at least 2^n, the
first projection is bijective. Its inverse followed by the second projection
is the actual homomorphism with the prescribed generator images.

Only the stated collection containments are used. In particular a list of
coordinates is not assumed to define a quotient, and no multiplication table
or abstract presentation identification is required.
-/

open Subgroup
namespace Theory.GroupTheory.BinaryGraph

private theorem card_closure_le {G : Type*} [Group G] [Finite G]
    {n : ℕ} (g : Fin n → G)
    (hs : ∀ i, g i ^ 2 ∈ generatorPrefix g i.val)
    (hn : ∀ i, g i ∈ normalizer (generatorPrefix g i.val : Set G)) :
    Nat.card (closure (Set.range g)) ≤ 2 ^ n := by
  have hp : ∀ k ≤ n, Nat.card (generatorPrefix g k) ≤ 2 ^ k := by
    intro k hk
    induction k with
    | zero => simp [generatorPrefix]
    | succ k ih =>
      let i : Fin n := ⟨k, by omega⟩
      let K := generatorPrefix g k
      have hsq : g i * g i ∈ K := by simpa only [pow_two] using hs i
      have hc : ∀ x ∈ K, (g i)⁻¹ * x * g i ∈ K :=
        fun x hx => (mem_normalizer_iff''.mp (hn i) x).mp hx
      let E := twoCosetExtension K (g i) hsq hc
      have hle : generatorPrefix g (k + 1) ≤ E := by
        apply (generatorPrefix_le _ _ _).mpr
        intro j hj
        by_cases hlt : j.val < k
        · exact Or.inl ((generatorPrefix_le g k K).mp le_rfl j hlt)
        · have he : j = i := Fin.ext (by dsimp [i]; omega)
          subst j
          exact Or.inr ⟨1, K.one_mem, (mul_one (g i)).symm⟩
      calc
        Nat.card (generatorPrefix g (k + 1)) ≤ Nat.card E :=
          Nat.card_le_card_of_injective (Subgroup.inclusion hle)
            (Subgroup.inclusion_injective hle)
        _ ≤ 2 * Nat.card K := twoCosetExtension_card K (g i) hsq hc
        _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 (ih (by omega))
        _ = 2 ^ (k + 1) := by rw [pow_succ, Nat.mul_comm]
  have he : generatorPrefix g n = closure (Set.range g) := by
    unfold generatorPrefix
    congr 1
    ext x
    exact ⟨fun ⟨j, _, h⟩ => ⟨j, h⟩, fun ⟨j, h⟩ => ⟨j, j.isLt, h⟩⟩
  simpa only [he] using hp n le_rfl

/-- Compatible binary collection on graph generators constructs an actual
homomorphism; the order bound proves that no graph kernel remains. -/
public theorem exists_hom_of_graph_collection
    {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q] {n : ℕ}
    (g : Fin n → G) (c : Fin n → Q)
    (hg : closure (Set.range g) = ⊤) (hcard : 2 ^ n ≤ Nat.card G)
    (hs : ∀ i, (g i, c i) ^ 2 ∈ generatorPrefix (fun j => (g j, c j)) i.val)
    (hn : ∀ i, (g i, c i) ∈ normalizer
      (generatorPrefix (fun j => (g j, c j)) i.val : Set (G × Q))) :
    ∃ f : G →* Q, ∀ i, f (g i) = c i := by
  let H := closure (Set.range (fun j => (g j, c j)))
  let π : H →* G := (MonoidHom.fst G Q).comp H.subtype
  have hgen : closure (Set.range g) ≤ π.range := by
    apply (closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨(g i, c i), subset_closure ⟨i, rfl⟩⟩, rfl⟩
  have hsurj : Function.Surjective π := MonoidHom.range_eq_top.mp
    (top_unique (hg ▸ hgen))
  have hbij := hsurj.bijective_of_nat_card_le ((card_closure_le _ hs hn).trans hcard)
  let e : H ≃* G := MulEquiv.ofBijective π hbij
  let f : G →* Q := ((MonoidHom.snd G Q).comp H.subtype).comp e.symm.toMonoidHom
  refine ⟨f, ?_⟩
  intro i
  have he : e ⟨(g i, c i), subset_closure ⟨i, rfl⟩⟩ = g i := rfl
  have hi := congrArg e.symm he
  rw [e.symm_apply_apply] at hi
  change (e.symm (g i)).val.2 = c i
  rw [← hi]

end Theory.GroupTheory.BinaryGraph
