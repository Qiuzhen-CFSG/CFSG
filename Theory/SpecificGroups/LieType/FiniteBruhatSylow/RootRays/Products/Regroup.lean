module

public import Theory.GroupTheory.FixedOrderedProduct
public import Theory.AlgebraicGroup.Borel.RootStructure.FundamentalCorootData

/-!
# Regrouping unique ordered coordinates

A finite partition of a coordinate set can be grouped into blocks without
losing uniqueness, provided every block is the product of its coordinates in
any order. Concatenating the chosen internal orders proves both coverage and
injectivity. The groups, and the resulting blocks, need not be abelian.

This is the grouping argument from GLS3 1.12.7(a),(c) to 2.3.7. Its application
to the actual algebraic root subgroups is in the parent `Products` module.
-/

namespace Theory.AlgebraicGroup.FiniteBruhatSylow

private theorem glue_disjoint_functions {A G I : Type*} [One G]
    (s : I → Set A) (hd : Pairwise (fun i j => Disjoint (s i) (s j)))
    (f : I → A → G) : ∃ g : A → G, ∀ i a, a ∈ s i → g a = f i a := by
  classical
  let g : A → G := fun a => if h : ∃ i, a ∈ s i then f h.choose a else 1
  refine ⟨g, ?_⟩
  intro i a ha
  have h : ∃ i, a ∈ s i := ⟨i, ha⟩
  have heq : h.choose = i := by
    by_contra hne
    exact Set.disjoint_left.mp (hd hne) h.choose_spec ha
  simp only [g, dif_pos h, heq]

/-- Unique ordered coordinates regroup along a finite partition. The two
conclusions are exactly injectivity and coverage of the subgroup product. -/
public theorem orderedProduct_regroup_partition
    {A G : Type*} [Finite A] [Group G] {m : ℕ}
    (X : A → Subgroup G) (Y : Fin m → Subgroup G) (U : Subgroup G)
    (s : Set A) (fiber : Fin m → Set A)
    (hd : Pairwise (fun i j => Disjoint (fiber i) (fiber j)))
    (hc : ∀ a, a ∈ s ↔ ∃ i, a ∈ fiber i)
    (hunique : ∀ order, EnumeratesRootSet s order →
      ∀ f g : A → G, (∀ a ∈ s, f a ∈ X a) → (∀ a ∈ s, g a ∈ X a) →
        (order.map f).prod = (order.map g).prod → ∀ a ∈ s, f a = g a)
    (hfull : ∀ order, EnumeratesRootSet s order → ∀ x ∈ U,
      ∃ f : A → G, (∀ a ∈ s, f a ∈ X a) ∧ (order.map f).prod = x)
    (hblock : ∀ i order, EnumeratesRootSet (fiber i) order → ∀ x,
      x ∈ Y i ↔ ∃ f : A → G,
        (∀ a ∈ fiber i, f a ∈ X a) ∧ (order.map f).prod = x) :
    Function.Injective (Subgroup.orderedProduct Y) ∧
      ∀ x ∈ U, ∃ b : ∀ i, Y i, Subgroup.orderedProduct Y b = x := by
  classical
  let := Fintype.ofFinite A
  have hex : ∀ i, ∃ order, EnumeratesRootSet (fiber i) order :=
    fun i => exists_enumeratesRootSet (fiber i)
  choose order ho using hex
  let total := (List.ofFn order).flatten
  have hmem : ∀ a, a ∈ total ↔ a ∈ s := by
    intro a
    simp only [total, List.mem_flatten, List.mem_ofFn]
    constructor
    · rintro ⟨l, ⟨i, rfl⟩, ha⟩
      exact (hc a).mpr ⟨i, (ho i).2 a |>.mp ha⟩
    · intro ha
      obtain ⟨i, hi⟩ := (hc a).mp ha
      exact ⟨order i, ⟨i, rfl⟩, (ho i).2 a |>.mpr hi⟩
  have ht : EnumeratesRootSet s total := by
    refine ⟨?_, hmem⟩
    apply List.nodup_flatten.mpr
    constructor
    · intro l hl
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
      exact (ho i).1
    · apply List.pairwise_ofFn.mpr
      intro i j hij
      apply List.disjoint_left.mpr
      intro a hai haj
      exact Set.disjoint_left.mp (hd (Fin.ne_of_lt hij))
        ((ho i).2 a |>.mp hai) ((ho j).2 a |>.mp haj)
  have hprod (f : A → G) :
      (total.map f).prod = (List.ofFn fun i => ((order i).map f).prod).prod := by
    simp only [total, List.map_flatten, List.prod_flatten, List.map_ofFn]
    rfl
  have hfiber : ∀ i, fiber i ⊆ s := fun i a ha => (hc a).mpr ⟨i, ha⟩
  constructor
  · intro b c heq
    have hb : ∀ i, ∃ f : A → G,
        (∀ a ∈ fiber i, f a ∈ X a) ∧ ((order i).map f).prod = (b i : G) :=
      fun i => (hblock i _ (ho i) _).mp (b i).property
    have hc' : ∀ i, ∃ f : A → G,
        (∀ a ∈ fiber i, f a ∈ X a) ∧ ((order i).map f).prod = (c i : G) :=
      fun i => (hblock i _ (ho i) _).mp (c i).property
    choose fb hfb hpb using hb
    choose fc hfc hpc using hc'
    obtain ⟨f, hf⟩ := glue_disjoint_functions fiber hd fb
    obtain ⟨g, hg⟩ := glue_disjoint_functions fiber hd fc
    have hpf : ∀ i, ((order i).map f).prod = (b i : G) := by
      intro i
      rw [← hpb i]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact hf i a ((ho i).2 a |>.mp ha)
    have hpg : ∀ i, ((order i).map g).prod = (c i : G) := by
      intro i
      rw [← hpc i]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact hg i a ((ho i).2 a |>.mp ha)
    have hfg : ∀ a ∈ s, f a = g a := by
      apply hunique total ht f g
      · intro a ha
        obtain ⟨i, hi⟩ := (hc a).mp ha
        rw [hf i a hi]
        exact hfb i a hi
      · intro a ha
        obtain ⟨i, hi⟩ := (hc a).mp ha
        rw [hg i a hi]
        exact hfc i a hi
      · simpa only [hprod, hpf, hpg, Subgroup.orderedProduct] using heq
    funext i
    apply Subtype.ext
    rw [← hpf i, ← hpg i]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact hfg a (hfiber i ((ho i).2 a |>.mp ha))
  · intro x hx
    obtain ⟨f, hf, hfx⟩ := hfull total ht x hx
    let b : ∀ i, Y i := fun i => ⟨((order i).map f).prod,
      (hblock i _ (ho i) _).mpr ⟨f, fun a ha => hf a (hfiber i ha), rfl⟩⟩
    exact ⟨b, (hprod f).symm.trans hfx⟩

end Theory.AlgebraicGroup.FiniteBruhatSylow
