module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph.Contracts

/-!
# Three graph conjugates generate the binary SL₅ image

Put `u = x₀₁(1)` and `g = x₃₄(1)x₂₃(1)x₁₂(1)x₀₁(1)`.
For inverse transpose γ, the two products `u γ(u)⁻¹` and `g γ(g)⁻¹`
generate SL₅(2). The finite words below recover every elementary transvection;
each matrix equality is checked by kernel reduction. Elementary matrix
induction then proves generation without enumerating the whole group.

For an operator t implementing γ, both products are images of a conjugate of t
multiplied by t⁻¹. Thus t and its conjugates by σ(u), σ(g) generate a subgroup
containing the entire marked image. `Higher` uses this to bound the module
by three cyclic fixed codimensions.

This supplies an alternative dimension-to-displacement step for
Guralnick–Malle, *Classification of 2F-modules II*, Proposition 4.8(3B),
author manuscript pp.27–28, and Aschbacher–Smith K.3.2, printed pp.454–455.
The generation assertion is proved here, rather than assumed from that source.
-/

public section

open Representation.SL5TenDimensional Representation.SL5TenDimensional.Classification
open BinaryLinear.OuterCyclic

private def a : Group := simpleUpper 0 * simpleLower 0

private def chain : Group := simpleUpper 3 * simpleUpper 2 * simpleUpper 1 * simpleUpper 0

private def b : Group := chain * simpleLower 0 * simpleLower 1 * simpleLower 2 * simpleLower 3

private def bi : Group := simpleLower 3 * simpleLower 2 * simpleLower 1 * simpleLower 0 *
  simpleUpper 0 * simpleUpper 1 * simpleUpper 2 * simpleUpper 3

private def letter : Fin 4 → Group := ![a, a * a, b, bi]

private def word (l : List (Fin 4)) : Group := (l.map letter).prod

private def elementary (i j : Fin 5) : Group :=
  if h : i = j then 1 else Matrix.SpecialLinearGroup.transvection h (1 : ZMod 2)

private def rootWord (i j : Fin 5) : List (Fin 4) :=
  (![
    ![
      [],
      [2, 0, 3, 0, 2, 0, 3, 1, 2, 0, 3, 0, 2, 1, 3, 0, 2, 0, 3],
      [3, 0, 2, 0, 3, 1, 2, 0, 3, 0, 2],
      [3, 1, 3, 1, 2, 1, 3, 1, 2, 2],
      [0, 2, 0, 2, 2, 0, 2, 2, 2, 1, 3, 1, 3, 1, 3, 3, 1, 3, 3]],
    ![
      [3, 0, 2, 0, 3, 1, 2, 0, 3, 0, 2, 1, 3, 0, 2, 0, 3, 0, 2],
      [],
      [0, 3, 0, 2, 0, 3, 1, 2, 0, 3, 0, 2, 1],
      [0, 3, 1, 3, 1, 2, 1, 3, 1, 2, 2, 1],
      [2, 0, 2, 1, 3, 1, 3, 0, 2, 0, 3, 0, 2, 2, 1, 3, 3]],
    ![
      [2, 0, 3, 0, 2, 1, 3, 0, 2, 0, 3],
      [1, 2, 0, 3, 0, 2, 1, 3, 0, 2, 0, 3, 0],
      [],
      [2, 0, 3, 3, 1, 3, 1, 2, 1, 3, 1, 2, 2, 2, 1, 3],
      [0, 2, 0, 3, 3, 3, 0, 3, 3, 1, 3, 1, 2, 1, 2, 2, 1, 2, 2]],
    ![
      [2, 0, 2, 0, 3, 0, 2, 0, 3, 3],
      [1, 2, 0, 2, 0, 3, 0, 2, 0, 3, 3, 0],
      [3, 1, 2, 2, 0, 2, 0, 3, 0, 2, 0, 3, 3, 3, 0, 2],
      [],
      [2, 2, 2, 0, 2, 1, 3, 0, 2, 1, 3, 3, 3, 3]],
    ![
      [0, 3, 0, 2, 1, 3, 0, 3, 1, 2, 2, 0, 3, 0, 3, 0, 2, 2, 1],
      [3, 0, 2, 1, 3, 0, 3, 1, 2, 2, 0, 3, 0, 3, 0, 2, 2],
      [0, 2, 2, 1, 2, 2, 1, 2, 1, 3, 1, 3, 3, 0, 3, 3, 3, 0, 2],
      [3, 3, 3, 1, 3, 0, 2, 1, 3, 0, 2, 2, 2, 2],
      []]
  ] : Fin 5 → Fin 5 → List (Fin 4)) i j

private theorem word_root (i j : Fin 5) : word (rootWord i j) = elementary i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel

private theorem letter_one : letter 1 = (letter 0)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  decide +kernel

private theorem letter_three : letter 3 = (letter 2)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  decide +kernel

private theorem first_eq : letter 0 = simpleUpper 0 * (graphSL 5 (simpleUpper 0))⁻¹ := by
  change letter 0 = simpleUpper 0 * ((Matrix.SpecialLinearGroup.transpose (simpleUpper 0))⁻¹)⁻¹
  rw [inv_inv]
  decide +kernel

private theorem second_eq : letter 2 = chain * (graphSL 5 chain)⁻¹ := by
  change letter 2 = chain * ((Matrix.SpecialLinearGroup.transpose chain)⁻¹)⁻¹
  rw [inv_inv]
  decide +kernel

private theorem pair_generates (K : Subgroup Group)
    (ha : letter 0 ∈ K) (hb : letter 2 ∈ K) (g : Group) : g ∈ K := by
  have hl (i : Fin 4) : letter i ∈ K := by
    fin_cases i
    · exact ha
    · change letter 1 ∈ K
      rw [letter_one]; exact K.inv_mem ha
    · exact hb
    · change letter 3 ∈ K
      rw [letter_three]; exact K.inv_mem hb
  have hw (l : List (Fin 4)) : word l ∈ K := by
    induction l with
    | nil => exact K.one_mem
    | cons i l ih => exact K.mul_mem (hl i) ih
  have hr (i j : Fin 5) : elementary i j ∈ K := by
    rw [← word_root]
    exact hw _
  apply Matrix.SpecialLinearGroup.diagonal_transvection_induction' (fun g => g ∈ K) g
  · intro i j hij c hc
    have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc
    have hd : Matrix.SpecialLinearGroup.diag2n hij c hc = 1 := by
      apply Subtype.ext
      simp [Matrix.SpecialLinearGroup.diag2n_coe, hc1]
    rw [hd]
    exact K.one_mem
  · intro i j hij c
    have hc : c = 0 ∨ c = 1 := (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
    rcases hc with rfl | rfl
    · simpa only [Matrix.SpecialLinearGroup.transvection_coeff_zero] using K.one_mem
    · simpa only [elementary, dif_neg hij] using hr i j
  · intro a b ha hb
    exact K.mul_mem ha hb

open Subgroup Representation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) SL5TenDimensional.Group V)

/-- The literal image lies in the group generated by three conjugates of the graph operator. -/
theorem exists_three_graph_conjugates (t : linearNormalizer σ) (ht : IsStandardGraph σ t) :
    ∃ c : Fin 3 → (Module.End (ZMod 2) V)ˣ,
      actionImage σ ≤ Subgroup.closure (Set.range fun i => c i * t.val * (c i)⁻¹) := by
  let c : Fin 3 → (Module.End (ZMod 2) V)ˣ :=
    ![1, σ.asGroupHom (simpleUpper 0), σ.asGroupHom chain]
  let K : Subgroup (Module.End (ZMod 2) V)ˣ :=
    Subgroup.closure (Set.range fun i => c i * t.val * (c i)⁻¹)
  have htK : t.val ∈ K := by
    exact Subgroup.subset_closure ⟨0, by simp [c]⟩
  have hpair (g : SL5TenDimensional.Group) :
      σ.asGroupHom (g * (graphSL 5 g)⁻¹) =
        (σ.asGroupHom g * t.val * (σ.asGroupHom g)⁻¹) * t.val⁻¹ := by
    rw [map_mul, map_inv, ← ht.2 g]
    group
  have ha : letter 0 ∈ K.comap σ.asGroupHom := by
    change σ.asGroupHom (letter 0) ∈ K
    rw [first_eq, hpair]
    apply K.mul_mem _ (K.inv_mem htK)
    exact subset_closure ⟨1, rfl⟩
  have hb : letter 2 ∈ K.comap σ.asGroupHom := by
    change σ.asGroupHom (letter 2) ∈ K
    rw [second_eq, hpair]
    apply K.mul_mem _ (K.inv_mem htK)
    exact subset_closure ⟨2, rfl⟩
  refine ⟨c, ?_⟩
  rintro _ ⟨g, rfl⟩
  exact pair_generates (K.comap σ.asGroupHom) ha hb g

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Graph
