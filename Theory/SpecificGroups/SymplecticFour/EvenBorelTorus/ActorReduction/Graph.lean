module
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction.Action
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph

/-!
# Graph powers and the inner kernel of the Borel torus action

The exceptional graph class generates the actual outer group under the explicit
classification of diagram-preserving automorphisms. An actor normalizing the
standard Sylow therefore factors as Borel conjugation times a graph power.
Borel conjugations act trivially on the torus. The graph-generated torus action
is faithful on graph powers: even powers are detected on field units, and an
odd power cannot fix both coordinates when the field has more than two elements.
Consequently the kernel on the full Sylow stabilizer consists exactly of inner
actors. No restriction to involutions is made.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954; GLS3,
Theorem 2.5.12(e), as proved for the explicit exceptional map in the imports.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction
open DiagramAutomorphisms DiagramAutomorphisms.ExceptionalGraph
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

def graphActor : stabilizer (F := F) := ⟨graphAut, graph_map_unipotent⟩

theorem torusAction_graph {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    torusAction hF graphActor = graphTorus := by
  apply MulEquiv.ext
  intro x
  obtain ⟨b, rfl⟩ := characters_surjective x
  rw [torusAction_characters]
  exact characters_graph b

def innerActor (g : borel (F := F)) : stabilizer (F := F) :=
  ⟨MulAut.conj g.val, mem_normalizer_iff_map_conj_eq.mp
    (borel_eq_normalizer_unipotent (F := F) ▸ g.property)⟩

omit [CharP F 2] in
theorem torusAction_inner {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (g : borel (F := F)) : torusAction hF (innerActor g) = 1 := by
  apply MulEquiv.ext
  intro x
  obtain ⟨b, rfl⟩ := characters_surjective x
  rw [torusAction_characters]
  change borelCharacters (g * b * g⁻¹) = borelCharacters b
  simp

/-- Normalizing the fixed Sylow forces the inner factor into its actual Borel. -/
theorem exists_inner_graph_power (hF : 2 < Nat.card F)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (a : stabilizer (F := F)) :
    ∃ g : borel (F := F), ∃ k : ℕ, a = innerActor g * graphActor ^ k := by
  let π : MulAut (Sp F) →* MulAut.Outer (Sp F) := QuotientGroup.mk' _
  have hm : π a.val ∈ zpowers (π (graphAut (F := F))) := by
    rw [outerGraph_zpowers_eq_top hF hclass]
    trivial
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hm)
  have hi : a.val / graphAut ^ k ∈ MulAut.innerSubgroup (Sp F) := by
    apply QuotientGroup.eq_iff_div_mem.mp
    change π a.val = π (graphAut ^ k)
    rw [map_pow, hk]
  obtain ⟨g, hg⟩ := hi
  have he : a.val = MulAut.conj g * graphAut ^ k := (eq_div_iff_mul_eq'.mp hg).symm
  have hgi : MulAut.conj g ∈ stabilizer (F := F) := by
    rw [hg]
    exact stabilizer.div_mem a.property (stabilizer.pow_mem graphActor.property k)
  have hgb : g ∈ borel (F := F) := by
    rw [borel_eq_normalizer_unipotent]
    exact mem_normalizer_iff_map_conj_eq.mpr hgi
  exact ⟨⟨g, hgb⟩, k, Subtype.ext he⟩

/-- Every actual stabilizing actor induces a power of the exceptional torus map. -/
theorem torusAction_mem_graph {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (a : stabilizer (F := F)) : torusAction hF a ∈ zpowers (graphTorus (F := F)) := by
  have hc : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hn
  obtain ⟨g, k, rfl⟩ := exists_inner_graph_power hc hclass a
  rw [map_mul, map_pow, torusAction_inner, torusAction_graph, one_mul]
  exact npow_mem_zpowers _ _

private def fieldTorusHom : (F ≃+* F) →* MulAut (Fˣ × Fˣ) where
  toFun := fieldTorus
  map_one' := by ext x <;> rfl
  map_mul' σ τ := by ext x <;> rfl

omit [Finite F] [CharP F 2] in
private theorem fieldTorus_eq_one {σ : F ≃+* F} (hσ : fieldTorus σ = 1) : σ = 1 := by
  apply RingEquiv.ext
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · let u : Fˣ := Units.mk0 x hx
    have he := congrArg (fun t : Fˣ × Fˣ => (t.1 : F)) (DFunLike.congr_fun hσ (u, 1))
    exact he

private theorem graph_power_eq_one_of_torus {k : ℕ} (hF : 2 < Nat.card F)
    (hk : graphTorus (F := F) ^ k = 1) : graphAut (F := F) ^ k = 1 := by
  rcases Nat.even_or_odd k with he | ho
  · obtain ⟨m, rfl⟩ := even_iff_two_dvd.mp he
    rw [pow_mul, graphTorus_square] at hk
    have hf : fieldTorus (frobeniusEquiv F 2 ^ m) = 1 := by
      change fieldTorusHom (frobeniusEquiv F 2 ^ m) = 1
      rw [map_pow]
      exact hk
    rw [pow_mul, graphAut_square]
    change fieldAutomorphismHom (frobeniusEquiv F 2) ^ m = 1
    rw [← map_pow, fieldTorus_eq_one hf, map_one]
  · obtain ⟨m, rfl⟩ := ho
    have hu : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
    let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hu
    obtain ⟨u, hu⟩ := exists_ne (1 : Fˣ)
    rw [pow_add, pow_mul, graphTorus_square, pow_one] at hk
    have hf : fieldTorus (frobeniusEquiv F 2 ^ m) * graphTorus = 1 := by
      change fieldTorusHom (frobeniusEquiv F 2 ^ m) * graphTorus = 1
      rw [map_pow]
      exact hk
    have he := congrArg Prod.fst (DFunLike.congr_fun hf (u, 1))
    change (fieldTorus (frobeniusEquiv F 2 ^ m) (graphTorus (u, 1))).1 = u at he
    rw [graphTorus_apply, fieldTorus_apply] at he
    simp only [map_one] at he
    exact (hu he.symm).elim

/-- The torus action detects exactly the inner actors in the Sylow stabilizer. -/
theorem torusAction_eq_one_iff_inner {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ g : Sp F, ∃ σ : F ≃+* F, a = MulAut.conj g * fieldAutomorphism σ)
    (a : stabilizer (F := F)) :
    torusAction hF a = 1 ↔ a.val ∈ MulAut.innerSubgroup (Sp F) := by
  constructor
  · intro ha
    have hc : 2 < Nat.card F := by
      rw [hF]
      exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hn
    obtain ⟨g, k, he⟩ := exists_inner_graph_power hc hclass a
    rw [he, map_mul, map_pow, torusAction_inner, torusAction_graph, one_mul] at ha
    have hg := graph_power_eq_one_of_torus hc ha
    have he' := congrArg Subtype.val he
    change a.val = MulAut.conj g.val * graphAut ^ k at he'
    rw [hg, mul_one] at he'
    exact ⟨g.val, he'.symm⟩
  · rintro ⟨g, hg⟩
    have hgb : g ∈ borel (F := F) := by
      rw [borel_eq_normalizer_unipotent]
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [hg]
      exact a.property
    have he : a = innerActor ⟨g, hgb⟩ := Subtype.ext hg.symm
    rw [he, torusAction_inner]

end Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.ActorReduction
