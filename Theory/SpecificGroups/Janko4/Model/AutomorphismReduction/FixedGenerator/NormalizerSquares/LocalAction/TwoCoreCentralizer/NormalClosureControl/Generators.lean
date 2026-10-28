module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Max2Bridge
public import Mathlib.Algebra.Group.Subgroup.Finite
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group

set_option maxRecDepth 10000

/-!
# The literal max2 normal-closure generators

The thirteen words are the distinguished central involution and twelve
conjugates of the order-four seed. Their squares follow from conjugacy.
Stability under the two local generators identifies their span with the
normal closure, using only generation inside `localSubgroup`. The faithful
representation undoes the certified conjugating element, so original max2
row witnesses can be reused without changing the relative group.

Source motivation: GLS3 Table 5.3i, printed p.270. The concrete words come
from ATLAS `J4G1-max2W1`, documented in `TwoCoreCentralizer.Words`.
Neither the global J₄ order nor a local model identification is assumed.
-/

@[expose] public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl

/-- The thirteen words in the saved max2 normal-closure witness, central word first. -/
def conjugates {G : Type*} [Group G] (x y u t : G) : Fin 13 → G :=
  let e1 := u
  let e2 := y⁻¹ * e1 * y
  let e3 := y⁻¹ * e2 * y
  let e4 := x⁻¹ * e3 * x
  let e5 := y⁻¹ * e4 * y
  let e6 := x⁻¹ * e5 * x
  let e7 := y⁻¹ * e5 * y
  let e8 := y⁻¹ * e6 * y
  let e9 := x⁻¹ * e7 * x
  let e10 := x⁻¹ * e8 * x
  let e11 := y⁻¹ * e8 * y
  let e12 := y⁻¹ * e9 * y
  ![t, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12]

def basis : Fin 13 → localSubgroup :=
  conjugates subgroupX subgroupY localSeed subgroupInvolution

def span : Subgroup localSubgroup := Subgroup.closure (Set.range basis)

lemma conjugates_mem {G : Type*} [Group G] (x y u t : G)
    (K : Subgroup G) [hK : K.Normal] (hu : u ∈ K) (ht : t ∈ K)
    (i : Fin 13) : conjugates x y u t i ∈ K := by
  have step (g z : G) (hz : z ∈ K) := hK.conj_mem' z hz g
  fin_cases i <;> dsimp only [conjugates, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact ht
  all_goals repeat first | exact hu | apply step

lemma conjugates_square {G : Type*} [Group G] (x y u t : G)
    (ht : t ∈ Subgroup.center G) (ht2 : t ^ 2 = 1) (hu : u ^ 2 = t)
    (i : Fin 13) : conjugates x y u t i ^ 2 = 1 ∨ conjugates x y u t i ^ 2 = t := by
  have step (g z : G) (hz : z ^ 2 = t) : (g⁻¹ * z * g) ^ 2 = t := by
    have htg := (Subgroup.mem_center_iff.mp ht) g
    calc
      (g⁻¹ * z * g) ^ 2 = g⁻¹ * z ^ 2 * g := by simp only [pow_two]; group
      _ = g⁻¹ * t * g := by rw [hz]
      _ = t := by rw [mul_assoc, ← htg, inv_mul_cancel_left]
  fin_cases i <;> dsimp only [conjugates, Matrix.cons_val_zero, Matrix.cons_val_succ]
  · exact Or.inl ht2
  all_goals apply Or.inr
  all_goals repeat first | exact hu | apply step

lemma basis_mem_normalClosure (i : Fin 13) : basis i ∈ localNormalClosure :=
  conjugates_mem _ _ _ _ _ localSeed_mem_normalClosure
    subgroupInvolution_mem_normalClosure i

lemma span_le_normalClosure : span ≤ localNormalClosure := by
  apply (Subgroup.closure_le _).mpr
  rintro z ⟨i, rfl⟩
  exact basis_mem_normalClosure i

lemma involution_mem_center : subgroupInvolution ∈ Subgroup.center localSubgroup := by
  rw [Subgroup.mem_center_iff]
  intro z
  apply Subtype.ext
  exact (Subgroup.mem_center_iff.mp centralInvolution_mem_center) z

lemma involution_pow_two : subgroupInvolution ^ 2 = 1 := by
  apply Subtype.ext
  exact centralInvolution_pow_two

lemma basis_square (i : Fin 13) : basis i ^ 2 = 1 ∨ basis i ^ 2 = subgroupInvolution :=
  conjugates_square _ _ _ _ involution_mem_center involution_pow_two localSeed_sq i

lemma local_generators_generate : Subgroup.closure {subgroupX, subgroupY} = ⊤ := by
  have hset : localSubgroup.subtype ⁻¹' ({localX, localY} : Set involutionCentralizer) =
      {subgroupX, subgroupY} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff]
    change (g.val = subgroupX.val ∨ g.val = subgroupY.val) ↔ _
    simp only [Subtype.val_inj]
  rw [← hset]
  exact Subgroup.closure_preimage_eq_top {localX, localY}

lemma closure_normal {G : Type*} [Group G] [Finite G] {ι : Type*}
    (x y : G) (e : ι → G) (hgen : Subgroup.closure {x, y} = ⊤)
    (hx : ∀ i, x⁻¹ * e i * x ∈ Subgroup.closure (Set.range e))
    (hy : ∀ i, y⁻¹ * e i * y ∈ Subgroup.closure (Set.range e)) :
    (Subgroup.closure (Set.range e)).Normal := by
  let K := Subgroup.closure (Set.range e)
  have normalizes (g : G) (hg : ∀ i, g⁻¹ * e i * g ∈ K) :
      g ∈ Subgroup.normalizer (K : Set G) := by
    have hm : K ≤ K.comap (MulAut.conj g⁻¹).toMonoidHom := by
      apply (Subgroup.closure_le _).mpr
      rintro z ⟨i, rfl⟩
      simpa using hg i
    have hi : g⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mem_normalizer_fintype (fun z hz => hm hz)
    simpa using (Subgroup.normalizer (K : Set G)).inv_mem hi
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hgen]
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with rfl | hg
  · exact normalizes _ hx
  · rw [Set.mem_singleton_iff] at hg
    subst g
    exact normalizes _ hy

lemma span_eq_normalClosure
    (hx : ∀ i, subgroupX⁻¹ * basis i * subgroupX ∈ span)
    (hy : ∀ i, subgroupY⁻¹ * basis i * subgroupY ∈ span) :
    span = localNormalClosure := by
  let : span.Normal := closure_normal _ _ _ local_generators_generate hx hy
  apply le_antisymm span_le_normalClosure
  apply Subgroup.normalClosure_le_normal (N := span)
  rw [Set.singleton_subset_iff]
  exact Subgroup.subset_closure ⟨1, rfl⟩

/-- Inclusion into the literal matrix model, followed by undoing the certified bridge. -/
def unconjugate : localSubgroup →* Model :=
  (MulAut.conj h).toMonoidHom.comp
    ((Subgroup.inclusion involutionCentralizer_le_matrixGroup).comp localSubgroup.subtype)

lemma unconjugate_injective : Function.Injective unconjugate :=
  (MulAut.conj h).injective.comp
    ((Subgroup.inclusion_injective involutionCentralizer_le_matrixGroup).comp
      Subtype.val_injective)

lemma unconjugate_x : unconjugate subgroupX = w10 := by
  change h * (h⁻¹ * w10 * h) * h⁻¹ = w10
  group

lemma unconjugate_y : unconjugate subgroupY = w14 := by
  change h * (h⁻¹ * w14 * h) * h⁻¹ = w14
  group

lemma unconjugate_seed : unconjugate localSeed = xyxyy ^ 11 := by
  simp only [localSeed, map_pow, map_mul, unconjugate_x, unconjugate_y]
  rfl

lemma unconjugate_involution : unconjugate subgroupInvolution = t := by
  change h * a * h⁻¹ = t
  rw [← conjugates_t]
  group

/-- Faithful representation with the original max2 outputs as generator matrices. -/
def representation : localSubgroup →* BinaryMatrix := toMatrix.comp unconjugate

lemma representation_injective : Function.Injective representation :=
  toMatrix_injective.comp unconjugate_injective

lemma representation_x : representation subgroupX = decodeRows w10Rows := by
  change toMatrix (unconjugate subgroupX) = _
  rw [unconjugate_x, eval_w10]

lemma representation_y : representation subgroupY = decodeRows w14Rows := by
  change toMatrix (unconjugate subgroupY) = _
  rw [unconjugate_y, eval_w14]

lemma representation_seed : representation localSeed = decodeRows tp11Rows := by
  change toMatrix (unconjugate localSeed) = _
  rw [unconjugate_seed, eval_tp11]

lemma representation_involution : representation subgroupInvolution = decodeRows tRows := by
  change toMatrix (unconjugate subgroupInvolution) = _
  rw [unconjugate_involution, eval_t]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.NormalClosureControl
