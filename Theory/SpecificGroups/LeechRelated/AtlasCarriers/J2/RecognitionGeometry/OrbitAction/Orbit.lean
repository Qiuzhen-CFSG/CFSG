module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.RecognitionGeometry.OrbitAction.Checks
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order

/-!
# The actual conjugate-subgroup orbit and its faithful action

The 280 word representatives form a generator coset cover for the literal
normalizer M. Their cyclic subgroups are distinct because their fixed-point
sets in the ATLAS permutation action differ. This proves exhaustive coverage
and index 280, so the independently checked order 604800 gives |M| = 2160.

The same fixed-point sets distinguish the 100 permutation points. An element
fixing every vertex preserves all these sets and hence every point, proving
faithfulness without a simplicity or recognition assumption.

Source: Aschbacher, *Sporadic Groups*, 47.3, 47.5 and 47.10, pp.261–267.
The concrete words and signed transitions are certified in `Checks`.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.RecognitionGeometry.OrbitAction
open Subgroup Theory.GroupTheory GeneratorPair FirstFusion Data

def rep (i : Fin 280) : Carrier := evalWord letter (words i)
def element (i : Fin 280) : Carrier := (rep i)⁻¹ * x * rep i
def vertex (i : Fin 280) : Vertex := (rep i)⁻¹ • base

theorem rep_zero : rep 0 = 1 := rfl

theorem row_spec (i : Fin 280) (p : Fin 100) :
    inclusion (element i) p = value i p := by
  have aux : ∀ (n : Nat) (j : Fin 280), j.val = n → ∀ q : Fin 100,
      inclusion (element j) q = value j q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj q
      by_cases hzero : j = 0
      · subst j
        simpa only [element, rep_zero, inv_one, one_mul, mul_one, inclusion_x] using
          (value_zero q).symm
      obtain ⟨hlt, hw, hn, hf⟩ := word_data j hzero
      have hp := ih (parent j).val (hj ▸ hlt) (parent j) rfl
      have hr : rep j = rep (parent j) * letter (parentLetter j) := by
        simp only [rep, hw, evalWord_append, evalWord, mul_one]
      have he : element j = (letter (parentLetter j))⁻¹ * element (parent j) *
          letter (parentLetter j) := by
        simp only [element, hr, mul_inv_rev, mul_assoc]
      rw [he, map_mul, map_mul, map_inv, inclusion_letter]
      change (permLetter (parentLetter j))⁻¹
        (inclusion (element (parent j)) (permLetter (parentLetter j) q)) = value j q
      rw [hp]
      have hs := value_step (parent j) (parentLetter j) q
      simpa only [hf, hn, signedValue, Bool.false_eq_true, ↓reduceIte] using hs.symm
  exact aux i.val i rfl p

theorem vertex_val (i : Fin 280) : (vertex i).val = zpowers (element i) := by
  rw [vertex, smul_val, show base.val = X from rfl, X, MonoidHom.map_zpowers]
  change zpowers ((rep i)⁻¹ * x * ((rep i)⁻¹)⁻¹) = _
  rw [inv_inv]
  rfl

theorem element_cube (i : Fin 280) : element i ^ 3 = 1 := by
  have h := map_pow (MulAut.conj (rep i)⁻¹) x 3
  simpa only [x_cube, map_one, MulAut.conj_apply, inv_inv, element] using h.symm

theorem element_square (i : Fin 280) : element i ^ 2 = (element i)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  simpa only [← pow_succ] using element_cube i

theorem conjugate_step (i : Fin 280) (s : Fin 3) :
    (letter s)⁻¹ * element i * letter s =
      if flip i s then (element (nextRow i s))⁻¹ else element (nextRow i s) := by
  apply inclusion_injective
  apply Equiv.ext
  intro p
  rw [map_mul, map_mul, map_inv, inclusion_letter]
  change (permLetter s)⁻¹ (inclusion (element i) (permLetter s p)) = _
  rw [row_spec, ← value_step]
  cases hf : flip i s
  · simp only [Bool.false_eq_true, ↓reduceIte, signedValue, row_spec]
  · simp only [↓reduceIte, ← element_square, pow_two, map_mul, Equiv.Perm.mul_apply,
      row_spec, signedValue]

theorem vertex_step (i : Fin 280) (s : Fin 3) :
    (letter s)⁻¹ • vertex i = vertex (nextRow i s) := by
  apply Subtype.ext
  rw [smul_val, vertex_val, MonoidHom.map_zpowers, vertex_val]
  change zpowers ((letter s)⁻¹ * element i * ((letter s)⁻¹)⁻¹) = _
  rw [inv_inv, conjugate_step]
  cases hf : flip i s <;> simp only [↓reduceIte, Bool.false_eq_true, zpowers_inv]

theorem step_mem (i : Fin 280) (s : Fin 3) :
    rep i * letter s * (rep (nextRow i s))⁻¹ ∈ M := by
  rw [← base_stabilizer, MulAction.mem_stabilizer_iff]
  have hs := congrArg (fun A : Vertex => (rep i * letter s) • A) (vertex_step i s)
  simpa only [vertex, mul_smul, smul_inv_smul] using hs.symm

def cosetCover : Subgroup.GeneratorCosetCover M letter (Fin 280) where
  repr := rep
  initial := 0
  initial_eq := rep_zero
  step i s := ⟨⟨_, step_mem i s⟩, nextRow i s, by simp [mul_assoc]⟩
  inv_step i s := by
    rw [← letter_inv]
    exact ⟨⟨_, step_mem i (invLetter s)⟩, nextRow i (invLetter s), by simp [mul_assoc]⟩

/-- A cyclic subgroup fixes precisely the points fixed by its generator. -/
theorem fixed_of_mem_zpowers {u v : Carrier} {p : Fin 100}
    (hu : inclusion u p = p) (hv : v ∈ zpowers u) : inclusion v p = p := by
  let S := (MulAction.stabilizer (Equiv.Perm (Fin 100)) p).comap inclusion
  have hs : zpowers u ≤ S := zpowers_le.mpr hu
  exact hs hv

theorem fixed_iff_of_zpowers_eq {u v : Carrier} (h : zpowers u = zpowers v)
    (p : Fin 100) : inclusion u p = p ↔ inclusion v p = p := by
  constructor
  · intro hu
    exact fixed_of_mem_zpowers hu (h.symm ▸ mem_zpowers v)
  · intro hv
    exact fixed_of_mem_zpowers hv (h ▸ mem_zpowers u)

theorem vertex_injective : Function.Injective vertex := by
  intro i j hij
  have hv : zpowers (element i) = zpowers (element j) := by
    rw [← vertex_val, ← vertex_val, hij]
  have hc : rowCode i = rowCode j := by
    unfold rowCode
    congr 1
    funext p
    have hf := fixed_iff_of_zpowers_eq hv p
    simp only [row_spec] at hf
    simp only [hf]
  have h := congrArg identifyRow hc
  simpa only [identifyRow_spec] using h

theorem vertex_surjective : Function.Surjective vertex := by
  intro A
  obtain ⟨g, hg⟩ := transitive A
  obtain ⟨m, i, hi⟩ := cosetCover.covers letter_generates g⁻¹
  change g⁻¹ = m.val * rep i at hi
  have hm : (m.val)⁻¹ • base = base := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [base_stabilizer]
    exact M.inv_mem m.property
  refine ⟨i, ?_⟩
  have hg' : g = (rep i)⁻¹ * m.val⁻¹ := by
    simpa only [inv_inv, mul_inv_rev] using congrArg Inv.inv hi
  rw [← hg, hg', mul_smul, hm]
  rfl

noncomputable def vertexEquiv : Fin 280 ≃ Vertex :=
  Equiv.ofBijective vertex ⟨vertex_injective, vertex_surjective⟩

theorem card_vertex : Nat.card Vertex = 280 := by
  rw [← Nat.card_congr vertexEquiv, Nat.card_fin]

theorem normalizer_index : M.index = 280 := by
  apply Nat.le_antisymm
  · simpa only [Nat.card_fin] using cosetCover.index_le_card letter_generates
  · have hsep (i j : Fin 280) (h : rep i * (rep j)⁻¹ ∈ M) : i = j := by
      apply vertex_injective
      have hh : (rep i * (rep j)⁻¹) • base = base := by
        apply MulAction.mem_stabilizer_iff.mp
        rwa [base_stabilizer]
      have hh := congrArg (fun A : Vertex => (rep i)⁻¹ • A) hh
      simpa only [mul_smul, inv_smul_smul, vertex] using hh.symm
    simpa only [Nat.card_fin] using
      Subgroup.card_le_index_of_rightCoset_separation M rep hsep

set_option maxRecDepth 4000 in
theorem card_M : Nat.card M = 2160 := by
  have h := M.card_mul_index
  rw [normalizer_index, ExceptionalParabolics.FirstParabolic.card_carrier] at h
  omega

/-- A normalizer preserves the fixed points of the actual cyclic generator. -/
theorem normalizer_preserves_fixed {u g : Carrier} (hg : g ∈ normalizer (zpowers u : Set Carrier))
    {p : Fin 100} (hp : inclusion u p = p) : inclusion u (inclusion g p) = inclusion g p := by
  have hm : g⁻¹ * u * g ∈ zpowers u := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp ((normalizer _).inv_mem hg) u).mp (mem_zpowers u)
  have hf := fixed_of_mem_zpowers hp hm
  have h := congrArg (inclusion g) hf
  change inclusion g ((inclusion g).symm (inclusion u (inclusion g p))) = inclusion g p at h
  simpa only [Equiv.apply_symm_apply] using h

/-- Faithfulness follows from fixed-point sets separating all 100 letters. -/
theorem faithful (g : Carrier) (hg : ∀ A : Vertex, g • A = A) : g = 1 := by
  have hn (i : Fin 280) : g ∈ normalizer (zpowers (element i) : Set Carrier) := by
    rw [← vertex_val, ← stabilizer_eq_normalizer, MulAction.mem_stabilizer_iff]
    exact hg _
  have hf (i : Fin 280) (p : Fin 100) :
      value i (inclusion g p) = inclusion g p ↔ value i p = p := by
    rw [← row_spec, ← row_spec]
    constructor
    · intro h
      have h' := normalizer_preserves_fixed ((normalizer _).inv_mem (hn i)) h
      change inclusion (element i) ((inclusion g).symm (inclusion g p)) =
        (inclusion g).symm (inclusion g p) at h'
      simpa only [Equiv.symm_apply_apply] using h'
    · exact normalizer_preserves_fixed (hn i)
  apply inclusion_injective
  apply Equiv.ext
  intro p
  change inclusion g p = p
  have hc : pointCode (inclusion g p) = pointCode p := by
    unfold pointCode
    congr 1
    funext i
    simp only [hf]
  have h := congrArg identifyPoint hc
  simpa only [identifyPoint_spec] using h

end Sporadic.LeechRelated.J2.RecognitionGeometry.OrbitAction
