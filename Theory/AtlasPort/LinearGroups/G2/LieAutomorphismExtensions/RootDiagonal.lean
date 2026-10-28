module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
The generation argument adapts Atlas/LinearGroups/G2/LongRootNormalGeneration.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917;
see LICENSES/ATLAS-CITATION.cff. The root-character automorphism arguments are
new in CFSG.
-/

public import Theory.AtlasPort.LinearGroups.G2.LongRootNormalGeneration
public import Theory.AtlasPort.LinearGroups.G2.TorusNormalization

/-!
# Root-diagonal automorphisms of the actual G₂ model

The six positive roots and two negative simple roots generate the full
split-octonion automorphism group. Rank-one words recover both Weyl generators
and the split torus, so agreement on these eight root groups determines an
automorphism. This uses the existing coordinate generation proof, with no
order or simplicity hypothesis.

The short and long simple roots are F and E. Their prescribed character
values u and v give the positive-root characters
(u³v², u³v, u²v, uv, v, u), and inverse characters on the negative simple
roots. The octonion torus with coordinates (u²v, uv) has exactly these actions.
Thus every root-diagonal automorphism is inner. Conversely every torus element
arises this way, proving that this is the actual root-character diagonal group,
not a label assigned to the inner subgroup.

Source: GLS III, Theorem 2.5.1(b), Lemma 2.5.8, and Remark 2.5.11(c), which
describe diagonal automorphisms by root characters and inner-diagonal
automorphisms as products of inner and diagonal automorphisms. The explicit
root and rank-one word identities are from the licensed ATLAS port.
-/

@[expose] public section

open Subgroup
namespace Atlas.G2.RootDiagonal
variable {E : Type*} [Field E]

/-- Six positive roots, followed by the two negative simple roots. -/
def root (i : Fin 8) (t : E) : Model E :=
  ![rootA t, rootB t, rootC t, rootD t, rootE t, rootF t,
    weylR * rootE t * weylR⁻¹, weylS * rootF t * weylS⁻¹] i

/-- The root characters in the simple short/long root coordinates. -/
def character (u v : Eˣ) : Fin 8 → Eˣ :=
  ![u ^ 3 * v ^ 2, u ^ 3 * v, u ^ 2 * v, u * v, v, u, v⁻¹, u⁻¹]

/-- The root-character definition of a diagonal automorphism. -/
def IsDiagonal (a : MulAut (Model E)) : Prop :=
  ∃ u v : Eˣ, ∀ (i : Fin 8) (t : E),
    a (root i t) = root i ((character u v i : E) * t)

private theorem eq_top_of_root_mem (H : Subgroup (Model E))
    (hroot : ∀ (i : Fin 8) (t : E), root i t ∈ H) : H = ⊤ := by
  have hE (a : E) : rootE a ∈ H := hroot 4 a
  have hF (a : E) : rootF a ∈ H := hroot 5 a
  have hlong (a : Eˣ) : torus (-1) a * weylR ∈ H := by
    rw [← long_rank_one_word]
    exact H.mul_mem (H.mul_mem (hE _) (hroot 6 _)) (hE _)
  have hshort (a : Eˣ) : torus a (-a⁻¹) * weylS ∈ H := by
    rw [← short_rank_one_word]
    exact H.mul_mem (H.mul_mem (hF _) (hroot 7 _)) (hF _)
  have htm (a : Eˣ) : torus 1 a ∈ H := by
    have h := H.mul_mem (hlong a) (H.inv_mem (hlong 1))
    rw [mul_inv_rev, ← mul_assoc, mul_assoc (torus (-1) a), mul_inv_cancel,
      mul_one, torus_inverse, torus_product] at h
    simpa using h
  have htd (a : Eˣ) : torus a a⁻¹ ∈ H := by
    have h := H.mul_mem (hshort a) (H.inv_mem (hshort 1))
    rw [mul_inv_rev, ← mul_assoc, mul_assoc (torus a (-a⁻¹)), mul_inv_cancel,
      mul_one, torus_inverse, torus_product] at h
    simpa using h
  have ht (a b : Eˣ) : torus a b ∈ H := by
    have h := H.mul_mem (htd a) (htm (a * b))
    rw [torus_product] at h
    simpa using h
  have hr : (weylR : Model E) ∈ H := by
    have h := H.mul_mem (H.inv_mem (ht (-1) 1)) (hlong 1)
    simpa only [inv_mul_cancel_left] using h
  have hs : (weylS : Model E) ∈ H := by
    have h := H.mul_mem (H.inv_mem (ht 1 (-1))) (hshort 1)
    simpa only [inv_one, inv_mul_cancel_left] using h
  have hU : unipotent (K := E) ≤ H := by
    apply (closure_le H).mpr
    intro g hg
    simp only [Set.union_assoc, Set.mem_union, Set.mem_range] at hg
    rcases hg with (⟨t, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩ | ⟨t, rfl⟩)
    · exact hroot 0 t
    · exact hroot 1 t
    · exact hroot 2 t
    · exact hroot 3 t
    · exact hroot 4 t
    · exact hroot 5 t
  apply top_unique
  rw [← generated_eq_top]
  apply sup_le
  · apply (closure_le H).mpr
    intro g hg
    rcases hg with hg | hg
    · exact hU hg
    · rcases hg with rfl | rfl
      · exact hr
      · exact hs
  · rintro g ⟨⟨a, b⟩, rfl⟩
    exact ht a b

/-- The displayed root groups determine every group homomorphism on the model. -/
theorem hom_ext {G : Type*} [Group G] (a b : Model E →* G)
    (h : ∀ (i : Fin 8) (t : E), a (root i t) = b (root i t)) : a = b := by
  have htop := eq_top_of_root_mem (a.eqLocus b) h
  ext x
  exact htop.ge (mem_top x)

private theorem torus_negative_long (l m : Eˣ) (t : E) :
    torus l m * root 6 t * (torus l m)⁻¹ =
      root 6 (((l : E) / (m : E)^2) * t) := by
  rw [torus_inverse]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [root, torus, torusEquiv, torusLinear, torusWeights,
      weylR, weylREquiv, weylRLinear, weylRApply,
      rootE, Explicit.rootEEquiv, Explicit.rootELinear, Explicit.rootEApply] <;> field_simp

private theorem torus_negative_short (l m : Eˣ) (t : E) :
    torus l m * root 7 t * (torus l m)⁻¹ =
      root 7 (((m : E) / (l : E)) * t) := by
  rw [torus_inverse]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;>
    simp [root, torus, torusEquiv, torusLinear, torusWeights,
      weylS, weylSEquiv, weylSLinear, weylSApply,
      rootF, Explicit.rootFEquiv, Explicit.rootFLinear, Explicit.rootFApply] <;> field_simp

/-- Every root-lattice character is realized by an actual octonion torus element. -/
theorem torus_character (u v : Eˣ) (i : Fin 8) (t : E) :
    MulAut.conj (torus (u ^ 2 * v) (u * v)) (root i t) =
      root i ((character u v i : E) * t) := by
  change torus _ _ * root i t * (torus _ _)⁻¹ = _
  fin_cases i
  · change torus (u ^ 2 * v) (u * v) * rootA t *
      (torus (u ^ 2 * v) (u * v))⁻¹ = rootA ((↑(u ^ 3 * v ^ 2) : E) * t)
    rw [torus_rootA]
    congr 1
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    field_simp
  · change torus (u ^ 2 * v) (u * v) * rootB t *
      (torus (u ^ 2 * v) (u * v))⁻¹ = rootB ((↑(u ^ 3 * v) : E) * t)
    rw [torus_rootB]
    congr 1
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    field_simp
  · change torus (u ^ 2 * v) (u * v) * rootC t *
      (torus (u ^ 2 * v) (u * v))⁻¹ = rootC ((↑(u ^ 2 * v) : E) * t)
    rw [torus_rootC]
  · change torus (u ^ 2 * v) (u * v) * rootD t *
      (torus (u ^ 2 * v) (u * v))⁻¹ = rootD ((↑(u * v) : E) * t)
    rw [torus_rootD]
  · change torus (u ^ 2 * v) (u * v) * rootE t *
      (torus (u ^ 2 * v) (u * v))⁻¹ = rootE ((↑(v) : E) * t)
    rw [torus_rootE]
    congr 1
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    field_simp
  · change torus (u ^ 2 * v) (u * v) * rootF t *
      (torus (u ^ 2 * v) (u * v))⁻¹ = rootF ((↑(u) : E) * t)
    rw [torus_rootF]
    congr 1
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    field_simp
  · change torus (u ^ 2 * v) (u * v) * root 6 t *
      (torus (u ^ 2 * v) (u * v))⁻¹ = root 6 ((↑(v⁻¹) : E) * t)
    rw [torus_negative_long]
    congr 1
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
  · change torus (u ^ 2 * v) (u * v) * root 7 t *
      (torus (u ^ 2 * v) (u * v))⁻¹ = root 7 ((↑(u⁻¹) : E) * t)
    rw [torus_negative_short]
    congr 1
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp

/-- A diagonal automorphism is conjugation by the explicit matching torus element. -/
theorem eq_conj_of_diagonal (a : MulAut (Model E)) (ha : IsDiagonal a) :
    ∃ u v : Eˣ, a = MulAut.conj (torus (u ^ 2 * v) (u * v)) := by
  obtain ⟨u, v, huv⟩ := ha
  refine ⟨u, v, ?_⟩
  apply MulEquiv.toMonoidHom_injective
  apply hom_ext
  intro i t
  exact (huv i t).trans (torus_character u v i t).symm

/-- The character definition gives exactly the conjugation action of the split torus. -/
theorem diagonal_iff_torus (a : MulAut (Model E)) :
    IsDiagonal a ↔ ∃ t ∈ splitTorus (K := E), a = MulAut.conj t := by
  constructor
  · intro ha
    obtain ⟨u, v, rfl⟩ := eq_conj_of_diagonal a ha
    exact ⟨_, ⟨(u ^ 2 * v, u * v), rfl⟩, rfl⟩
  · rintro ⟨_, ⟨⟨l, m⟩, rfl⟩, rfl⟩
    change IsDiagonal (MulAut.conj (torus l m))
    have hl : (l * m⁻¹) ^ 2 * (m ^ 2 * l⁻¹) = l := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
      field_simp
    have hm : (l * m⁻¹) * (m ^ 2 * l⁻¹) = m := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
      field_simp
    have hd : IsDiagonal (MulAut.conj
        (torus ((l * m⁻¹) ^ 2 * (m ^ 2 * l⁻¹)) ((l * m⁻¹) * (m ^ 2 * l⁻¹)))) :=
      ⟨l * m⁻¹, m ^ 2 * l⁻¹, torus_character (l * m⁻¹) (m ^ 2 * l⁻¹)⟩
    rw [hl, hm] at hd
    exact hd

/-- Inner-diagonal automorphisms, generated by inner and root-diagonal actions. -/
def innerDiagonal : Subgroup (MulAut (Model E)) :=
  (MulAut.conj : Model E →* MulAut (Model E)).range ⊔ closure {a | IsDiagonal a}

/-- G₂ has no outer diagonal automorphisms. -/
theorem innerDiagonal_eq_inner : innerDiagonal (E := E) =
    (MulAut.conj : Model E →* MulAut (Model E)).range := by
  apply le_antisymm
  · apply sup_le le_rfl
    apply (closure_le _).mpr
    intro a ha
    obtain ⟨u, v, rfl⟩ := eq_conj_of_diagonal a ha
    exact ⟨_, rfl⟩
  · exact le_sup_left
end Atlas.G2.RootDiagonal
