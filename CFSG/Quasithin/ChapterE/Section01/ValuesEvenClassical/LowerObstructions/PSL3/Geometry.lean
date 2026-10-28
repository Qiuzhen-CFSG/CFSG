module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Normalizers

/-!
# The two-plane family for the PSL₃ lower obstruction

For a normal subgroup L isomorphic to PSL₃(2^f), take every elementary
abelian subgroup of L of order 2^(2f). In an ambient Sylow subgroup
containing the standard matrix Sylow S, precisely the two marked root
planes belong to this family. They generate S, so the weak closure is S.
Its normalizer is proper: otherwise every element of PSL₃ would normalize
the upper unitriangular subgroup, whereas its normalizer is the upper Borel.

These constructions include ambient graph and field automorphisms. The
separate geometric normalizer implication at the end is an explicit proof
obligation for the local E-member calculation, not an asserted result.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.5 and the PSL₃ case of E.1.14(1), printed pp.210 and 214;
unitriangular geometry as in §5.3.5--7, printed p.660.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.PSL3Obstruction
open Matrix.PSL3Even.UnipotentGeometry
variable {G F : Type*} [Group G] [Field F]

noncomputable def modelEmbedding (L : Subgroup G) (e : L ≃* PSL(3,F)) : PSL(3,F) →* G :=
  L.subtype.comp e.symm.toMonoidHom

theorem modelEmbedding_injective (L : Subgroup G) (e : L ≃* PSL(3,F)) :
    Function.Injective (modelEmbedding L e) := L.subtype_injective.comp e.symm.injective

theorem modelEmbedding_range (L : Subgroup G) (e : L ≃* PSL(3,F)) :
    (modelEmbedding L e).range = L := by
  rw [modelEmbedding, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective]
  rw [← MonoidHom.range_eq_map, L.range_subtype]

noncomputable def coordinates (L : Subgroup G) (e : L ≃* PSL(3,F)) : U F →* G :=
  (modelEmbedding L e).comp (projective F)

noncomputable def sylowImage (L : Subgroup G) (e : L ≃* PSL(3,F)) : Subgroup G :=
  (Matrix.PSL3.LinearThree.unipotent F).map (modelEmbedding L e)

noncomputable def planeImage (L : Subgroup G) (e : L ≃* PSL(3,F)) (b : Bool) : Subgroup G :=
  (if b then V₁ F else V₂ F).map (coordinates L e)

def planeFamily (L : Subgroup G) (f : ℕ) : Set (Subgroup G) :=
  {A | A ≤ L ∧ IsElementaryAbelian 2 A ∧ Nat.card A = 2 ^ (2 * f)}

theorem coordinates_injective (L : Subgroup G) (e : L ≃* PSL(3,F)) :
    Function.Injective (coordinates L e) :=
  (modelEmbedding_injective L e).comp (projective_injective F)

theorem coordinates_range (L : Subgroup G) (e : L ≃* PSL(3,F)) :
    (coordinates L e).range = sylowImage L e := by
  rw [coordinates, MonoidHom.range_comp, Matrix.PSL3.LinearThree.projective_range]
  rfl

theorem sylowImage_le (L : Subgroup G) (e : L ≃* PSL(3,F)) : sylowImage L e ≤ L := by
  exact (Subgroup.map_le_range _ _).trans_eq (modelEmbedding_range L e)

theorem planeImage_le (L : Subgroup G) (e : L ≃* PSL(3,F)) (b : Bool) :
    planeImage L e b ≤ sylowImage L e := by
  exact (Subgroup.map_le_range _ _).trans_eq (coordinates_range L e)

theorem isElementaryFamily_planeFamily (L : Subgroup G) [L.Normal] (f : ℕ) :
    IsElementaryFamily (planeFamily L f) := by
  constructor
  · exact fun A hA => hA.2.1
  · intro g A hA
    let := hA.2.1
    refine ⟨?_, IsElementaryAbelian.map _, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩
      exact (inferInstance : L.Normal).conj_mem a (hA.1 ha) g
    · rw [← Nat.card_congr (A.equivMapOfInjective _ (MulAut.conj g).injective).toEquiv]
      exact hA.2.2

variable [Finite F]

theorem sylowImage_isPGroup (L : Subgroup G) (e : L ≃* PSL(3,F))
    {f : ℕ} (hF : Nat.card F = 2^f) : IsPGroup 2 (sylowImage L e) :=
  (Matrix.PSL3.LinearThree.unipotent_isTwoGroup F hF).map _

theorem inf_eq_sylowImage (L : Subgroup G) (e : L ≃* PSL(3,F))
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (T : Sylow 2 G) (hST : sylowImage L e ≤ (T : Subgroup G)) :
    L ⊓ (T : Subgroup G) = sylowImage L e := by
  have hle : Matrix.PSL3.LinearThree.unipotent F ≤
      (T : Subgroup G).comap (modelEmbedding L e) := map_le_iff_le_comap.mp hST
  have heq := (Matrix.PSL3.LinearThree.unipotentSylow F hf hF).is_maximal'
    (T.isPGroup'.comap_of_injective _ (modelEmbedding_injective L e)) hle
  have hm := congrArg (Subgroup.map (modelEmbedding L e)) heq
  simpa only [Subgroup.map_comap_eq, modelEmbedding_range, Matrix.PSL3.LinearThree.coe_unipotentSylow, sylowImage] using hm

variable [CharP F 2]

omit [Finite F] in
theorem planeImage_mem (L : Subgroup G) (e : L ≃* PSL(3,F))
    {f : ℕ} (hF : Nat.card F = 2^f) (b : Bool) :
    planeImage L e b ∈ planeFamily L f := by
  refine ⟨(planeImage_le L e b).trans (sylowImage_le L e), ?_, ?_⟩
  · cases b with
    | false => exact IsElementaryAbelian.map (A := V₂ F) (coordinates L e)
    | true => exact IsElementaryAbelian.map (A := V₁ F) (coordinates L e)
  · unfold planeImage
    rw [← Nat.card_congr ((if b then V₁ F else V₂ F).equivMapOfInjective _
      (coordinates_injective L e)).toEquiv]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, card_V₂, card_V₁, hF,
      ← pow_mul, Nat.mul_comm f 2]

omit [Finite F] [CharP F 2] in
theorem planes_sup (L : Subgroup G) (e : L ≃* PSL(3,F)) :
    planeImage L e true ⊔ planeImage L e false = sylowImage L e := by
  apply le_antisymm (sup_le (planeImage_le L e true) (planeImage_le L e false))
  rw [← coordinates_range L e]
  rintro _ ⟨u, rfl⟩
  have hu : u = (⟨u.x, 0, u.c - u.x * u.y⟩ : U F) * ⟨0, u.y, 0⟩ := by
    apply U.ext <;> simp
  rw [hu, map_mul]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left ⟨_, (mem_V₁ F _).mpr rfl, rfl⟩)
    (Subgroup.mem_sup_right ⟨_, (mem_V₂ F _).mpr rfl, rfl⟩)

theorem weakClosure_eq (L : Subgroup G) (e : L ≃* PSL(3,F))
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (T : Sylow 2 G) (hST : sylowImage L e ≤ (T : Subgroup G)) :
    weakClosure (T : Subgroup G) (planeFamily L f) = sylowImage L e := by
  apply le_antisymm
  · rw [← inf_eq_sylowImage L e hf hF T hST]
    exact sSup_le fun A hA => le_inf hA.1.1 hA.2
  · rw [← planes_sup L e]
    apply sup_le
    · exact le_sSup ⟨planeImage_mem L e hF true, (planeImage_le L e true).trans hST⟩
    · exact le_sSup ⟨planeImage_mem L e hF false, (planeImage_le L e false).trans hST⟩

/-- Exactly the two marked planes occur in the chosen ambient Sylow subgroup. -/
theorem family_le_sylow_iff [Finite G] (L : Subgroup G) (e : L ≃* PSL(3,F))
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2^f)
    (T : Sylow 2 G) (hST : sylowImage L e ≤ (T : Subgroup G)) (A : Subgroup G) :
    (A ∈ planeFamily L f ∧ A ≤ (T : Subgroup G)) ↔ ∃ b, A = planeImage L e b := by
  constructor
  · rintro ⟨hA, hAT⟩
    let := hA.2.1
    have hAS : A ≤ sylowImage L e := by
      rw [← inf_eq_sylowImage L e hf hF T hST]
      exact le_inf hA.1 hAT
    have hAr : A ≤ (coordinates L e).range := by rwa [coordinates_range]
    have hmap : (A.comap (coordinates L e)).map (coordinates L e) = A :=
      Subgroup.map_comap_eq_self hAr
    have hplanes := le_plane_of_exponent_two F (A.comap (coordinates L e)) (by
      intro a ha
      apply coordinates_injective L e
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian _ ha)
    rcases hplanes with h | h
    · refine ⟨true, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
      · exact hmap ▸ Subgroup.map_mono h
      · exact ((planeImage_mem L e hF true).2.2.trans hA.2.2.symm).le
    · refine ⟨false, Subgroup.eq_of_le_of_card_ge ?_ ?_⟩
      · exact hmap ▸ Subgroup.map_mono h
      · exact ((planeImage_mem L e hF false).2.2.trans hA.2.2.symm).le
  · rintro ⟨b, rfl⟩
    exact ⟨planeImage_mem L e hF b, (planeImage_le L e b).trans hST⟩

omit [CharP F 2] in
private theorem borel_ne_top : Matrix.PSL3.LinearThree.borel F ≠ ⊤ := by
  intro h
  have hh := congrArg (Subgroup.comap (Matrix.PSL3.projection F)) h
  rw [Matrix.PSL3.LinearThree.borel_comap, Subgroup.comap_top] at hh
  let x := Matrix.SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (1 : F)
  have hx : x ∈ Matrix.PSL3.LinearThree.borelSL F := hh ▸ mem_top x
  have he := (Matrix.PSL3.LinearThree.mem_borelSL_iff F x).mp hx
  have : (1 : F) = 0 := by simpa [x, Matrix.SpecialLinearGroup.transvection_coe] using he.1
  exact one_ne_zero this

theorem normalizer_sylowImage_ne_top (L : Subgroup G) (e : L ≃* PSL(3,F)) :
    normalizer (sylowImage L e : Set G) ≠ ⊤ := by
  intro h
  have hn := Subgroup.le_normalizer_comap (H := sylowImage L e) (modelEmbedding L e)
  rw [h, Subgroup.comap_top] at hn
  have he : (sylowImage L e).comap (modelEmbedding L e) =
      Matrix.PSL3.LinearThree.unipotent F :=
    Subgroup.comap_map_eq_self_of_injective (modelEmbedding_injective L e) _
  rw [he, Matrix.PSL3.LinearThree.normalizer_unipotent_of_charTwo] at hn
  exact borel_ne_top (top_unique hn)


/-- The geometric input used to trap a member whose quotient image is small.
It is a statement about normalizers of actual subgroups of the matrix Sylow,
not an E-generation hypothesis. -/
def LargeIntersectionNormalizer (L : Subgroup G) (e : L ≃* PSL(3,F)) (f : ℕ) : Prop :=
  ∀ Q : Subgroup G, Q ≤ sylowImage L e → ∀ b : Bool,
    2^f < Nat.card (Q ⊓ planeImage L e b : Subgroup G) →
      normalizer (Q : Set G) ≤ normalizer (planeImage L e b : Set G) ∨
      normalizer (Q : Set G) ≤ normalizer (sylowImage L e : Set G)

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.PSL3Obstruction
