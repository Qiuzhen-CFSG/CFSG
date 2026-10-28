module

public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global

/-!
# Sylow and conjugation foundations for the weak-closure minimum

Simultaneous conjugation preserves the indexed weak-closure escape condition.
Inside the normalizer of `V`, Sylow conjugacy moves any two-subgroup into the
specified Sylow subgroup while fixing `V`. Consequently a noncentralizing
conjugate-corank generator which normalizes `V` forces a weak-closure escape at
its actual corank. No finiteness assumption on the extended minimum is needed.

These are the group-theoretic foundations for E.3.25–28 and the reverse-normalizer
bound in E.3.31; the source-numbered conclusions are assembled separately.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.3.22–31,
printed pp. 236–238.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterE
open Subgroup
variable {G : Type*} [Group G]

/-- Composition of the ambient conjugation maps, in their left-action convention. -/
theorem offender_map_conj_map (V : Subgroup G) (g h : G) :
    (V.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      V.map (MulAut.conj (h * g)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- Inverse conjugation restores the original subgroup. -/
theorem offender_map_conj_inverse (V : Subgroup G) (g : G) :
    (V.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = V := by
  rw [offender_map_conj_map, inv_mul_cancel]
  have h : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [h, Subgroup.map_id]

/-- An actual ambient group equivalence carries the full centralizer to the centralizer of the image. -/
theorem offender_centralizer_map (V : Subgroup G) (e : G ≃* G) :
    (centralizer (V : Set G)).map e.toMonoidHom =
      centralizer (V.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

/-- Replacing the base subgroup by a conjugate leaves its conjugate-corank family unchanged. -/
theorem conjugateCorankFamily_conj (V : Subgroup G) (g : G) (i : ℕ) :
    conjugateCorankFamily (V.map (MulAut.conj g).toMonoidHom) i =
      conjugateCorankFamily V i := by
  ext A
  constructor
  · rintro ⟨h, hA, hi⟩
    rw [offender_map_conj_map] at hA hi
    exact ⟨h * g, hA, hi⟩
  · rintro ⟨h, hA, hi⟩
    refine ⟨h * g⁻¹, ?_, ?_⟩
    · simpa only [offender_map_conj_map, inv_mul_cancel_right] using hA
    · simpa only [offender_map_conj_map, inv_mul_cancel_right] using hi

private theorem indexedWeakClosure_map_conj_le (V T : Subgroup G) (g : G) (i : ℕ) :
    (indexedWeakClosure V T i).map (MulAut.conj g).toMonoidHom ≤
      indexedWeakClosure V (T.map (MulAut.conj g).toMonoidHom) i :=
  SubgroupFamily.map_span_le (conjugateCorankFamily_invariant V i) g
    (Subgroup.map_mono (indexedWeakClosure_le V T i))

/-- Simultaneous conjugation transports the actual indexed weak closure. -/
theorem indexedWeakClosure_map_conj (V T : Subgroup G) (g : G) (i : ℕ) :
    (indexedWeakClosure V T i).map (MulAut.conj g).toMonoidHom =
      indexedWeakClosure (V.map (MulAut.conj g).toMonoidHom)
        (T.map (MulAut.conj g).toMonoidHom) i := by
  change _ = SubgroupFamily.span
    (conjugateCorankFamily (V.map (MulAut.conj g).toMonoidHom) i) _
  rw [conjugateCorankFamily_conj]
  apply le_antisymm (indexedWeakClosure_map_conj_le V T g i)
  have h := indexedWeakClosure_map_conj_le V (T.map (MulAut.conj g).toMonoidHom) g⁻¹ i
  rw [offender_map_conj_inverse] at h
  have hh := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) h
  have hinv := offender_map_conj_inverse
    (indexedWeakClosure V (T.map (MulAut.conj g).toMonoidHom) i) g⁻¹
  simp only [inv_inv] at hinv
  rwa [hinv] at hh

theorem indexedWeakClosure_conj_le_centralizer_iff
    (V T : Subgroup G) (g : G) (i : ℕ) :
    indexedWeakClosure (V.map (MulAut.conj g).toMonoidHom)
        (T.map (MulAut.conj g).toMonoidHom) i ≤
      T.map (MulAut.conj g).toMonoidHom ⊓
        centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) ↔
      indexedWeakClosure V T i ≤ T ⊓ centralizer (V : Set G) := by
  rw [← indexedWeakClosure_map_conj, ← offender_centralizer_map,
    ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
  exact Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective

/-- Sylow conjugacy inside the normalizer, with an explicit normalizer-valued conjugator. -/
theorem offender_exists_normalizer_conjugate_le_sylow [Finite G]
    (V : Subgroup G) (T : Sylow 2 G)
    (hTN : (T : Subgroup G) ≤ normalizer (V : Set G))
    {A : Subgroup G} (hA : IsPGroup 2 A)
    (hAN : A ≤ normalizer (V : Set G)) :
    ∃ n ∈ normalizer (V : Set G), A.map (MulAut.conj n).toMonoidHom ≤ T := by
  let N := normalizer (V : Set G)
  have hAp : IsPGroup 2 (A.subgroupOf N) := hA.comap_subtype
  obtain ⟨P, hAP⟩ := hAp.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N P (T.subtype hTN)
  have hmap : (A.subgroupOf N).map (MulAut.conj n).toMonoidHom ≤
      (T.subtype hTN : Subgroup N) := by
    rw [← hn]
    exact Subgroup.map_mono hAP
  have hcomp : N.subtype.comp (MulAut.conj n).toMonoidHom =
      (MulAut.conj (n : G)).toMonoidHom.comp N.subtype := by
    ext x
    rfl
  have hamb := Subgroup.map_mono (f := N.subtype) hmap
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hAN, Sylow.coe_subtype,
    Subgroup.map_subgroupOf_eq_of_le hTN] at hamb
  exact ⟨n, n.property, hamb⟩

/-- Centralization of the weak closure controls every normalizing two-subgroup in its generating family. -/
theorem conjugateCorankFamily_le_centralizer_of_weakClosure [Finite G]
    (V : Subgroup G) (T : Sylow 2 G)
    (hTN : (T : Subgroup G) ≤ normalizer (V : Set G))
    {A : Subgroup G} {i : ℕ} (hA : A ∈ conjugateCorankFamily V i)
    (hAp : IsPGroup 2 A) (hAN : A ≤ normalizer (V : Set G))
    (hW : indexedWeakClosure V T i ≤ centralizer (V : Set G)) :
    A ≤ centralizer (V : Set G) := by
  obtain ⟨n, hn, hAT⟩ := offender_exists_normalizer_conjugate_le_sylow V T hTN hAp hAN
  have hAC : A.map (MulAut.conj n).toMonoidHom ≤ centralizer (V : Set G) :=
    (gamma_le_weakClosure ⟨conjugateCorankFamily_invariant V i A hA n, hAT⟩).trans hW
  have hV : V.map (MulAut.conj n).toMonoidHom = V :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hn
  have hC : (centralizer (V : Set G)).map (MulAut.conj n).toMonoidHom =
      centralizer (V : Set G) := by
    rw [offender_centralizer_map, hV]
  rw [← hC] at hAC
  exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj n).injective).mp hAC

/-- A noncentralizing normalizing generator forces escape, even if it does not initially lie in the chosen Sylow subgroup. -/
theorem indexedWeakClosure_escape_of_noncentralizing_generator [Finite G]
    (V : Subgroup G) (T : Sylow 2 G)
    (hTN : (T : Subgroup G) ≤ normalizer (V : Set G))
    {A : Subgroup G} {i : ℕ} (hA : A ∈ conjugateCorankFamily V i)
    (hAp : IsPGroup 2 A) (hAN : A ≤ normalizer (V : Set G))
    (hAC : ¬ A ≤ centralizer (V : Set G)) :
    ¬ indexedWeakClosure V T i ≤ (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  intro hW
  exact hAC (conjugateCorankFamily_le_centralizer_of_weakClosure V T hTN hA hAp hAN
    (hW.trans inf_le_right))

/-- The escape index is the actual quotient corank of the supplied subgroup of a conjugate. -/
theorem indexedWeakClosure_escape_at_corank [Finite G]
    (V : Subgroup G) [IsElementaryAbelian 2 V] (T : Sylow 2 G)
    (hTN : (T : Subgroup G) ≤ normalizer (V : Set G))
    (g : G) {A : Subgroup G}
    (hA : A ≤ V.map (MulAut.conj g).toMonoidHom ⊓ normalizer (V : Set G))
    (hAC : ¬ A ≤ centralizer (V : Set G)) :
    ¬ indexedWeakClosure V T (subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A) ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  let W := V.map (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hAW : A ≤ W := hA.trans inf_le_left
  have hAp : IsPGroup 2 A :=
    (IsElementaryAbelian.isPGroup 2 W).of_injective (Subgroup.inclusion hAW)
      (Subgroup.inclusion_injective hAW)
  apply indexedWeakClosure_escape_of_noncentralizing_generator V T hTN
    (A := A) ?_ hAp (hA.trans inf_le_right) hAC
  refine ⟨g, hAW, ?_⟩
  change A.relIndex W = 2 ^ subgroupCorank W A
  rw [subgroupCorank_eq_quotient_finrank]
  exact Subgroup.relIndex_eq_two_pow_quotient_finrank W A

/-- The nontriviality, containment and relative normality data of E.3.22 transport to the conjugate Sylow subgroup. -/
theorem offender_conjugate_sylow_data (V : Subgroup G) (T : Sylow 2 G)
    (hV : V ≠ ⊥) (hVT : V ≤ T)
    (hTN : (T : Subgroup G) ≤ normalizer (V : Set G)) (g : G) :
    V.map (MulAut.conj g).toMonoidHom ≠ ⊥ ∧
      V.map (MulAut.conj g).toMonoidHom ≤ (g • T : Sylow 2 G) ∧
      (g • T : Sylow 2 G) ≤
        normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
  refine ⟨?_, Subgroup.map_mono hVT, ?_⟩
  · intro he
    have hle : V.map (MulAut.conj g).toMonoidHom ≤
        (⊥ : Subgroup G).map (MulAut.conj g).toMonoidHom := by
      rw [he, Subgroup.map_bot]
    exact hV (le_bot_iff.mp
      ((Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective).mp hle))
  · change (T : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ _
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hTN

/-- Normalizing conjugates centralize whenever the zero-index weak closure does. -/
theorem conjugate_le_centralizer_of_normalizes_of_weakClosure_zero [Finite G]
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hTN : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hW : indexedWeakClosure V T 0 ≤ centralizer (V : Set G))
    (g : G) (hg : V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G)) :
    V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) := by
  let _ : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  exact conjugateCorankFamily_le_centralizer_of_weakClosure V T hTN
    ⟨g, le_rfl, by simp⟩ (IsElementaryAbelian.isPGroup 2 _) hg hW

/-- The four centralization and normalization conditions of E.3.25, expressed
using the actual zero-index weak closure. -/
theorem conjugate_normalization_equivalences_of_weakClosure_zero [Finite G]
    {V : Subgroup G} [IsElementaryAbelian 2 V] {T : Sylow 2 G}
    (hTN : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hW : indexedWeakClosure V T 0 ≤ centralizer (V : Set G)) (g : G) :
    (V.map (MulAut.conj g).toMonoidHom ≤ normalizer (V : Set G) ↔
      V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) ∧
    (V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) ↔
      V ≤ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G)) ∧
    (V ≤ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) ↔
      V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) := by
  refine ⟨⟨conjugate_le_centralizer_of_normalizes_of_weakClosure_zero hTN hW g,
    fun h => h.trans (centralizer_le_normalizer _)⟩, le_centralizer_iff, ?_⟩
  refine ⟨fun h => h.trans (centralizer_le_normalizer _), ?_⟩
  intro hn
  let W := V.map (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hSN : (g • T : Sylow 2 G) ≤ normalizer (W : Set G) := by
    change (T : Subgroup G).map (MulAut.conj g).toMonoidHom ≤ _
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hTN
  have hSW : indexedWeakClosure W (g • T : Sylow 2 G) 0 ≤
      centralizer (W : Set G) := by
    change indexedWeakClosure (V.map (MulAut.conj g).toMonoidHom)
      ((T : Subgroup G).map (MulAut.conj g).toMonoidHom) 0 ≤ _
    rw [← indexedWeakClosure_map_conj, ← offender_centralizer_map]
    exact Subgroup.map_mono hW
  have hinv : W.map (MulAut.conj g⁻¹).toMonoidHom = V :=
    offender_map_conj_inverse V g
  have h := conjugate_le_centralizer_of_normalizes_of_weakClosure_zero hSN hSW g⁻¹
    (hinv.symm ▸ hn)
  rwa [hinv] at h

end CFSG.Quasithin.ChapterE
